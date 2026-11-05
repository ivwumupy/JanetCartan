module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Fixed output cutoffs for literal retarded leakage

The regularized identity contribution need not have compact output support.
For `app:ch_regular:eq:chain-tail`, a fixed smooth physical cutoff can instead
be inserted before taking the Fourier limit. It is one on the actual output
support, so the limiting operator is unchanged. This provides the compact
output carriers required by the kernel-to-Sobolev bridge.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace JanetCartan.FiniteChain.Retarded.Leakage
open LocalizedKernel

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The literal localized lower or upper operator, retaining the respective
scalars `i` and `-i` (`app:ch_regular:lem:finite-chain`). The endpoint is the
lower endpoint for `false` and the upper endpoint for `true`. -/
def literalLocalizedOperator (upper : Bool) (endpoint : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (u : ℝ × E → ℂ) : ℝ × E → ℂ :=
  let v := if upper then
    fun x => -Complex.I * JanetCartan.Retarded.upper endpoint β α (rightOperator mi u) x
  else fun x => Complex.I * JanetCartan.Retarded.lower endpoint β α (rightOperator mi u) x
  fun x => v x - leftOperator mo v x

/-- A compact carrier for the actual limiting output, including the left
symbol's base projection (`app:ch_regular:eq:chain-tail`). -/
def literalOutputCarrier (upper : Bool) (α β : ℝ × E → ℝ)
    (mo : (ℝ × E) → (ℝ × E) → ℂ) : Set (ℝ × E) :=
  (if upper then tsupport β else tsupport α) ∪
    Prod.fst '' tsupport (Function.uncurry mo)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The carrier is fixed by the weights and proof mask; it is independent
of the datum and Fourier regularization (`app:ch_regular:eq:chain-tail`). -/
theorem isCompact_literalOutputCarrier (upper : Bool)
    {α β : ℝ × E → ℝ} {mo : (ℝ × E) → (ℝ × E) → ℂ}
    (hα : HasCompactSupport α) (hβ : HasCompactSupport β)
    (ho : HasCompactSupport (Function.uncurry mo)) :
    IsCompact (literalOutputCarrier upper α β mo) := by
  unfold literalOutputCarrier
  have hw : IsCompact (if upper then tsupport β else tsupport α) := by
    cases upper <;> assumption
  exact hw.union (ho.isCompact.image continuous_fst)

/-- Left quantization vanishes off its symbol's base projection, without
any support or regularity assumption on the datum (`app:ch_regular:eq:chain-tail`). -/
theorem leftOperator_eq_zero_off_base (mo : (ℝ × E) → (ℝ × E) → ℂ)
    (u : ℝ × E → ℂ) {x : ℝ × E}
    (hx : x ∉ Prod.fst '' tsupport (Function.uncurry mo)) :
    leftOperator mo u x = 0 := by
  have hz (ξ : ℝ × E) : mo x ξ = 0 :=
    image_eq_zero_of_notMem_tsupport (f := Function.uncurry mo)
      (fun h => hx ⟨(x, ξ), h, rfl⟩)
  simp [leftOperator, leftKernel, hz]

/-- Both literal orientations have the asserted output carrier. Compact
support is proved for the actual limit, not presumed for its regularizations
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem literalLocalizedOperator_eq_zero_off_carrier (upper : Bool) (endpoint : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (u : ℝ × E → ℂ) {x : ℝ × E}
    (hx : x ∉ literalOutputCarrier upper α β mo) :
    literalLocalizedOperator upper endpoint α β mi mo u x = 0 := by
  have hmo : x ∉ Prod.fst '' tsupport (Function.uncurry mo) :=
    fun h => hx (Or.inr h)
  cases upper
  · have hα : α x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
    simp [literalLocalizedOperator, leftOperator_eq_zero_off_base mo _ hmo,
      JanetCartan.Retarded.lower, hα]
  · have hβ : β x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
    simp [literalLocalizedOperator, leftOperator_eq_zero_off_base mo _ hmo,
      JanetCartan.Retarded.upper, hβ]

/-- Construct the fixed smooth output cutoff needed for compact kernel
estimates. Its insertion leaves the actual literal operator unchanged for
every input (`app:ch_regular:eq:chain-tail`). -/
theorem exists_literalOutputCutoff (upper : Bool)
    {α β : ℝ × E → ℝ} {mo : (ℝ × E) → (ℝ × E) → ℂ}
    (hα : HasCompactSupport α) (hβ : HasCompactSupport β)
    (ho : HasCompactSupport (Function.uncurry mo))
    {U : Set (ℝ × E)} (hU : IsOpen U)
    (hKU : literalOutputCarrier upper α β mo ⊆ U) :
    ∃ χ : ℝ × E → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      literalOutputCarrier upper α β mo ⊆ interior {x | χ x = 1} ∧
      ∀ endpoint mi u x, (χ x : ℂ) *
        literalLocalizedOperator upper endpoint α β mi mo u x =
          literalLocalizedOperator upper endpoint α β mi mo u x := by
  obtain ⟨χ, hs, hr, hc, hu, hp⟩ := CompatibleResponse.exists_compact_family_cutoff
    (isCompact_literalOutputCarrier upper hα hβ ho) hU hKU
  refine ⟨χ, hs, hr, hc, hu, hp, ?_⟩
  intro endpoint mi u x
  by_cases hx : x ∈ literalOutputCarrier upper α β mo
  · have hone : x ∈ {x | χ x = 1} := interior_subset (hp hx)
    change χ x = 1 at hone
    simp [hone]
  · simp [literalLocalizedOperator_eq_zero_off_carrier upper endpoint α β mi mo u hx]

/-- The actual regularized kernel with a fixed physical output cutoff.
Its purpose is the compact kernel-to-Sobolev estimate in
`app:ch_regular:eq:chain-tail`; no change to the limiting operator is made. -/
def baseCutFourierKernel (upper : Bool) (χ : ℝ × E → ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) : ℂ :=
  (χ xo : ℂ) * if upper then upperFourierKernel α β mi mo r xi xo
    else lowerFourierKernel α β mi mo r xi xo

/-- Inserting the fixed output cutoff commutes with the exact reconstruction
limit. Both endpoint buffers and both literal scalar signs are retained
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem tendsto_integral_baseCutFourierKernel
    (upper : Bool) (endpoint ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (u : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hu : ContDiff ℝ ∞ u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi))
    (hso : HasCompactSupport (Function.uncurry mo)) (hsu : HasCompactSupport u)
    (hbuffer : if upper then ∀ s y, endpoint - ε ≤ s → α (s, y) = 0
      else ∀ s y, s ≤ endpoint + ε → β (s, y) = 0)
    (χ : ℝ × E → ℝ)
    (hχone : ∀ x ∈ literalOutputCarrier upper α β mo, χ x = 1)
    (ψ : ℝ × E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (hψ0 : ψ 0 = 1) (xo : ℝ × E) :
    Tendsto (fun R : ℝ => ∫ xi,
      baseCutFourierKernel upper χ α β mi mo (fun ξ => (ψ (R⁻¹ • ξ) : ℂ)) xi xo * u xi)
      atTop (𝓝 (literalLocalizedOperator upper endpoint α β mi mo u xo)) := by
  have he : (χ xo : ℂ) * literalLocalizedOperator upper endpoint α β mi mo u xo =
      literalLocalizedOperator upper endpoint α β mi mo u xo := by
    by_cases hx : xo ∈ literalOutputCarrier upper α β mo
    · simp [hχone xo hx]
    · simp [literalLocalizedOperator_eq_zero_off_carrier upper endpoint α β mi mo u hx]
  have hl : Tendsto (fun R : ℝ => ∫ xi,
      (if upper then upperFourierKernel α β mi mo (fun ξ => (ψ (R⁻¹ • ξ) : ℂ)) xi xo
      else lowerFourierKernel α β mi mo (fun ξ => (ψ (R⁻¹ • ξ) : ℂ)) xi xo) * u xi)
      atTop (𝓝 (literalLocalizedOperator upper endpoint α β mi mo u xo)) := by
    cases upper
    · exact tendsto_integral_lowerFourierKernel endpoint ε hε α β mi mo u hα hβ hi ho hu
        hsα hsβ hsi hso hsu hbuffer ψ hψ hsψ hψ0 xo
    · exact tendsto_integral_upperFourierKernel endpoint ε hε α β mi mo u hα hβ hi ho hu
        hsα hsβ hsi hso hsu hbuffer ψ hψ hsψ hψ0 xo
  have hm := (tendsto_const_nhds (x := (χ xo : ℂ))).mul hl
  rw [he] at hm
  simpa only [baseCutFourierKernel, mul_assoc, integral_const_mul] using hm

end JanetCartan.FiniteChain.Retarded.Leakage
