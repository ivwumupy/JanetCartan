module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.Atoms
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.CompactJets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.CanonicalSuperposition

/-!
# Physical bounds for the literal raw primary integral

`app:ch_waves:eq:raw-physical-bound` is deduced from primitive amplitude jets
and physical jets of the covector derivative of the phase. The quotient is
the literal `(S(x,ζ+τ η)-S(x,ζ))/τ`; its bounds come from the segment formula.
Dominated differentiation is proved by the imported measure-envelope calculus.

All analytic hypotheses concern the original phase and amplitude on an open
buffer containing the measurement set. Their actual WKB/common-history
production, and all slice/Sobolev estimates, remain the parent's obligations.
The Fourier support below is the input support before physical multiplication.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary

/-- Fixed constant in `app:ch_waves:eq:raw-physical-bound`. This expression
contains no shift size, frequency scale, band count, sample count, or weights. -/
def rawPhysicalConstant (c : ℝ) (a s : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), atomJetConstant a (fun r ↦ c * s r) j

/-- Nonnegativity of the raw physical constant
(`app:ch_waves:eq:raw-physical-bound`). -/
theorem rawPhysicalConstant_nonneg {c : ℝ} {a s : ℕ → ℝ} {m : ℕ}
    (hc : 0 ≤ c) (ha : ∀ j ≤ m, 0 ≤ a j)
    (hs : ∀ j, 1 ≤ j → j ≤ m → 0 ≤ s j) :
    0 ≤ rawPhysicalConstant c a s m := by
  apply Finset.sum_nonneg
  intro j hj
  have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  exact atomJetConstant_nonneg (fun i hi ↦ ha i (hi.trans hj'))
    (fun i hi hi' ↦ mul_nonneg hc (hs i hi (hi'.trans hj')))

section Integral

variable {X P F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [MeasurableSpace P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Compact-support synthesis is the same literal raw integral, even for an
almost-everywhere supported integrable density
(`app:ch_waves:eq:individual-representation`). -/
theorem rawPrimaryDemodulatedIntegral_eq_compactSynthesis
    (S : X → P → ℝ) (A : X → P → F) (ζ : P) (τ : ℝ)
    {μ : Measure P} {f : P → ℂ} {T : Set P}
    (hfT : ∀ᵐ η ∂μ, η ∉ T → f η = 0) (x : X) :
    rawPrimaryDemodulatedIntegral S A ζ τ μ f x =
      MeasureEnvelopes.synthesis (μ.restrict T) f
        (fun η ↦ rawPrimaryDemodulatedAtom S A ζ τ (x, η)) := by
  unfold rawPrimaryDemodulatedIntegral MeasureEnvelopes.synthesis
  calc
    _ = ∫ η, f η • rawPrimaryDemodulatedAtom S A ζ τ (x, η) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with η
      exact smul_comm _ _ _
    _ = _ := (setIntegral_eq_integral_of_ae_compl_eq_zero
      (hfT.mono fun η hη hηT ↦ by rw [hη hηT, zero_smul])).symm

end Integral

section Physical

variable {X P F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ P] in
/-- The literal raw integral is smooth for an arbitrary compactly supported
`L¹` density. This applies to the original annular `L²` data via their checked
Fourier `L¹` estimate, without any smooth-density assumption
(`app:ch_waves:thm:individual`). -/
theorem contDiffOn_rawPrimaryDemodulatedIntegral
    {U : Set X} {V T : Set P} (hU : IsOpen U) (hV : IsOpen V) (hT : IsCompact T)
    {S : X → P → ℝ} {A : X → P → F}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {ζ : P} {τ : ℝ} (hζ : ζ ∈ V) (hshift : ∀ η ∈ T, ζ + τ • η ∈ V)
    {μ : Measure P} [IsFiniteMeasure (μ.restrict T)]
    {f : P → ℂ} (hf : Integrable f μ) (hfT : ∀ᵐ η ∂μ, η ∉ T → f η = 0) :
    ContDiffOn ℝ ∞ (rawPrimaryDemodulatedIntegral S A ζ τ μ f) U := by
  let Ω : Set P := {η | ζ + τ • η ∈ V}
  have hΩ : IsOpen Ω := hV.preimage (by fun_prop)
  have hB : ContDiffOn ℝ ∞ (rawPrimaryDemodulatedAtom S A ζ τ) (U ×ˢ Ω) :=
    contDiffOn_rawPrimaryDemodulatedAtom hS hA hζ (fun _ h ↦ h)
  have h := contDiffOn_weightedCompactIntegral hU hΩ hT hshift hf.integrableOn hB
  exact h.congr (fun x _ ↦ (rawPrimaryDemodulatedIntegral_eq_compactSynthesis
    S A ζ τ hfT x))

omit [CompleteSpace F] in
/-- Finite-order physical bound for the literal raw integral with arbitrary
integrable complex Fourier density supported in the ball of radius `c K`.
Every exponential, quotient, measurability and differentiation-under-integral
estimate is derived from the displayed primitive data
(`app:ch_waves:eq:raw-physical-bound`). -/
theorem cNorm_rawPrimaryDemodulatedIntegral_le
    {U Q : Set X} {V : Set P} (hU : IsOpen U) (hV : IsOpen V)
    (hQU : Q ⊆ U)
    {S : X → P → ℝ} {A : X → P → F}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {ζ : P} {τ c K L : ℝ} (hτ : τ ≠ 0) (hζ : ζ ∈ V)
    (hc : 0 ≤ c) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hsegment : ∀ η ∈ Metric.closedBall 0 (c * K), ∀ t ∈ Icc (0 : ℝ) 1,
      ζ + (t * τ) • η ∈ V)
    {μ : Measure P} [IsFiniteMeasure (μ.restrict (Metric.closedBall 0 (c * K)))]
    {f : P → ℂ} (hf : Integrable f μ)
    (hfT : ∀ᵐ η ∂μ, η ∉ Metric.closedBall 0 (c * K) → f η = 0)
    {m : ℕ} {a s : ℕ → ℝ}
    (ha : ∀ j ≤ m, 0 ≤ a j) (hs : ∀ j, 1 ≤ j → j ≤ m → 0 ≤ s j)
    (hAj : ∀ j ≤ m, ∀ x ∈ U, ∀ ξ ∈ V,
      ‖iteratedFDeriv ℝ j (fun y ↦ A y ξ) x‖ ≤ a j * L ^ j)
    (hSj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U, ∀ ξ ∈ V,
      ‖iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ (S y) ξ) x‖ ≤ s j * L ^ (j - 1)) :
    cNorm Q m (rawPrimaryDemodulatedIntegral S A ζ τ μ f) ≤
      rawPhysicalConstant c a s m * (K + L) ^ m * ∫ η, ‖f η‖ ∂μ := by
  have hshift (η : P) (hη : η ∈ Metric.closedBall 0 (c * K)) : ζ + τ • η ∈ V := by
    simpa using hsegment η hη 1 (by simp)
  let T : Set P := Metric.closedBall 0 (c * K)
  let Ω : Set P := {η | ζ + τ • η ∈ V}
  let B := rawPrimaryDemodulatedAtom S A ζ τ
  let C (j : ℕ) := atomJetConstant a (fun r ↦ c * s r) j * (K + L) ^ j
  have hΩ : IsOpen Ω := hV.preimage (by fun_prop)
  have hT : IsCompact T := isCompact_closedBall _ _
  have hTΩ : T ⊆ Ω := hshift
  have hB : ContDiffOn ℝ ∞ B (U ×ˢ Ω) :=
    contDiffOn_rawPrimaryDemodulatedAtom hS hA hζ (fun _ h ↦ h)
  have hCj (j : ℕ) (hj : j ≤ m) : 0 ≤ atomJetConstant a (fun r ↦ c * s r) j :=
    atomJetConstant_nonneg (fun i hi ↦ ha i (hi.trans hj))
      (fun i hi hi' ↦ mul_nonneg hc (hs i hi (hi'.trans hj)))
  have hC (j : ℕ) (hj : j ≤ m) : 0 ≤ C j :=
    mul_nonneg (hCj j hj) (pow_nonneg (by linarith) _)
  have hBAE : ∀ᵐ η ∂μ.restrict T, ∀ x ∈ U, ContDiffAt ℝ m (fun y ↦ B (y, η)) x := by
    filter_upwards [ae_restrict_mem hT.measurableSet] with η hη x hx
    have hBx : ContDiffAt ℝ ∞ (fun y ↦ B (y, η)) x :=
      (hB.contDiffAt ((hU.prod hΩ).mem_nhds
        (show (x, η) ∈ U ×ˢ Ω from ⟨hx, hTΩ hη⟩))).comp x
        (contDiffAt_id.prodMk contDiffAt_const)
    exact hBx.of_le (by simp)
  have hm : ∀ j ≤ m, ∀ x ∈ U,
      AEStronglyMeasurable (fun η ↦ iteratedFDeriv ℝ j (fun y ↦ B (y, η)) x) (μ.restrict T) := by
    intro j _ x hx
    exact (integrableOn_compactParameter hT hTΩ
      (contDiffOn_atomPhysicalJet hU hΩ hB j).continuousOn hx).aestronglyMeasurable
  have hb : ∀ j ≤ m, ∀ᵐ η ∂μ.restrict T, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j (fun y ↦ B (y, η)) x‖ ≤ C j := by
    intro j hj
    filter_upwards [ae_restrict_mem hT.measurableSet] with η hη x hx
    exact norm_iteratedFDeriv_rawPrimaryDemodulatedAtom_le hU hV hS hA
      hτ hζ (hsegment η hη) hx hc (by linarith) (by linarith)
      (by simpa [T] using hη) (fun i hi ↦ ha i (hi.trans hj))
      (fun i hi hi' ↦ hs i hi (hi'.trans hj))
      (fun i hi ↦ hAj i (hi.trans hj) x hx)
      (fun i hi hi' ↦ hSj i hi (hi'.trans hj) x hx)
  have heq : rawPrimaryDemodulatedIntegral S A ζ τ μ f =
      (fun x ↦ MeasureEnvelopes.synthesis (μ.restrict T) f (fun η ↦ B (x, η))) :=
    funext (rawPrimaryDemodulatedIntegral_eq_compactSynthesis S A ζ τ hfT)
  rw [heq]
  apply (MeasureEnvelopes.cNorm_synthesis_le hU hf.integrableOn hBAE hm hb hC hQU).trans
  have hmass : MeasureEnvelopes.densityMass (μ.restrict T) f = ∫ η, ‖f η‖ ∂μ :=
    setIntegral_eq_integral_of_ae_compl_eq_zero
      (hfT.mono fun η hη hηT ↦ by rw [hη hηT, norm_zero])
  rw [hmass]
  have hsum : ∑ j ∈ Finset.range (m + 1), C j ≤ rawPhysicalConstant c a s m * (K + L) ^ m := by
    rw [rawPhysicalConstant, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hj') (hCj j hj')
  simpa only [mul_comm (∫ η, ‖f η‖ ∂μ)] using
    mul_le_mul_of_nonneg_left hsum (integral_nonneg (μ := μ) fun η ↦ norm_nonneg (f η))

end Physical

open RawInputPartition

/-- The physical estimate for the original wide annular Hilbert input, with
the proved `4 K` ceiling and the exact Fourier factor `K^(n/2)`. The amplitude
is a matrix with its Frobenius norm. The constant is independent of band count
and of the datum, including nonsmooth Fourier densities
(`app:ch_waves:eq:raw-physical-bound`). -/
theorem cNorm_rawPrimaryDemodulatedIntegral_weightedWideDensity_le
    {n N : ℕ} (hn : 1 ≤ n) {U Q : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V) (hQU : Q ⊆ U)
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {A : Euclidean n → Euclidean (n - 1) → Matrix (Fin N) (Fin n) ℂ}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {ζ : Euclidean (n - 1)} {τ K L : ℝ} (hτ : τ ≠ 0) (hζ : ζ ∈ V)
    (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hsegment : ∀ η ∈ Metric.closedBall 0 (4 * K), ∀ t ∈ Icc (0 : ℝ) 1,
      ζ + (t * τ) • η ∈ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hdb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n (cutoffCount K)) {m : ℕ} {a s : ℕ → ℝ}
    (ha : ∀ j ≤ m, 0 ≤ a j) (hs : ∀ j, 1 ≤ j → j ≤ m → 0 ≤ s j)
    (hAj : ∀ j ≤ m, ∀ x ∈ U, ∀ ξ ∈ V,
      ‖iteratedFDeriv ℝ j (fun y ↦ A y ξ) x‖ ≤ a j * L ^ j)
    (hSj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U, ∀ ξ ∈ V,
      ‖iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ (S y) ξ) x‖ ≤ s j * L ^ (j - 1)) :
    cNorm Q m (rawPrimaryDemodulatedIntegral S A ζ τ volume (weightedWideDensity d v)) ≤
      (rawPhysicalConstant 4 a s m *
        (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2))) *
        (K + L) ^ m * K ^ ((n : ℝ) / 2) * ‖v‖ := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Euclidean (n - 1))
      (4 * K))) := isFiniteMeasure_restrict.mpr (isCompact_closedBall _ _).measure_lt_top.ne
  have hfT : ∀ᵐ η ∂volume, η ∉ Metric.closedBall 0 (4 * K) → weightedWideDensity d v η = 0 := by
    filter_upwards [] with η hη
    exact wideDensity_eq_zero_of_four_mul_le hK d v (le_of_lt (by simpa using hη))
  apply (cNorm_rawPrimaryDemodulatedIntegral_le hU hV hQU hS hA hτ hζ
    (by norm_num) hK hL hsegment (integrable_wideDensity hd hM hdb v) hfT ha hs hAj hSj).trans
  have hC : 0 ≤ rawPhysicalConstant 4 a s m * (K + L) ^ m :=
    mul_nonneg (rawPhysicalConstant_nonneg (by norm_num) ha hs) (pow_nonneg (by linarith) _)
  convert mul_le_mul_of_nonneg_left
    (integral_norm_weightedWideDensity_rounded_le hn hK hd hM hdb v) hC using 1
  ring

end JanetCartan.RawPrimary
