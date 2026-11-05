module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.PullbackGrades

/-!
# Primitive original-chart producers for the rescaled joint grades

The phase is the published segment quotient, smooth also at epsilon zero.
The amplitude is the original WKB amplitude evaluated at the literal shifted
covector and multiplied by the original masks. The quantitative premises are
jets on the original buffered chart, before either operation. The consumer is
the differentiated SingleChannel input for `app:ch_waves:eq:individual-raw-slice`.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open FourierIntegral.NormalOneHigh

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The SAME divided phase, with its canonical smooth value at epsilon zero
(`app:ch_waves:eq:phase-quotient`). -/
def rawSlicePhaseExtension (S : X → P → ℝ) (ζ : P) (q : ℝ × X × P) : ℝ :=
  phaseShiftQuotient S q.2.1 ζ q.2.2 q.1

/-- The literal raw band amplitude with epsilon free. The mask `m θ` is
`sqrt ‖θ‖ * β (2^j • θ)` in the consumer
(`app:ch_waves:eq:individual-raw-slice`). -/
def rawSliceAmplitudeExtension (A : X → P → F) (χ : X → ℝ)
    (m : P → ℂ) (ζ : P) (q : ℝ × X × P) : F :=
  ((χ q.2.1 : ℂ) * m q.2.2) • A q.2.1 (ζ + q.1 • q.2.2)

/-- Identification with the actual nonzero quotient uses the original
segment, without convexification or changing charts
(`app:ch_waves:eq:phase-quotient`). -/
theorem rawSlicePhaseExtension_eq_rawPrimaryPhaseDifference
    {U : Set X} {V : Set P} (hV : IsOpen V) {S : X → P → ℝ}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    {ζ : P} {q : ℝ × X × P} (hq : q.2.1 ∈ U) (hε : q.1 ≠ 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ζ + (t * q.1) • q.2.2 ∈ V) :
    rawSlicePhaseExtension S ζ q = rawPrimaryPhaseDifference S ζ q.1 q.2.1 q.2.2 := by
  rw [rawPrimaryPhaseDifference_eq_segmentIntegral hV hS hε hseg hq]
  simp only [rawSlicePhaseExtension, phaseShiftQuotient, inner_gradient_left]

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ P]

/-- Joint smoothness through epsilon zero follows from primitive smoothness
and buffered shifted-segment containment (`app:ch_waves:eq:phase-quotient`). -/
theorem contDiffOn_rawSlicePhaseExtension
    {U : Set X} {V : Set P} {Q : Set (ℝ × X × P)} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) {S : X → P → ℝ} {ζ : P}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (rawSlicePhaseExtension S ζ) Q :=
  FullPhaseCharts.contDiffOn_phaseShiftQuotient_comp hU hV hQ hW hIW hS
    contDiffOn_snd.fst contDiffOn_const contDiffOn_snd.snd contDiffOn_fst
    (fun _ hq t ht ↦ hshift t ht hq)

omit [CompleteSpace P] [FiniteDimensional ℝ X] [FiniteDimensional ℝ P] in
/-- The original shifted WKB amplitude and masks are jointly smooth, including
at epsilon zero (`app:ch_waves:eq:individual-raw-slice`). -/
theorem contDiffOn_rawSliceAmplitudeExtension
    {U : Set X} {V Ω : Set P} {Q : Set (ℝ × X × P)}
    {A : X → P → F} {χ : X → ℝ} {m : P → ℂ} {ζ : P}
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    (hχ : ContDiffOn ℝ ∞ χ U) (hm : ContDiffOn ℝ ∞ m Ω)
    (hshift : MapsTo (rawSliceShift ζ 1) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω) :
    ContDiffOn ℝ ∞ (rawSliceAmplitudeExtension A χ m ζ) Q := by
  have ha : ContDiffOn ℝ ∞ (fun q : ℝ × X × P ↦
      A q.2.1 (ζ + q.1 • q.2.2)) Q := by
    apply hA.comp (f := fun q : ℝ × X × P ↦ (q.2.1, ζ + q.1 • q.2.2))
      (by fun_prop)
    intro q hq
    simpa only [rawSliceShift, one_mul] using hshift hq
  exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn
    (hχ.comp contDiffOn_snd.fst (fun q hq ↦ (hshift hq).1))).mul
      (hm.comp contDiffOn_snd.snd hθ)).smul ha

/-- Original covector-differential jets produce every joint phase jet on the
rescaled chart. This includes the epsilon derivative. The fixed reserve `R`
is preserved, and only primitive covector jets through `k` are used. In terms
of `S` itself these are orders through `k+1`
(`app:ch_waves:eq:phase-quotient`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_iteratedFDeriv_rawSlicePhaseExtension_le
    {U : Set X} {V : Set P} {Q : Set (ℝ × X × P)} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) {S : X → P → ℝ} {ζ : P}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    {q : ℝ × X × P} (hq : q ∈ Q) {k R : ℕ} {L : ℝ} (hL : 1 ≤ L)
    {p c b : ℕ → ℝ} (hp : ∀ j, 0 ≤ p j) (hc : ∀ j, 0 ≤ c j)
    (hb : ∀ j, 0 ≤ b j)
    (hprimitive : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ k,
      ‖iteratedFDeriv ℝ j (fun z : X × P ↦ fderiv ℝ (S z.1) z.2)
        (rawSliceShift ζ t q)‖ ≤ p j * L ^ (j - 1 - R))
    (hmap : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, 1 ≤ j → j ≤ k →
      ‖iteratedFDeriv ℝ j (rawSliceShift ζ t) q‖ ≤ c j)
    (hθ : ∀ j ≤ k, ‖iteratedFDeriv ℝ j (fun z : ℝ × X × P ↦ z.2.2) q‖ ≤ b j) :
    ‖iteratedFDeriv ℝ k (rawSlicePhaseExtension S ζ) q‖ ≤
      sliceMaskJetConstant (compositionBudget p c) b k * L ^ (k - 1 - R) := by
  let D : X × P → P →L[ℝ] ℝ := fun z ↦ fderiv ℝ (S z.1) z.2
  have hD : ContDiffOn ℝ ∞ D (U ×ˢ V) := contDiffOn_rawPhaseCovectorDerivative hU hV hS
  have hcomp (t : ℝ) (ht : t ∈ W) : ContDiffOn ℝ ∞ (D ∘ rawSliceShift ζ t) Q :=
    hD.comp (by unfold rawSliceShift; fun_prop) (hshift t ht)
  have hint : ContDiffOn ℝ ∞
      (fun w : (ℝ × X × P) × ℝ ↦ D (rawSliceShift ζ w.2 w.1) w.1.2.2) (Q ×ˢ W) := by
    apply (hD.comp (f := fun w : (ℝ × X × P) × ℝ ↦ rawSliceShift ζ w.2 w.1)
      (by unfold rawSliceShift; fun_prop) (fun w hw ↦ hshift w.2 hw.2 hw.1)).clm_apply
    exact contDiffOn_fst.snd.snd
  have heq : rawSlicePhaseExtension S ζ = fun z : ℝ × X × P ↦
      ∫ t in (0 : ℝ)..1, D (rawSliceShift ζ t z) z.2.2 := by
    funext z
    simp only [rawSlicePhaseExtension, phaseShiftQuotient, inner_gradient_left, D, rawSliceShift]
  rw [heq]
  apply FullPhaseCharts.InverseEstimates.norm_iteratedFDeriv_unitIntervalParameterIntegral_le
    hQ hW hIW hint hq k
  intro t ht
  have hj (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (D ∘ rawSliceShift ζ t) q‖ ≤
        compositionBudget p c i * L ^ (i - 1 - R) := by
    simpa only [Nat.sub_sub] using norm_iteratedFDeriv_comp_le_sliceGrade
      (g := rawSliceShift ζ t) (f := D) (R := 1 + R)
      (by unfold rawSliceShift; fun_prop)
      (hD.contDiffAt ((hU.prod hV).mem_nhds (hshift t (hIW ht) hq)))
      (fun j _ ↦ hp j) hL
      (fun j hj ↦ by simpa only [Nat.sub_sub] using hprimitive t ht j (hj.trans hi))
      (fun j hj hj' ↦ hmap t ht j hj (hj'.trans hi))
  have hh := norm_iteratedFDerivWithin_clm_apply (hcomp t (hIW ht))
    (contDiffOn_snd.snd : ContDiffOn ℝ ∞ (fun z : ℝ × X × P ↦ z.2.2) Q)
    hQ.uniqueDiffOn hq (by simp : (k : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ hQ hq] at hh
  apply hh.trans
  rw [sliceMaskJetConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hci := compositionBudget_nonneg hp hc i
  have hbi := hb (k - i)
  calc
    _ ≤ (k.choose i : ℝ) * (compositionBudget p c i * L ^ (i - 1 - R)) * b (k - i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hj i hi') (Nat.cast_nonneg _))
        (hθ _ (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = ((k.choose i : ℝ) * compositionBudget p c i * b (k - i)) * L ^ (i - 1 - R) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (by positivity)

omit [CompleteSpace P] [FiniteDimensional ℝ X] [FiniteDimensional ℝ P] in
/-- Original WKB amplitude jets produce all joint chart amplitude jets, with
the fixed reserve unchanged. The only other inputs are fixed mask and
substitution jets, whose compact bounds are independent of the WKB data
(`app:ch_waves:eq:WKB-amplitude-difference`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_iteratedFDeriv_rawSliceAmplitudeExtension_le
    {U : Set X} {V Ω : Set P} {Q : Set (ℝ × X × P)}
    (hU : IsOpen U) (hV : IsOpen V) (hQ : IsOpen Q)
    {A : X → P → F} {χ : X → ℝ} {m : P → ℂ} {ζ : P}
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    (hχ : ContDiffOn ℝ ∞ χ U) (hm : ContDiffOn ℝ ∞ m Ω)
    (hshift : MapsTo (rawSliceShift ζ 1) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω) {q : ℝ × X × P} (hq : q ∈ Q)
    {k R : ℕ} {L : ℝ} (hL : 1 ≤ L)
    {a c b : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (hc : ∀ j, 0 ≤ c j)
    (hb : ∀ j, 0 ≤ b j)
    (hprimitive : ∀ j ≤ k,
      ‖iteratedFDeriv ℝ j (Function.uncurry A) (rawSliceShift ζ 1 q)‖ ≤ a j * L ^ (j - R))
    (hmap : ∀ j, 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j (rawSliceShift ζ 1) q‖ ≤ c j)
    (hmask : ∀ j ≤ k, ‖iteratedFDeriv ℝ j
      (fun z : ℝ × X × P ↦ (χ z.2.1 : ℂ) * m z.2.2) q‖ ≤ b j) :
    ‖iteratedFDeriv ℝ k (rawSliceAmplitudeExtension A χ m ζ) q‖ ≤
      sliceMaskJetConstant b (compositionBudget a c) k * L ^ (k - R) := by
  have hh : ContDiffOn ℝ ∞ ((Function.uncurry A) ∘ rawSliceShift ζ 1) Q :=
    hA.comp (by unfold rawSliceShift; fun_prop) hshift
  have hm' : ContDiffOn ℝ ∞ (fun z : ℝ × X × P ↦ (χ z.2.1 : ℂ) * m z.2.2) Q :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hχ.comp contDiffOn_snd.fst (fun z hz ↦ (hshift hz).1))).mul
      (hm.comp contDiffOn_snd.snd hθ)
  have h := norm_iteratedFDeriv_mask_smul_le_sliceGrade hQ hm' hh hq hL
    (fun j _ ↦ hb j) (fun j _ ↦ compositionBudget_nonneg ha hc j) hmask
    (fun j hj ↦ norm_iteratedFDeriv_comp_le_sliceGrade
      (by unfold rawSliceShift; fun_prop)
      (hA.contDiffAt ((hU.prod hV).mem_nhds (hshift hq)))
      (fun i _ ↦ ha i) hL (fun i hi ↦ hprimitive i (hi.trans hj))
      (fun i hi hi' ↦ hmap i hi (hi'.trans hj)))
  change ‖iteratedFDeriv ℝ k (fun z : ℝ × X × P ↦
    ((χ z.2.1 : ℂ) * m z.2.2) • A z.2.1 (ζ + z.1 • z.2.2)) q‖ ≤ _
  simpa only [Function.comp_def, Function.uncurry_apply_pair, rawSliceShift, one_mul] using h

end JanetCartan.RawPrimary.SliceBounds
