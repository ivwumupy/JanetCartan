module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.Collared

/-!
# Symbol bounds for the actual collared conic matrices

The fixed angular/low-frequency mask has all normalized budgets. Multiplying
the same homogeneous extension preserves order zero/minus one and introduces
no derivative loss or second high coefficient factor. Consumer: the actual
`W₀,W₁,PW₁` in `EvolutionIntegral.SymbolBudgets`, for
`app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicAmplitude
open AmplitudeBounds FiniteMasks EvolutionIntegral SymbolBudgets
open FourierIntegral.PrimitiveProfiles
variable {d n : ℕ}
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "JPoint" => SymbolBudgets.TwoTimePoint d
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- Normalize the actual collar and the actual order `-o` amplitude before
taking joint derivatives. The radial weight cancels exactly
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem twoTimeOrderField_curry_collared (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (a : Euclidean d → ℝ) (f : T → Mat) {R : ℝ} (hR : R ≠ 0) :
    twoTimeOrderField o R (curryCharacteristicMatrix (collared ℓ o a f)) =
      fun p ↦ (conicMask a (R • p.2) : ℂ) •
        jointAmplitude (curryCharacteristicMatrix (extend ℓ o f)) p := by
  funext p
  change R ^ o • ((conicMask a (R • p.2) : ℂ) •
    extend ℓ o f (p.1.1, (p.1.2.1, (p.1.2.2, R • p.2)))) = _
  rw [smul_comm (R ^ o), extend_smul ℓ o f (p.1.1, (p.1.2.1, (p.1.2.2, p.2))) hR, smul_smul,
    ← mul_pow, mul_inv_cancel₀ hR, one_pow, one_smul]
  rfl

/-- The cost of the fixed collar, independent of the varying matrix and all
frequency radii (`app:ch_regular_base:lem:retarded-kernel`). -/
def collarBoundConstant (a : Euclidean d → ℝ) (K : Set JPoint) (m : ℕ) : ℝ :=
  1 + (m + 1 : ℝ) * 2 ^ m *
    normalizedSeminorm K m (fun p : JPoint ↦ (conicMask a p.2 : ℂ))

/-- The same constant works for both symbol orders and is strictly positive. -/
theorem collarBoundConstant_pos (a : Euclidean d → ℝ) (K : Set JPoint) (m : ℕ) :
    0 < collarBoundConstant a K m := by
  unfold collarBoundConstant
  have := normalizedSeminorm_nonneg K m (fun p : JPoint ↦ (conicMask a p.2 : ℂ))
  positivity

/-- The collar contributes only its fixed constant to every normalized shell.
Local smoothness of the original matrix suffices on the same normalized chart;
no estimate for the masked amplitude is assumed (`retarded-kernel`). -/
theorem cNorm_twoTimeOrderField_curry_collared_le
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) {a : Euclidean d → ℝ}
    (ha : ContDiff ℝ ∞ a) {K : Set JPoint} {U : Set T}
    (hK : IsCompact K) (hU : IsOpen U)
    (hKU : evolutionToCharacteristicPoint '' K ⊆ ConicPhase.domain ℓ U)
    {f : T → Mat} (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    cNorm K m (twoTimeOrderField o R (curryCharacteristicMatrix (collared ℓ o a f))) ≤
      collarBoundConstant a K m *
        twoTimeOrderSeminorm o K m (curryCharacteristicMatrix (extend ℓ o f)) := by
  have hzero : ∀ p ∈ K, p.2 ≠ 0 := by
    intro p hp hz
    have h := (hKU (mem_image_of_mem evolutionToCharacteristicPoint hp)).1
    change 0 < ℓ p.2 at h
    simp [hz] at h
  have hb := boundedNormalizedSeminorm_conicMask ha hK hzero m
  let D := evolutionToCharacteristicPoint ⁻¹' ConicPhase.domain ℓ U
  have hD : IsOpen D := (ConicPhase.isOpen_domain ℓ hU).preimage
    evolutionToCharacteristicPoint.continuous
  have hKD : K ⊆ D := fun p hp ↦ hKU (mem_image_of_mem _ hp)
  have hm : ContDiff ℝ ∞ (fun p : JPoint ↦ (conicMask a (R • p.2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_conicMask ha).comp
      (contDiff_snd.const_smul R))
  rw [twoTimeOrderField_curry_collared ℓ o a f (by linarith : R ≠ 0)]
  have h := cNorm_smul_on_open_le hK hD hKD hm.contDiffOn
    (contDiffOn_jointAmplitude_curry_extend ℓ o hU hf) m
  apply h.trans
  rw [twoTimeOrderSeminorm_curry_extend]
  have hmle := cNorm_normalizedField_le hb hR
  change cNorm K m (fun p : JPoint ↦ (conicMask a (R • p.2) : ℂ)) ≤ _ at hmle
  calc
    _ ≤ (m + 1 : ℝ) * 2 ^ m *
        normalizedSeminorm K m (fun p : JPoint ↦ (conicMask a p.2 : ℂ)) *
        cNorm K m (jointAmplitude (curryCharacteristicMatrix (extend ℓ o f))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmle (by positivity))
        (cNorm_nonneg _ _ _)
    _ ≤ _ := by
      unfold collarBoundConstant
      nlinarith [cNorm_nonneg K m (jointAmplitude (curryCharacteristicMatrix (extend ℓ o f)))]

/-- Finiteness and the quantitative shell estimate hold for the literal
collared amplitude at the SAME order, including `o=0` and `o=1`. -/
theorem twoTimeOrderSeminorm_curry_collared_le
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) {a : Euclidean d → ℝ}
    (ha : ContDiff ℝ ∞ a) {K : Set JPoint} {U : Set T}
    (hK : IsCompact K) (hU : IsOpen U)
    (hKU : evolutionToCharacteristicPoint '' K ⊆ ConicPhase.domain ℓ U)
    {f : T → Mat} (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) :
    BoundedTwoTimeOrderSeminorm o K m (curryCharacteristicMatrix (collared ℓ o a f)) ∧
      twoTimeOrderSeminorm o K m (curryCharacteristicMatrix (collared ℓ o a f)) ≤
        collarBoundConstant a K m *
          twoTimeOrderSeminorm o K m (curryCharacteristicMatrix (extend ℓ o f)) := by
  have hb (R : ℝ) (hR : 1 ≤ R) :=
    cNorm_twoTimeOrderField_curry_collared_le ℓ o ha hK hU hKU hf m hR
  constructor
  · refine ⟨collarBoundConstant a K m *
      twoTimeOrderSeminorm o K m (curryCharacteristicMatrix (extend ℓ o f)), ?_⟩
    rintro _ ⟨R, rfl⟩
    exact hb R R.2
  · apply Real.sSup_le _ (mul_nonneg (collarBoundConstant_pos a K m).le
      (twoTimeOrderSeminorm_nonneg _ _ _ _))
    rintro _ ⟨R, rfl⟩
    exact hb R R.2

/-- Original local amplitude jets produce the complete collared symbol
budget. The fixed continuation and mask add zero derivatives and preserve
the single-high reserve nine of `AmplitudeBounds` (`retarded-kernel`). -/
theorem twoTimeOrderSeminorm_curry_collared_le_local
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) {a : Euclidean d → ℝ}
    (ha : ContDiff ℝ ∞ a) {K : Set JPoint} {J U : Set T}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hpos : ∀ p ∈ K, 0 < ℓ p.2)
    (hmap : MapsTo (ConicPhase.normalize ℓ ∘ evolutionToCharacteristicPoint) K J)
    {f : T → Mat} (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) :
    twoTimeOrderSeminorm o K m (curryCharacteristicMatrix (collared ℓ o a f)) ≤
      (collarBoundConstant a K m * symbolBoundConstant (n := n) ℓ o K m) * cNorm J m f := by
  have hKU : evolutionToCharacteristicPoint '' K ⊆ ConicPhase.domain ℓ U := by
    rintro q ⟨p, hp, rfl⟩
    exact ⟨hpos p hp, hJU (hmap hp)⟩
  exact (twoTimeOrderSeminorm_curry_collared_le ℓ o ha hK hU hKU hf m).2.trans
    (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (twoTimeOrderSeminorm_curry_extend_le ℓ o hK hJ hU hJU hpos hmap hf m)
        (collarBoundConstant_pos a K m).le)

end JanetCartan.RegularSector.Characteristic.ConicAmplitude
