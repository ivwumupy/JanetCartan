module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier

/-!
# Negative Fourier norms paired with restriction Sobolev norms

The pairing needed for `app:ch_regular_base:eq:negative-duality` is proved on
actual local L² classes. The source is extended by zero, while the test uses
every genuine weak extension before taking the infimum of their jet norms.
All constants are chosen before the domain and either datum.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ArbitraryAccuracy

open LocalSobolev Pseudodifferential

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι]

/-- The uniform real component comparison constant used in
`app:ch_regular_base:eq:negative-duality`. -/
def localDualityConstant (n N : ℕ) (b : OrthonormalBasis ι ℝ F) : ℝ :=
  (componentFourierSobolev_extension_bounds n N b).choose

/-- Positivity of the local pairing constant, including zero dimension and
order (`app:ch_regular_base:eq:negative-duality`). -/
theorem localDualityConstant_pos (n N : ℕ) (b : OrthonormalBasis ι ℝ F) :
    0 < localDualityConstant n N b :=
  (componentFourierSobolev_extension_bounds n N b).choose_spec.1

/-- The concrete supported/restriction pairing for finite-dimensional real
targets (`app:ch_regular_base:eq:negative-duality`). Negative Fourier membership
of the zero extension follows from its L² membership; the positive membership
and norm comparison follow from genuine weak jets, without a boundary extension
assumption. This supplies the duality input to the inverse remainder. -/
theorem abs_inner_le_negativeNorm_mul_restrictionSobolevNorm
    (b : OrthonormalBasis ι ℝ F) {W : Set (EuclideanSpace ℝ (Fin n))}
    (hW : MeasurableSet W) (N : ℕ) (h v : LocalL2 W F)
    (hv : MemRestrictionSobolev W N v) :
    |inner ℝ h v| ≤ localDualityConstant n N b *
      componentFourierSobolevNorm b (-(N : ℝ)) (SmallSupport.zeroExtend hW h) *
        restrictionSobolevNorm W N v := by
  have hc := (localDualityConstant_pos n N b).le
  have hn := componentFourierSobolevNorm_nonneg b (-(N : ℝ))
    (SmallSupport.zeroExtend hW h)
  apply le_mul_restrictionSobolevNorm_of_extensions hv (mul_nonneg hc hn)
  intro e
  obtain ⟨he, hbound⟩ :=
    (componentFourierSobolev_extension_bounds n N b).choose_spec.2 W v e
  rw [← e.inner_zeroExtend hW h]
  calc
    _ ≤ componentFourierSobolevNorm b (-(N : ℝ)) (SmallSupport.zeroExtend hW h) *
        componentFourierSobolevNorm b (N : ℝ) e.toL2 :=
      abs_inner_le_componentFourierSobolevNorm_mul b
        (memComponentFourierSobolev_of_nonpos b (by simp) _) he
    _ ≤ componentFourierSobolevNorm b (-(N : ℝ)) (SmallSupport.zeroExtend hW h) *
        (localDualityConstant n N b * e.jetNorm) :=
      mul_le_mul_of_nonneg_left hbound hn
    _ = _ := by ring

/-- Uniform scalar comparison constant for the complex pairing in
`app:ch_regular_base:eq:negative-duality`. -/
def scalarLocalDualityConstant (n N : ℕ) : ℝ :=
  (scalarFourierSobolev_extension_bounds n N).choose

/-- Positivity of the scalar constant for
`app:ch_regular_base:eq:negative-duality`. -/
theorem scalarLocalDualityConstant_pos (n N : ℕ) :
    0 < scalarLocalDualityConstant n N :=
  (scalarFourierSobolev_extension_bounds n N).choose_spec.1

/-- The complex pairing with a genuine weak extension is precisely the local
pairing (`app:ch_regular_base:eq:negative-duality`). -/
theorem complex_inner_zeroExtend_extension
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : MeasurableSet W)
    {N : ℕ} (h v : LocalL2 W ℂ) (e : SobolevExtension W N v) :
    inner ℂ (SmallSupport.zeroExtend hW h) e.toL2 = inner ℂ h v := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, W.indicator (fun y ↦ inner ℂ (h y) (e.toL2 y)) x := by
      apply integral_congr_ae
      filter_upwards [SmallSupport.zeroExtend_coeFn hW h] with x hx
      rw [hx]
      by_cases hxW : x ∈ W <;> simp [hxW]
    _ = ∫ x in W, inner ℂ (h x) (e.toL2 x) := integral_indicator hW
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [e.toL2_restrict] with x hx
      rw [hx]

/-- The scalar complex version of the genuine local negative pairing
(`app:ch_regular_base:eq:negative-duality`), with the absolute value interpreted
as the complex norm. -/
theorem norm_inner_le_negativeNorm_mul_restrictionSobolevNorm
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : MeasurableSet W)
    (N : ℕ) (h v : LocalL2 W ℂ) (hv : MemRestrictionSobolev W N v) :
    ‖inner ℂ h v‖ ≤ scalarLocalDualityConstant n N *
      fourierSobolevNorm (-(N : ℝ)) (SmallSupport.zeroExtend hW h) *
        restrictionSobolevNorm W N v := by
  have hc := (scalarLocalDualityConstant_pos n N).le
  have hn := fourierSobolevNorm_nonneg (-(N : ℝ)) (SmallSupport.zeroExtend hW h)
  apply le_mul_restrictionSobolevNorm_of_extensions hv (mul_nonneg hc hn)
  intro e
  obtain ⟨he, hbound⟩ :=
    (scalarFourierSobolev_extension_bounds n N).choose_spec.2 W v e
  rw [← complex_inner_zeroExtend_extension hW h v e]
  calc
    _ ≤ fourierSobolevNorm (-(N : ℝ)) (SmallSupport.zeroExtend hW h) *
        fourierSobolevNorm (N : ℝ) e.toL2 :=
      norm_inner_le_fourierSobolevNorm_mul (memFourierSobolev_of_nonpos (by simp) _) he
    _ ≤ fourierSobolevNorm (-(N : ℝ)) (SmallSupport.zeroExtend hW h) *
        (scalarLocalDualityConstant n N * e.jetNorm) :=
      mul_le_mul_of_nonneg_left hbound hn
    _ = _ := by ring

end JanetCartan.ArbitraryAccuracy
