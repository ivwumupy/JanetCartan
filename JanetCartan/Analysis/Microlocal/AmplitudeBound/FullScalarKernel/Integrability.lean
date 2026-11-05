module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullScalarKernel.Basic

/-!
# Absolute integrability of the full scalar kernel

The physical support and zeroth-order bound in `app:ch_osc:lem:osc-amplitude`
suffice for absolute integrability at each compact frequency cutoff.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace JanetCartan.AmplitudeBound

variable {d : ℕ}

/-- The physical position pairing in `app:ch_osc:lem:osc-amplitude` is continuous. -/
theorem continuous_pairedPosition :
    Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      pairedPosition p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  dsimp
  split_ifs <;> fun_prop

/-- The compact physical cutoff makes every L² input integrable in
`app:ch_osc:lem:osc-amplitude`. -/
theorem integrable_boxCellCutoff_mul {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Integrable (fun y ↦ boxCellCutoff ℓ y * f y) := by
  apply (integrable_cutoffModulation (rightPositionChart ℓ)
    (measurable_rightPositionChart ℓ) (boxCellCutoff ℓ)
    (aestronglyMeasurable_boxCellCutoff ℓ) (Eventually.of_forall (norm_boxCellCutoff_le ℓ))
    (hasCompactSupport_boxCellCutoff hℓ) 0 f).congr
  filter_upwards [cutoffModulation_coeFn (rightPositionChart ℓ)
    (measurable_rightPositionChart ℓ) (boxCellCutoff ℓ)
    (aestronglyMeasurable_boxCellCutoff ℓ) (Eventually.of_forall (norm_boxCellCutoff_le ℓ))
    0 f] with y hy
  simpa [UnitAddTorus.mFourier_zero] using hy

variable (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b))
  {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
  (A : ℝ) (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)

include hℓ hR hs hzero in
/-- A fixed integrable physical majorant for the original amplitude kernel
(`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxScalarAmplitudeKernel_integrand_le
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (x y ξ : EuclideanSpace ℝ (Fin d)) :
    ‖Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
      b ξ (pairedPosition x y) * f y‖ ≤ A * ‖boxCellCutoff ℓ y * f y‖ := by
  have hA : 0 ≤ A := (norm_nonneg (b 0 0)).trans (hzero 0 0)
  rw [← boxCellCutoff_boxAmplitudePeriodization_eq hℓ hR (hs ξ) x y]
  simp only [norm_mul, ← Real.fourierChar_apply, Circle.norm_coe, one_mul]
  calc
    _ ≤ (1 * A) * ‖boxCellCutoff ℓ y‖ * ‖f y‖ := by
      gcongr
      · exact norm_boxCellCutoff_le ℓ x
      · exact norm_boxAmplitudePeriodization_le (hzero ξ) ℓ _
    _ = _ := by ring

include hb in
/-- Joint measurability of the untruncated physical amplitude at a fixed
output point (`app:ch_osc:lem:osc-amplitude`). -/
theorem stronglyMeasurable_boxAmplitude_pairedPosition (x : EuclideanSpace ℝ (Fin d)) :
    StronglyMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      b p.1 (pairedPosition x p.2)) := by
  exact hb.comp_measurable (measurable_fst.prodMk
    (continuous_pairedPosition.comp (continuous_const.prodMk continuous_snd)).measurable)

include hb hℓ hR hs A hzero

/-- The inner physical integral is absolutely convergent at every frequency,
for every L² input (`app:ch_osc:lem:osc-amplitude`). -/
theorem integrable_boxScalarAmplitudeKernel_inner
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (x ξ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun y ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        b ξ (pairedPosition x y) * f y) := by
  have hp : Continuous (fun y : EuclideanSpace ℝ (Fin d) ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I)) := by fun_prop
  have hm := (stronglyMeasurable_boxAmplitude_pairedPosition b hb x).comp_measurable
    (measurable_const.prodMk measurable_id : Measurable (fun y ↦ (ξ, y)))
  apply ((integrable_boxCellCutoff_mul hℓ.ne' f).norm.const_mul A).mono'
    ((hp.aestronglyMeasurable.mul hm.aestronglyMeasurable).mul (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun y ↦
    norm_boxScalarAmplitudeKernel_integrand_le b hℓ hR hs A hzero f x y ξ)

/-- The full kernel is absolutely integrable in the product of compact
frequency volume and physical volume (`app:ch_osc:lem:osc-amplitude`). -/
theorem integrable_boxScalarAmplitudeKernel_prod (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I) *
        b p.1 (pairedPosition x p.2) * f p.2)
      ((volume.restrict (Metric.closedBall 0 ρ)).prod volume) := by
  have hp : Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I)) := by fun_prop
  have hi : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) ↦ A)
      (Metric.closedBall 0 ρ) := integrableOn_const (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ).measure_ne_top
  apply (hi.mul_prod (integrable_boxCellCutoff_mul hℓ.ne' f).norm).mono'
  · exact (hp.aestronglyMeasurable.mul
      (stronglyMeasurable_boxAmplitude_pairedPosition b hb x).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f).comp_snd
  · exact Eventually.of_forall (fun p ↦
      norm_boxScalarAmplitudeKernel_integrand_le b hℓ hR hs A hzero f x p.2 p.1)

/-- Absolute convergence of the outer frequency integral of the full physical
amplitude (`app:ch_osc:lem:osc-amplitude`). -/
theorem integrableOn_boxScalarAmplitudeKernel_outer (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun ξ ↦ ∫ y,
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        b ξ (pairedPosition x y) * f y) (Metric.closedBall 0 ρ) :=
  (integrable_boxScalarAmplitudeKernel_prod b hb hℓ hR hs A hzero ρ f x).integral_prod_left

end JanetCartan.AmplitudeBound
