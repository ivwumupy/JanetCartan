module

public import JanetCartan.Iteration.PhysicalScalarChannel.TimeIntegration
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.ChartInput
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Multiplication

/-!
# Removing the normalized annular half weight on the input

The scalar normal family contains the original `sqrt ‖θ‖` amplitude. The bare
fixed-carrier test uses the same operator composed with this bounded annular
multiplier. No original mask, measure, or frequency variable is changed.
The block input bound is independent of the number of bands.
Consumer: `app:ch_mean_pairs:eq:raw-adjoint-moments`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace JanetCartan.PhysicalScalarChannel
open RawInputPartition RawInputHilbert RawPrimary.SliceBounds

/-- Only the already certified annulus is used. This is an input multiplier,
not a replacement of the original detector or dyadic cutoff. -/
def annularInverseHalf {d : ℕ} (θ : Euclidean d) : ℂ :=
  if (1 / 2 : ℝ) ≤ ‖θ‖ then ((Real.sqrt ‖θ‖)⁻¹ : ℝ) else 0

/-- The normalized input multiplier is measurable on every original chart. -/
theorem measurable_annularInverseHalf (d : ℕ) :
    Measurable (annularInverseHalf (d := d)) := by
  unfold annularInverseHalf
  apply Measurable.ite (measurableSet_le measurable_const measurable_norm)
  · exact Complex.measurable_ofReal.comp ((Real.continuous_sqrt.measurable.comp measurable_norm).inv)
  · exact measurable_const

/-- A fixed bound suffices; there is no original-frequency or band-count loss. -/
theorem norm_annularInverseHalf_le_two {d : ℕ} (θ : Euclidean d) :
    ‖annularInverseHalf θ‖ ≤ 2 := by
  by_cases h : (1 / 2 : ℝ) ≤ ‖θ‖
  · have hpos : 0 < Real.sqrt ‖θ‖ := Real.sqrt_pos.mpr (by linarith)
    rw [annularInverseHalf, ite_eq_left h, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    apply (inv_le_iff_one_le_mul₀ hpos).mpr
    have hs := Real.sq_sqrt (norm_nonneg θ)
    nlinarith [Real.sqrt_nonneg ‖θ‖, sq_nonneg (Real.sqrt ‖θ‖ - 1)]
  · simp only [annularInverseHalf, ite_eq_right h, norm_zero]
    norm_num

/-- Exact cancellation on the SAME annulus; no inequality replaces the kernel. -/
theorem sqrt_mul_annularInverseHalf {d : ℕ} {θ : Euclidean d}
    (hθ : (1 / 2 : ℝ) ≤ ‖θ‖) :
    (Real.sqrt ‖θ‖ : ℂ) * annularInverseHalf θ = 1 := by
  have hpos : 0 < Real.sqrt ‖θ‖ := Real.sqrt_pos.mpr (by linarith)
  simp only [annularInverseHalf, ite_eq_left hθ, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]

/-- The original wide-band dilation and chart restriction followed by the
fixed normalized annular multiplier. -/
def bareChartInput (n j : ℕ) (D : Set (Euclidean (n - 1))) :
    WideBandL2 n j →L[ℂ] Lp ℂ 2 (volume.restrict D) :=
  (boundedMultiplier ((measurable_annularInverseHalf (n - 1)).aestronglyMeasurable)
    (Filter.Eventually.of_forall norm_annularInverseHalf_le_two)).comp
      (wideBandChartInput n j D)

/-- The single input map has an absolute bound, before every band index. -/
theorem norm_bareChartInput_le (n j : ℕ) (D : Set (Euclidean (n - 1))) :
    ‖bareChartInput n j D‖ ≤ 2 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 2 * 1 := mul_le_mul
      (norm_boundedMultiplier_le _ (by norm_num) _)
      (norm_wideBandChartInput_le j D) (norm_nonneg _) (by norm_num)
    _ = 2 := mul_one _

/-- Literal input action on the original restricted measure. -/
theorem bareChartInput_apply_ae (n j : ℕ) (D : Set (Euclidean (n - 1)))
    (f : WideBandL2 n j) :
    bareChartInput n j D f =ᵐ[volume.restrict D] fun θ ↦
      annularInverseHalf θ * (wideBand n 0).indicator
        (fun θ ↦ wideBandDilation n j f θ) θ := by
  filter_upwards [boundedMultiplier_coeFn
    ((measurable_annularInverseHalf (n - 1)).aestronglyMeasurable)
    (Filter.Eventually.of_forall norm_annularInverseHalf_le_two)
    (wideBandChartInput n j D f), wideBandChartInput_apply_ae j D f] with θ hθ hchart
  exact hθ.trans (congrArg (fun z ↦ annularInverseHalf θ * z) hchart)

/-- Block-diagonal input transfer on the full original wide input. -/
def bareChartRow (n J : ℕ) (D : Set (Euclidean (n - 1))) :
    WideInput n J →L[ℂ] PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 (volume.restrict D)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin J ↦ Lp ℂ 2 (volume.restrict D))).symm
    |>.toContinuousLinearMap.comp (ContinuousLinearMap.pi (fun j : Fin J ↦
      (bareChartInput n j.val D).comp (PiLp.proj 2 _ j)))

/-- Every block is the original band, with its own literal dilation. -/
@[simp] theorem bareChartRow_apply (n J : ℕ) (D : Set (Euclidean (n - 1)))
    (f : WideInput n J) (j : Fin J) :
    bareChartRow n J D f j = bareChartInput n j.val D (f j) := rfl

/-- The whole input transfer has the SAME fixed bound for every band count. -/
theorem norm_bareChartRow_le (n J : ℕ) (D : Set (Euclidean (n - 1))) :
    ‖bareChartRow n J D‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have hs : ‖bareChartRow n J D f‖ ^ 2 ≤ (2 * ‖f‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hb := ((bareChartInput n j.val D).le_opNorm (f j)).trans
      (mul_le_mul_of_nonneg_right (norm_bareChartInput_le n j.val D) (norm_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq (mul_pow _ _ _)
  nlinarith [norm_nonneg (bareChartRow n J D f), norm_nonneg f]

end JanetCartan.PhysicalScalarChannel
