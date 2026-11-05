module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.KernelDefinitions
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Elementary off-diagonal heat bounds

These are pointwise estimates for the explicit heat integrand in
`app:ch_background:prop:bg-frame`, Step 1. They supply the separation part
of the domination needed to differentiate `imageBesselKernel`; they do not
assert that differentiation under the integral has already been justified.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Spatial smoothness of each fixed-time heat density used in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem contDiff_imageBesselHeatKernel (t : ℝ) :
    ContDiff ℝ ∞ (imageBesselHeatKernel (d := d) t) := by
  unfold imageBesselHeatKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp)

/-- Positivity of the positive-time heat density in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem imageBesselHeatKernel_pos {t : ℝ} (ht : 0 < t) (x : E) :
    0 < imageBesselHeatKernel t x := by
  unfold imageBesselHeatKernel
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- Splitting the Gaussian leaves both uniform small-time suppression and
spatial decay outside a gap. This is the pointwise majorant for the
off-diagonal integral in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem imageBesselHeatKernel_le_gap_majorant {t δ : ℝ} (ht : 0 < t)
    (hδ : 0 ≤ δ) (x : E) (hx : δ ≤ ‖x‖) :
    imageBesselHeatKernel t x ≤
      (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-(δ ^ 2) / (8 * t)) * Real.exp (-(‖x‖ ^ 2) / (8 * t)) := by
  have hs : δ ^ 2 ≤ ‖x‖ ^ 2 := sq_le_sq₀ hδ (norm_nonneg x) |>.mpr hx
  have he : -(‖x‖ ^ 2) / (4 * t) ≤ -(δ ^ 2) / (8 * t) +
      -(‖x‖ ^ 2) / (8 * t) := by
    calc
      _ ≤ (-(δ ^ 2) - ‖x‖ ^ 2) / (8 * t) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      _ = _ := by ring
  unfold imageBesselHeatKernel
  rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.rpow_nonneg (by positivity) _)

/-- The nonzero translates have a common positive-time majorant with the
literal gap `1 - 2r`, for the lattice integral in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem imageBesselHeatKernel_sub_add_integerTranslation_le {r t : ℝ}
    (hr : r < 1 / 2) (ht : 0 < t) {x y : E}
    (hx : ∀ i, |x i| ≤ r) (hy : ∀ i, |y i| ≤ r)
    {k : Fin d → ℤ} (hk : k ≠ 0) :
    imageBesselHeatKernel t (x - y + integerTranslation k) ≤
      (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-((1 - 2 * r) ^ 2) / (8 * t)) *
        Real.exp (-(‖x - y + integerTranslation k‖ ^ 2) / (8 * t)) :=
  imageBesselHeatKernel_le_gap_majorant ht (by linarith) _
    (norm_sub_add_integerTranslation_ge hx hy hk)

/-- The mass factor trades part of the Gaussian for exponential spatial
decay, while preserving small-time suppression from the gap. This is the
zeroth-order integrand bound for the lattice sum in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem imageBessel_integrand_le_gap_exponential {t δ : ℝ} (ht : 0 < t)
    (hδ : 0 ≤ δ) (x : E) (hx : δ ≤ ‖x‖) :
    t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x ≤
      (t ^ (-(1 : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-(δ ^ 2) / (8 * t)) * Real.exp (-t / 2)) *
        Real.exp (-‖x‖ / 2) := by
  have he : -t + -(‖x‖ ^ 2) / (8 * t) ≤ -t / 2 + -‖x‖ / 2 := by
    have hs := sq_nonneg (2 * t - ‖x‖)
    have hdiv : -(‖x‖ ^ 2) / (8 * t) ≤ t / 2 - ‖x‖ / 2 := by
      apply (div_le_iff₀ (show 0 < 8 * t by positivity)).mpr
      nlinarith
    linarith
  have hmass : Real.exp (-t) * Real.exp (-(‖x‖ ^ 2) / (8 * t)) ≤
      Real.exp (-t / 2) * Real.exp (-‖x‖ / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr he
  calc
    _ ≤ t ^ (-(1 : ℝ) / 2) * Real.exp (-t) *
        ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
          Real.exp (-(δ ^ 2) / (8 * t)) * Real.exp (-(‖x‖ ^ 2) / (8 * t))) :=
      mul_le_mul_of_nonneg_left (imageBesselHeatKernel_le_gap_majorant ht hδ x hx)
        (by positivity)
    _ = (t ^ (-(1 : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-(δ ^ 2) / (8 * t))) *
        (Real.exp (-t) * Real.exp (-(‖x‖ ^ 2) / (8 * t))) := by ring
    _ ≤ (t ^ (-(1 : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-(δ ^ 2) / (8 * t))) *
        (Real.exp (-t / 2) * Real.exp (-‖x‖ / 2)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end JanetCartan.ContinuumNormalReduction.ImageNormal
