module

public import JanetCartan.Analysis.Extension.Ball.Regularity.BoundaryMoments.Moments

/-!
# Affine dependence of radial sampling jets

The radial map in `app:ch_regular_base:eq:extension-radial-formula` depends
affinely on `b = -2^k`. At `b = 1` it is the identity near the sphere.
This is the geometric input to the boundary-jet argument following
`app:ch_regular_base:eq:extension-collar-l2`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (p : JanetCartan.BallExtension.Parameters E)

/-- The constant part of radial sampling as a function of `b` in
`app:ch_regular_base:eq:extension-radial-formula`. -/
def radialBase (y : E) : E :=
  p.center + (p.radius / ‖y - p.center‖) • (y - p.center)

/-- The linear part of radial sampling as a function of `b` in
`app:ch_regular_base:eq:extension-radial-formula`. -/
def radialSlope (y : E) : E :=
  ((‖y - p.center‖ - p.radius) / ‖y - p.center‖) • (y - p.center)

/-- The radial map is affine in `b = -2^k`, as used in the boundary-jet
argument following `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem radialPoint_eq_base_add_slope (k : ℕ) (y : E) :
    p.radialPoint k y = p.radialBase y + (-(2 : ℝ) ^ k) • p.radialSlope y := by
  simp only [radialPoint, radialBase, radialSlope, sub_div, mul_div_assoc,
    sub_smul, mul_smul, neg_smul]
  abel

/-- Both affine parts of radial sampling are smooth away from the center,
for the boundary-jet argument after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem contDiffAt_radialBase {x : E} (hx : x ≠ p.center) :
    ContDiffAt ℝ ∞ p.radialBase x := by
  have hn : ContDiffAt ℝ ∞ (fun y ↦ ‖y - p.center‖) x :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hx)
  exact contDiffAt_const.add ((contDiffAt_const.div hn
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))).smul
    (contDiffAt_id.sub contDiffAt_const))

/-- Smoothness of the linear part needed in the boundary-jet argument after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem contDiffAt_radialSlope {x : E} (hx : x ≠ p.center) :
    ContDiffAt ℝ ∞ p.radialSlope x := by
  have hn : ContDiffAt ℝ ∞ (fun y ↦ ‖y - p.center‖) x :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hx)
  exact ((hn.sub contDiffAt_const).div hn
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))).smul
    (contDiffAt_id.sub contDiffAt_const)

/-- Evaluation at `b = 1` recovers the identity near the sphere, as required
by `app:ch_regular_base:eq:extension-infinite-moments`. -/
theorem radialBase_add_radialSlope {y : E} (hy : y ≠ p.center) :
    p.radialBase y + p.radialSlope y = y := by
  have hn : ‖y - p.center‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
  simp only [radialBase, radialSlope, add_assoc p.center,
    ← add_smul, ← add_div, add_sub_cancel, div_self hn, one_smul]

/-- Every radial sampling jet is affine in `b = -2^k`, the input to the
moment calculation after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem iteratedFDeriv_radialPoint_eq_base_add_slope {x : E} (hx : x ≠ p.center)
    (k m : ℕ) :
    iteratedFDeriv ℝ m (p.radialPoint k) x =
      iteratedFDeriv ℝ m p.radialBase x +
        (-(2 : ℝ) ^ k) • iteratedFDeriv ℝ m p.radialSlope x := by
  have hfun : p.radialPoint k = p.radialBase + (-(2 : ℝ) ^ k) • p.radialSlope :=
    funext (p.radialPoint_eq_base_add_slope k)
  rw [hfun]
  change iteratedFDeriv ℝ m (p.radialBase + (fun y ↦ (-(2 : ℝ) ^ k) • p.radialSlope y)) x = _
  rw [iteratedFDeriv_add_apply (i := m) ((p.contDiffAt_radialBase hx).of_le (by simp))
    (((p.contDiffAt_radialSlope hx).of_le (by simp)).const_smul (-(2 : ℝ) ^ k)),
    iteratedFDeriv_const_smul_apply' (i := m) (a := -(2 : ℝ) ^ k) ((p.contDiffAt_radialSlope hx).of_le (by simp))]

/-- The sum of the two affine parts of each jet is the identity jet;
this identifies evaluation at one in `app:ch_regular_base:eq:extension-infinite-moments`. -/
theorem iteratedFDeriv_radialBase_add_radialSlope {x : E} (hx : x ≠ p.center) (m : ℕ) :
    iteratedFDeriv ℝ m p.radialBase x + iteratedFDeriv ℝ m p.radialSlope x =
      iteratedFDeriv ℝ m (id : E → E) x := by
  rw [← iteratedFDeriv_add_apply (i := m) ((p.contDiffAt_radialBase hx).of_le (by simp))
    ((p.contDiffAt_radialSlope hx).of_le (by simp))]
  have he : (p.radialBase + p.radialSlope) =ᶠ[𝓝 x] (id : E → E) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact p.radialBase_add_radialSlope hy
  exact (he.iteratedFDeriv ℝ m).self_of_nhds

end JanetCartan.BallExtension.Parameters
