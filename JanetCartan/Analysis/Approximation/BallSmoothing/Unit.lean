module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Realization
public import JanetCartan.Analysis.Approximation.BallSmoothing.Cutoff
public import JanetCartan.Analysis.Approximation.BallSmoothing.Moments

/-!
# The actual unit-ball smoother

The operator in `app:ch_regular_base:eq:extension-radial-formula` is the
literal finite binomial combination of inward averages with the actual fixed
kernel and thin cutoff. Its convolution realization proves global smoothness
using only continuity on the original closed ball. Restriction independence
ensures that exterior values of an input representative play no role.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric ContinuousLinearMap
open scoped ContDiff Convolution

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal finite-moment inward smoother of
`app:ch_regular_base:eq:extension-radial-formula`. The same real kernel and
coefficients act on every component of the target space. -/
def unitSmoothing (R : ℝ) (m : ℕ) (f : E → F) : E → F :=
  radialSmoothing (unitCutoff n R) (coefficient m) (kernel n) R m f

private theorem cutoff_active_collar {R : ℝ} (hR : 1 ≤ R) (x : E)
    (hx : unitCutoff n R x ≠ 0) : ‖x‖ ≤ 1 + 1 / (2 * R) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hb := mem_ball_zero_iff.mp
    (unitCutoff_tsupport_subset n hR (subset_tsupport _ hx))
  apply hb.le.trans
  have hd : 1 / (4 * R) ≤ 1 / (2 * R) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- Exact fixed-kernel realization of the SAME unit-ball formula, used to
prove all output derivative bounds from the original `C⁰` input norm
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem unitSmoothing_eq_regularized {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : (2 : ℝ) * m ≤ R) (f : E → F) :
    unitSmoothing R m f = fun x ↦ unitCutoff n R x •
      ∑ j ∈ Finset.Icc 1 m, coefficient m j • regularizedAverage (kernel n) R j f x := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact radialSmoothing_eq_regularized hm hR _
    (cutoff_active_collar (by linarith)) _ tsupport_kernel_subset f

/-- The actual inward smoother is globally smooth. No exterior input
regularity is required (`app:ch_regular_base:lem:ball-extension`). -/
theorem contDiff_unitSmoothing {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : (2 : ℝ) * m ≤ R) {f : E → F}
    (hf : ContinuousOn f (closedBall (0 : E) 1)) :
    ContDiff ℝ ∞ (unitSmoothing R m f) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR0 : R ≠ 0 := ne_of_gt (by linarith)
  rw [unitSmoothing_eq_regularized hm hR f]
  apply (unitCutoff_contDiff n R).smul
  apply ContDiff.sum
  intro j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  exact (contDiff_regularizedAverage hR0 hj0 hasCompactSupport_kernel
    contDiff_kernel hf).const_smul _

/-- The whole output support lies in the actual thin collar, independently
of the approximation order and input
(`app:ch_regular_base:lem:ball-extension`). -/
theorem unitSmoothing_tsupport_subset {R : ℝ} (hR : 1 ≤ R)
    (m : ℕ) (f : E → F) :
    tsupport (unitSmoothing R m f) ⊆ ball (0 : E) (1 + 1 / (4 * R)) :=
  (tsupport_smul_subset_left _ _).trans (unitCutoff_tsupport_subset n hR)

/-- One fixed compact set contains every output support for every valid
scale and approximation order
(`app:ch_regular_base:lem:ball-extension`). -/
theorem unitSmoothing_tsupport_subset_closedBall_two {R : ℝ} (hR : 1 ≤ R)
    (m : ℕ) (f : E → F) :
    tsupport (unitSmoothing R m f) ⊆ closedBall (0 : E) 2 :=
  (tsupport_smul_subset_left _ _).trans
    (unitCutoff_tsupport_subset_closedBall_two n hR)

/-- Actual compact support of the same output, with no input support
assumption (`app:ch_regular_base:lem:ball-extension`). -/
theorem unitSmoothing_hasCompactSupport {R : ℝ} (hR : 1 ≤ R)
    (m : ℕ) (f : E → F) : HasCompactSupport (unitSmoothing R m f) :=
  (isCompact_closedBall (0 : E) 2).of_isClosed_subset
    (isClosed_tsupport _) (unitSmoothing_tsupport_subset_closedBall_two hR m f)

/-- The construction depends only on the original closed-ball values.
Thus its linear map on smooth representatives below defines a genuine
operator on smooth closed-ball data
(`app:ch_regular_base:lem:ball-extension`). -/
theorem unitSmoothing_congr_closedBall {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : (2 : ℝ) * m ≤ R) {f g : E → F}
    (hfg : EqOn f g (closedBall (0 : E) 1)) :
    unitSmoothing R m f = unitSmoothing R m g := by
  have he : inputExtension f = inputExtension g := by
    funext x
    by_cases hx : x ∈ closedBall (0 : E) 1
    · simp only [inputExtension, indicator_of_mem hx, hfg hx]
    · simp only [inputExtension, indicator_of_notMem hx]
  rw [unitSmoothing_eq_regularized hm hR f, unitSmoothing_eq_regularized hm hR g]
  have href j : reflectedInput R j f = reflectedInput R j g := by
    funext z
    simp only [reflectedInput, he]
  simp only [regularizedAverage, href]

end JanetCartan.BallSmoothing
