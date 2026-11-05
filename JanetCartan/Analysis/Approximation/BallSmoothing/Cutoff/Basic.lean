module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The actual thin cutoff for inward ball smoothing

The fixed smooth transition is applied to a rescaled squared radius. The
cutoff is one on the closed unit ball and has compact support strictly inside
the collar of width `1/(4R)`. This is the physical cutoff in
`app:ch_regular_base:lem:ball-extension`, used by `main:lem:smoothing`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.BallSmoothing

/-- The actual cutoff used by the inward finite-moment smoother. Its formula
contains no derivative order (`app:ch_regular_base:lem:ball-extension`). -/
def unitCutoff (n : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.smoothTransition (2 - 8*R*(‖x‖^2-1))

/-- Squared radius makes the actual cutoff smooth also at the origin
(`app:ch_regular_base:lem:ball-extension`). -/
theorem unitCutoff_contDiff (n : ℕ) (R : ℝ) : ContDiff ℝ ∞ (unitCutoff n R) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)))

/-- The cutoff is real and lies between zero and one, as required by the
low smoothing estimate `main:eq:smoothing-low`. -/
theorem unitCutoff_mem_Icc (n : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    unitCutoff n R x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The full closed unit ball is in the plateau of the actual cutoff.
Thus the cutoff creates no approximation error there
(`app:ch_regular_base:eq:ball-extension-continuous`). -/
theorem unitCutoff_eq_one (n : ℕ) {R : ℝ} (hR : 1 ≤ R)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ closedBall 0 1) :
    unitCutoff n R x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hs : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hp : 8*R*(‖x‖^2-1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

private theorem unitCutoff_tsupport_quadratic (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    tsupport (unitCutoff n R) ⊆ {x | ‖x‖^2 ≤ 1+1/(4*R)} := by
  apply closure_minimal _ (isClosed_le (continuous_norm.pow 2) continuous_const)
  intro x hx
  have ha : 0 < 2-8*R*(‖x‖^2-1) := by
    by_contra hn
    exact hx (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hn))
  have hb : ‖x‖^2-1 < 1/(4*R) :=
    (lt_div_iff₀ (by positivity : 0 < 4*R)).mpr (by nlinarith)
  change ‖x‖^2 ≤ 1+1/(4*R)
  linarith

/-- The closed support is strictly inside the prescribed thin collar. This
leaves the original inward kernel a spatial buffer
(`app:ch_regular_base:lem:ball-extension`). -/
theorem unitCutoff_tsupport_subset (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    tsupport (unitCutoff n R) ⊆ ball 0 (1+1/(4*R)) := by
  intro x hx
  have hs := unitCutoff_tsupport_quadratic n hR hx
  change ‖x‖^2 ≤ 1+1/(4*R) at hs
  have ht : 0 < 1/(4*R) := by positivity
  have hsq : ‖x‖^2 < (1+1/(4*R))^2 := by nlinarith [sq_nonneg (1/(4*R))]
  exact mem_ball_zero_iff.mpr
    ((sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp hsq)

/-- All scales use one fixed compact spatial support
(`main:lem:smoothing`). -/
theorem unitCutoff_tsupport_subset_closedBall_two (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    tsupport (unitCutoff n R) ⊆ closedBall 0 2 := by
  have ht : 1/(4*R) ≤ 1/4 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (by linarith)
  exact (unitCutoff_tsupport_subset n hR).trans
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))

/-- The same actual cutoff has compact support at every admissible scale
(`app:ch_regular_base:lem:ball-extension`). -/
theorem unitCutoff_hasCompactSupport (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    HasCompactSupport (unitCutoff n R) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 2).of_isClosed_subset
    (isClosed_tsupport _) (unitCutoff_tsupport_subset_closedBall_two n hR)

end JanetCartan.BallSmoothing
