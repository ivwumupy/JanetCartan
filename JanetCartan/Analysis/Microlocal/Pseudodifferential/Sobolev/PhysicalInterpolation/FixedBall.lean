module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Bounds

/-!
# The fixed ball for physical amplitude seminorms

The coordinate budget and the actual `cNorm` on a ball containing the physical
support are comparable, as used in `app:lem:elementary-interpolation-jets` and
Step 3 of `app:ch_regular_base:thm:actual-calculus`.
-/

@[expose] public noncomputable section
open scoped ContDiff
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential

/-- `app:lem:elementary-interpolation-jets`: a fixed positive radius enclosing
the physical box, depending only on its width and dimension. -/
def physicalInterpolationRadius (n : ℕ) (R : ℝ) : ℝ := (n : ℝ) * |R| + 1

/-- `app:lem:elementary-interpolation-jets`: the enclosing radius is positive. -/
theorem physicalInterpolationRadius_pos (n : ℕ) (R : ℝ) :
    0 < physicalInterpolationRadius n R := by
  unfold physicalInterpolationRadius
  positivity

/-- `app:ch_regular_base:thm:actual-calculus`: the topological support of a
fixed-box amplitude lies in the explicitly chosen fixed ball. -/
theorem tsupport_subset_physicalInterpolationBall {n : ℕ} {R : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox R f) :
    tsupport f ⊆ Metric.closedBall 0 (physicalInterpolationRadius n R) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsum : z = ∑ i, EuclideanSpace.single i (z i) := by
    ext i
    simp [EuclideanSpace.single]
  calc
    ‖z‖ = ‖∑ i, EuclideanSpace.single i (z i)‖ := congrArg norm hsum
    _ ≤ ∑ i, ‖EuclideanSpace.single i (z i)‖ := norm_sum_le _ _
    _ = ∑ i, |z i| := by simp [EuclideanSpace.single, PiLp.norm_single]
    _ ≤ ∑ _i : Fin n, |R| := Finset.sum_le_sum fun i _ ↦ (hs z hz i).trans (le_abs_self R)
    _ ≤ physicalInterpolationRadius n R := by simp [physicalInterpolationRadius]

/-- `app:lem:elementary-interpolation-jets`: the seminorm on the enclosing ball
bounds physical derivatives everywhere, since those derivatives vanish off the
amplitude's topological support. -/
theorem norm_coordinateDeriv_le_cNorm_physicalInterpolationBall {n N : ℕ} {R : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : SupportedInCenteredBox R f) (is : List (Fin n)) (hi : is.length ≤ N)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖euclideanCoordinateDerivList is f z‖ ≤
      cNorm (Metric.closedBall 0 (physicalInterpolationRadius n R)) N f := by
  by_cases hz : z ∈ Metric.closedBall 0 (physicalInterpolationRadius n R)
  · exact norm_coordinateDeriv_le_cNorm_closedBall hf _ _ is hi hz
  · have hzero : iteratedFDeriv ℝ is.length f z = 0 := by
      by_contra h
      exact hz (tsupport_subset_physicalInterpolationBall hs
        (support_iteratedFDeriv_subset is.length h))
    apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hf is z).trans
    rw [hzero, norm_zero]
    exact cNorm_nonneg _ _ _

end JanetCartan.Pseudodifferential
