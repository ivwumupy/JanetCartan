module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Reduced.Formula
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Local cutoff estimates for the entire reduced coefficient array

The input of `app:ch_background:eq:bg-frame-tame` is smooth only on a ball.
The cutoff product is globally smooth because it vanishes on a neighborhood
of every point outside the cutoff's closed support. The constants depend only
on the fixed cutoff, radius and differentiated order.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace JanetCartan.ContinuumRow.ImageGeometry.Periodization

open GeometricProfile

variable {n : ℕ}

/-- The same cut array is used for all entries in `app:ch_background:defn:bg-row`. -/
def cutReducedCoefficients (χ : Euclidean n → ℝ)
    (q : Euclidean n → ReducedCoefficientIndex n → ℝ) :
    Euclidean n → ReducedCoefficientIndex n → ℝ := fun x ↦ χ x • q x

/-- The cut array retains the fixed physical support in `app:ch_background:defn:bg-row`. -/
theorem tsupport_cutReducedCoefficients_subset (χ : Euclidean n → ℝ)
    (q : Euclidean n → ReducedCoefficientIndex n → ℝ) :
    tsupport (cutReducedCoefficients χ q) ⊆ tsupport χ :=
  tsupport_smul_subset_left χ q

/-- Local coefficient smoothness suffices for the actual global cut array of
`app:ch_background:defn:bg-row`, including outside the validity ball. -/
theorem contDiff_cutReducedCoefficients {χ : Euclidean n → ℝ} {R : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Metric.ball 0 R)
    {q : Euclidean n → ReducedCoefficientIndex n → ℝ}
    (hq : ContDiffOn ℝ ∞ q (Metric.ball 0 R)) :
    ContDiff ℝ ∞ (cutReducedCoefficients χ q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul ((hq x (hs hx)).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hs hx)))
  · apply (contDiffAt_const (c := (0 : ReducedCoefficientIndex n → ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [cutReducedCoefficients, hy]

/-- Positive constants fixed before the coefficient array in
`app:ch_background:eq:bg-frame-tame`; the finite sum is the Leibniz constant. -/
def cutoffDerivativeBound (χ : Euclidean n → ℝ) (r : ℝ) (m : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * cNorm (Metric.closedBall 0 r) m χ

/-- Positivity of the fixed derivative constants in `app:ch_background:eq:bg-frame-tame`. -/
theorem cutoffDerivativeBound_pos (χ : Euclidean n → ℝ) (r : ℝ) (m : ℕ) :
    0 < cutoffDerivativeBound χ r m := by
  have h : 0 ≤ ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * cNorm (Metric.closedBall 0 r) m χ :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _)
  unfold cutoffDerivativeBound
  linarith

/-- Uniform bound for every full derivative of the cut array, using only local
smoothness of the input (`app:ch_background:eq:bg-frame-tame`). -/
theorem norm_iteratedFDeriv_cutReducedCoefficients_le
    {χ : Euclidean n → ℝ} {r R : ℝ} (hrR : r < R)
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Metric.ball 0 r)
    {q : Euclidean n → ReducedCoefficientIndex n → ℝ}
    (hq : ContDiffOn ℝ ∞ q (Metric.ball 0 R)) (m : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ m (cutReducedCoefficients χ q) x‖ ≤
      cutoffDerivativeBound χ r m * cNorm (Metric.closedBall 0 r) m q := by
  by_cases hx : x ∈ tsupport χ
  · have hxr : x ∈ Metric.closedBall (0 : Euclidean n) r :=
      Metric.ball_subset_closedBall (hs hx)
    have hxR : x ∈ Metric.ball (0 : Euclidean n) R :=
      Metric.closedBall_subset_ball hrR hxr
    have hqa (y : Euclidean n) (hy : y ∈ Metric.closedBall (0 : Euclidean n) r) :
        ContDiffAt ℝ (m : ℕ∞ω) q y :=
      ((hq y (Metric.closedBall_subset_ball hrR hy)).contDiffAt
        (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hrR hy))).of_le (by simp)
    have hp := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn hq
      Metric.isOpen_ball.uniqueDiffOn hxR (n := m) (by simp)
    simp_rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hxR] at hp
    apply hp.trans
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          cNorm (Metric.closedBall 0 r) m χ * cNorm (Metric.closedBall 0 r) m q := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall 0 r)
              (hχ.of_le (by simp)) hxr hi') (Nat.cast_nonneg _)
        · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall 0 r)
            hqa hxr (Nat.sub_le m i)
        · exact norm_nonneg _
        · exact mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg _ _ _)
      _ = (∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * cNorm (Metric.closedBall 0 r) m χ) *
            cNorm (Metric.closedBall 0 r) m q := (Finset.sum_mul ..).symm
      _ ≤ cutoffDerivativeBound χ r m * cNorm (Metric.closedBall 0 r) m q := by
        apply mul_le_mul_of_nonneg_right _ (cNorm_nonneg _ _ _)
        unfold cutoffDerivativeBound
        linarith
  · have hz : iteratedFDeriv ℝ m (cutReducedCoefficients χ q) x = 0 := by
      by_contra h
      exact hx (tsupport_cutReducedCoefficients_subset χ q
        (tsupport_iteratedFDeriv_subset m (subset_tsupport _ h)))
    rw [hz, norm_zero]
    exact mul_nonneg (cutoffDerivativeBound_pos χ r m).le (cNorm_nonneg _ _ _)

/-- Taking an entry loses no derivative norm in the finite supremum norm.
This is the scalar projection used by `app:ch_background:eq:bg-frame-tame`. -/
theorem norm_iteratedFDeriv_coefficient_le
    {p : Euclidean n → ReducedCoefficientIndex n → ℝ} (hp : ContDiff ℝ ∞ p)
    (j : ReducedCoefficientIndex n) (m : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ m (fun y ↦ p y j) x‖ ≤ ‖iteratedFDeriv ℝ m p x‖ := by
  let L : (ReducedCoefficientIndex n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun v ↦ by simpa [L] using norm_le_pi_norm v j)
  exact (L.norm_iteratedFDeriv_comp_left hp.contDiffAt (by simp)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (norm_nonneg _))

end JanetCartan.ContinuumRow.ImageGeometry.Periodization
