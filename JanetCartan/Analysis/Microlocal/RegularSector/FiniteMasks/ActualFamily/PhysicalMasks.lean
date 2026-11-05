module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.Selection

/-!
# Common original physical masks

After the finite selection supplies a ball contained in every chart's actual
physical neighborhood, construct the original source and output masks in that
ball. This precedes any additional retarded-domain localization masks.
Consumer: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open Characteristic CompatibleResponse
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Construct both original physical masks in the common selected ball. The
output mask has a plateau on the measurement ball; the source mask is one
on the full closed output support. These masks are constructed here, before
`RetardedLocalization.exists_finite_retarded_domain_masks` is used.
Source: `app:ch_regular_base:thm:sector`, `energy-complete-residual`. -/
theorem exists_common_physical_masks (x : E) {R : ℝ} (hR : 0 < R) :
    ∃ (input output : E → ℝ),
      ContDiff ℝ ∞ input ∧ ContDiff ℝ ∞ output ∧
      (∀ y, input y ∈ Icc (0 : ℝ) 1) ∧
      (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport input ∧ HasCompactSupport output ∧
      tsupport input ⊆ ball x (3 * R) ∧
      tsupport output ⊆ ball x (2 * R) ∧
      closedBall x R ⊆ interior {y | output y = 1} ∧
      closedBall x (2 * R) ⊆ interior {y | input y = 1} ∧
      tsupport output ⊆ interior {y | input y = 1} := by
  obtain ⟨input, hi, hir, hic, his, hip⟩ := exists_compact_family_cutoff
    (isCompact_closedBall x (2 * R)) isOpen_ball
    (closedBall_subset_ball (by linarith : 2 * R < 3 * R))
  obtain ⟨output, ho, hor, hoc, hos, hop⟩ := exists_compact_family_cutoff
    (isCompact_closedBall x R) isOpen_ball
    (closedBall_subset_ball (by linarith : R < 2 * R))
  exact ⟨input, output, hi, ho, hir, hor, hic, hoc, his, hos, hop, hip,
    hos.trans (ball_subset_closedBall.trans hip)⟩

/-- Both original physical supports lie in every selected chart, so the
actual source and time plateaux apply on their FULL closed supports.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem physical_mask_supports_in_chart
    {Ω : Set (Euclidean (d + 1))} {x ξ : Euclidean (d + 1)} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)}
    (c : LocalChart Ω x RQ A₀ ξ M) {R : ℝ} (hR : 0 < R)
    (hball : closedBall x (4 * R) ⊆ c.physicalNeighborhood)
    {input output : E → ℝ}
    (hin : tsupport input ⊆ ball x (3 * R))
    (hout : tsupport output ⊆ ball x (2 * R)) :
    tsupport input ∪ tsupport output ⊆ c.physicalNeighborhood := by
  apply union_subset
  · exact hin.trans ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith))).trans hball)
  · exact hout.trans ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith))).trans hball)

end JanetCartan.RegularSector.FiniteMasks.ActualFamily
