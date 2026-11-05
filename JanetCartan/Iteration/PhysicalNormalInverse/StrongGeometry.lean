module

public import JanetCartan.Iteration.PhysicalNormalInverse.StrongSource
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongRawCap
public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongGeometryApplication

/-!
# Fixed working geometry on the one strengthened initializer

For `app:ch_background:prop:bg-inverse`, the doubled full working balls must
lie in the original physical ball and phase domain before the final source
scale is chosen.  The same strengthened contraction continuation at one EMPTY
legacy history proves only these history-independent containments.  No legacy
history conclusion is applied to a physical Schwartz prefix, no periodic
increment is introduced, and no source/current operator or row is reselected.
The actual current fields still come from the retained generic callback.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

cache_strong_empty_geometry_inputs
project_strong_current_conic_geometry

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalNormalInverse.StrongGeometry
open PhysicalSeed ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport ActualFlow LeadingWave.FullModulation

/-- The literal full working balls of the strengthened selected family have
the required fixed physical/phase inclusions.  The witness used to prove the
inclusions is an empty history only; its map or leading fields are not reused
as a nonempty physical history or a current inverse. -/
theorem working_geometry {n : ℕ} (hn : 5 ≤ n)
    (εframe : ℝ) (hεframe : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n))
    (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
    (k : ((j : Fin (OriginalBoundary.D hn).chartCount) ×
      Fin ((OriginalBoundary.D hn).patchCount j)) → Euclidean n)
    (hk : ∀ i, k i ≠ 0) (hkD : ∀ i, k i ∈ (OriginalBoundary.D hn).domain i.1)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmargin : ∀ j ∈ orders, 0 < margin j)
    (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) :
    (∀ i (j : ↥(OriginalBoundary.centers hn i)),
      closedBall (0 : Euclidean n) (2 * OriginalBoundary.σcover hn i j) ⊆
        closedBall 0 (OriginalBoundary.b hn)) ∧
    (∀ i (j : ↥(OriginalBoundary.centers hn i)),
      closedBall ((0 : Euclidean n), (j.1.1, (OriginalBoundary.T hn i).reference.spatialPatch j.1.1))
        (2 * OriginalBoundary.σcover hn i j) ⊆ domain (OriginalBoundary.T hn i)) := by
  let kTest := (exists_nat_gt
    (displacementLoss n + bandExponent * ((14 : ℝ) + (n : ℝ) / 2) + 2)).choose
  have hkTest := (exists_nat_gt
    (displacementLoss n + bandExponent * ((14 : ℝ) + (n : ℝ) / 2) + 2)).choose_spec
  let S := EmptyLeading.S hn εframe hεframe qext hqcenter hqradius k hk hkD
    p orders margin extendedMargin hmargin hextendedMargin cap hcap
    1 zero_lt_one le_rfl 14 0 kTest le_rfl (by norm_num) hkTest 1 1 zero_le_one zero_lt_one
  have hbase := EmptyAdmitted.continuation hn εframe hεframe qext hqcenter hqradius k hk hkD
    p orders margin extendedMargin hmargin hextendedMargin cap hcap
    1 zero_lt_one le_rfl 14 0 kTest le_rfl (by norm_num) hkTest 1 1 zero_le_one zero_lt_one
    S le_rfl 0 (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
    (isAdmissibleHistory_empty S kTest _ _)
  have hworkingPhase i (j : ↥(OriginalBoundary.centers hn i)) :
      closedBall ((0 : Euclidean n), (j.1.1, (OriginalBoundary.T hn i).reference.spatialPatch j.1.1))
        (2 * OriginalBoundary.σcover hn i j) ⊆ domain (OriginalBoundary.T hn i) :=
    ((OriginalBoundary.comparison_cover hn i j).2.1.trans (closedBall_subset_closedBall
      (by have := (OriginalBoundary.comparison_pos hn i j).1; linarith))).trans (hbase i j).1
  have hworkingK i (j : ↥(OriginalBoundary.centers hn i)) :
      closedBall (0 : Euclidean n) (2 * OriginalBoundary.σcover hn i j) ⊆
        closedBall 0 (OriginalBoundary.b hn) := by
    intro x hx
    have hp : (x, (j.1.1, (OriginalBoundary.T hn i).reference.spatialPatch j.1.1)) ∈
        closedBall ((0 : Euclidean n), (j.1.1, (OriginalBoundary.T hn i).reference.spatialPatch j.1.1))
          (2 * OriginalBoundary.σcover hn i j) := by
      rw [← closedBall_prod_same]
      exact ⟨hx, mem_closedBall_self (by
        have := (OriginalBoundary.comparison_pos hn i j).2.2.2.2.2.2.2.2
        positivity)⟩
    exact interior_subset ((hbase i j).2.1
      ((OriginalBoundary.comparison_cover hn i j).2.1.trans (closedBall_subset_closedBall
        (by have := (OriginalBoundary.comparison_pos hn i j).1; linarith)) hp)).2.2
  exact ⟨hworkingK, hworkingPhase⟩

end JanetCartan.PhysicalNormalInverse.StrongGeometry
