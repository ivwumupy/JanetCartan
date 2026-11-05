module

public import JanetCartan.Iteration.PhysicalSeed.OriginalBoundary
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.RawCap

/-!
# One raw cap on the strengthened original candidate geometry

For `app:ch_background:prop:bg-adjoint` and `new:sec:order-of-choices`, apply the
actual supplied-geometry raw-cap producer to `PhysicalSeed`'s own retained T
and density-product cells.  The minimum with arbitrary positive user extras is
formed once BEFORE incidence selection.  Both the source and current inverse
must consume this identical callback.  User extras may already include the
phase/scalar χstar buffers and positive-density caps; their bounds are retained.
No weak cached selected row is compared with the strengthened one.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalNormalInverse
open PhysicalSeed ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic
open FullPhaseCharts.ActualComparison ContinuumAdjoint.Canonical.PhaseExtension

/-- The exact positive-extra callback type of the single strengthened original
incidence selector, before any selected cell or source contraction. -/
abbrev StrongExtraCaps {n : ℕ} (hn : 5 ≤ n) :=
  (p : IncidenceCenter (OriginalBoundary.D hn)) →
    (l : Fin ((OriginalBoundary.D hn).patchCount p.1.1)) →
      ↥(OriginalBoundary.centers hn ⟨p.1.1, l⟩) → {ε : ℝ // 0 < ε}

/-- The actual raw-cap producer on the strengthened initializer's own retained
cells.  This cap precedes all quotient, finite-margin and user-cap inputs. -/
def strongIncidenceRawCap {n : ℕ} (hn : 5 ≤ n) : StrongExtraCaps hn := by
  let D := OriginalBoundary.D hn
  let Tm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) ↦
    OriginalBoundary.T hn ⟨b, l⟩
  let Im := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) ↦
    ↥(OriginalBoundary.centers hn ⟨b, l⟩)
  let Kin := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
    closedBall ((0 : Euclidean (n - 1)), j.1.1) (OriginalBoundary.L hn ⟨b, l⟩ j / 8)
  let Jfull := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
    closedBall ((0 : Euclidean n), (j.1.1, (Tm b l).reference.spatialPatch j.1.1))
      (OriginalBoundary.σcover hn ⟨b, l⟩ j)
  let E := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
    ball (0 : Euclidean n) (OriginalBoundary.Rproduct hn ⟨b, l⟩ j) ×ˢ
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨b, l⟩ j)
  have hball (b : Fin D.chartCount) (l : Fin (D.patchCount b)) :
      closedBall (0 : Euclidean n) (Tm b l).data.localReference.stateRadius ⊆
        closedBall 0 (OriginalBoundary.b hn) :=
    (frameBall_subset_of_stateDomain (OriginalBoundary.T hn ⟨b, l⟩).data.localReference
      (OriginalBoundary.stateDomain_subset_ball hn ⟨b, l⟩)).trans ball_subset_closedBall
  have hgraph (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) :
      MapsTo (LeadingPrimitive.carrierGraph (Tm b l)) (E b l j) (Jfull b l j) :=
    (((OriginalBoundary.carrier_cells hn ⟨b, l⟩ j).2.2.1).mono_left
      (OriginalBoundary.density_product_geometry hn ⟨b, l⟩ j).2.2.2.2.2.2.1).mono_right
        ball_subset_closedBall
  exact InitializedAnalyticData.retainedIncidenceCurrentRawCap (by omega : 0 < n)
    (OriginalBoundary.hD hn) Tm Im (isCompact_closedBall _ _)
    (closedBall_subset_ball (OriginalBoundary.b_lt_R hn)) hball Kin Jfull
    (fun _ _ _ ↦ isCompact_closedBall _ _) E
    (fun _ _ _ ↦ isOpen_ball.prod isOpen_ball) hgraph

/-- The ONE callback supplied to both actual strong source and current inverse.
Arbitrary earlier phase/scalar/positive extras remain in `userExtra`. -/
def strongCappedExtra {n : ℕ} (hn : 5 ≤ n) (userExtra : StrongExtraCaps hn) :
    StrongExtraCaps hn := fun p l j ↦
  ⟨min (userExtra p l j).val (strongIncidenceRawCap hn p l j).val,
    lt_min (userExtra p l j).property (strongIncidenceRawCap hn p l j).property⟩

/-- Positivity survives the single common pre-selection minimum. -/
theorem h_cappedExtra_pos {n : ℕ} (hn : 5 ≤ n) (userExtra : StrongExtraCaps hn)
    (p : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount p.1.1))
    (j : ↥(OriginalBoundary.centers hn ⟨p.1.1, l⟩)) :
    0 < (strongCappedExtra hn userExtra p l j).val :=
  (strongCappedExtra hn userExtra p l j).property

/-- Every early user buffer, including the χstar inner radius, is retained. -/
theorem h_cappedExtra_le_userExtra {n : ℕ} (hn : 5 ≤ n) (userExtra : StrongExtraCaps hn)
    (p : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount p.1.1))
    (j : ↥(OriginalBoundary.centers hn ⟨p.1.1, l⟩)) :
    (strongCappedExtra hn userExtra p l j).val ≤ (userExtra p l j).val :=
  min_le_left _ _

/-- The same callback satisfies the actual strengthened raw-cap constraint. -/
theorem h_cappedExtra_le_rawCap {n : ℕ} (hn : 5 ≤ n) (userExtra : StrongExtraCaps hn)
    (p : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount p.1.1))
    (j : ↥(OriginalBoundary.centers hn ⟨p.1.1, l⟩)) :
    (strongCappedExtra hn userExtra p l j).val ≤ (strongIncidenceRawCap hn p l j).val :=
  min_le_right _ _

/-- Earlier positive refinements associate with the raw cap without another
selector call or another chosen tuple. -/
theorem strongCappedExtra_min_assoc {n : ℕ} (hn : 5 ≤ n)
    (first second : StrongExtraCaps hn)
    (p : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount p.1.1))
    (j : ↥(OriginalBoundary.centers hn ⟨p.1.1, l⟩)) :
    (strongCappedExtra hn (fun p l j ↦
      ⟨min (first p l j).val (second p l j).val,
        lt_min (first p l j).property (second p l j).property⟩) p l j).val =
      min (first p l j).val (strongCappedExtra hn second p l j).val :=
  min_assoc _ _ _

end JanetCartan.PhysicalNormalInverse
