module

public import JanetCartan.Iteration.RevisedUniform.OriginalSmoothing
public import JanetCartan.Iteration.RevisedUniform.OriginalTarget
public import JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# A common final defect core for the same native data

The two independent native selectors do not assert that the inverse half-core
lies in the positive-normal exterior plateau. Take their literal minimum once,
before the source contraction/history, without changing either selector.

Only the SOURCE-SMOOTHING core is restricted. Its chart is unchanged; the real
physical P/V/S fields still use the original `OriginalSmoothing.Dsmooth` and
therefore agree with their uncut fields on this smaller final core as well.
The actual smoother below assumes the defect bound on THIS core, not on the
larger inverse core. This is an original-data geometry/smoothing producer, not
`UniformHistoryCorrection` or the unconditional Main
(`main:lem:smoothing`, `app:ch_background:eq:bg-current-identity`, `main:thm:step`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
open Set Metric Filter
open scoped Topology

namespace JanetCartan.RevisedUniform.OriginalFinalCore

/-- Keep the actual inverse chart and restrict only the smoothing/defect core
to the existing exterior half-plateau. No bump, inverse or sample is reselected. -/
def commonSmoothingDomain (D : LocalDomain) (ri : ℝ) (hi : 0 < ri) : LocalDomain where
  coreRadius := min D.coreRadius (ri / 2)
  chartRadius := D.chartRadius
  coreRadius_pos := lt_min D.coreRadius_pos (half_pos hi)
  coreRadius_lt_chartRadius := (min_le_left _ _).trans_lt D.coreRadius_lt_chartRadius
  chartRadius_lt_half := D.chartRadius_lt_half

/-- Both original plateaus contain the same fixed compact final core, with a
neighborhood of the origin. Its source-smoothing chart is literally unchanged. -/
theorem commonSmoothingDomain_spec (n : ℕ) (D : LocalDomain) (ri : ℝ) (hi : 0 < ri) :
    let C := commonSmoothingDomain D ri hi
    0 < C.coreRadius ∧
      IsCompact (C.core n) ∧
      (C.core n).Nonempty ∧
      (0 : Euclidean n) ∈ interior (C.core n) ∧
      (interior (C.core n)).Nonempty ∧
      C.core n ⊆ D.core n ∧
      C.core n ⊆ closedBall (0 : Euclidean n) (ri / 2) ∧
      C.chart n = D.chart n := by
  intro C
  have hpos : 0 < C.coreRadius := C.coreRadius_pos
  have hzero : (0 : Euclidean n) ∈ interior (C.core n) :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (ball_mem_nhds (0 : Euclidean n) hpos) ball_subset_closedBall)
  refine ⟨hpos, isCompact_closedBall _ _, ⟨0, mem_closedBall_self hpos.le⟩,
    hzero, ⟨0,hzero⟩, ?_, ?_, rfl⟩
  · exact closedBall_subset_closedBall (min_le_left _ _)
  · exact closedBall_subset_closedBall (min_le_right _ _)

end JanetCartan.RevisedUniform.OriginalFinalCore
end

public meta section
namespace JanetCartan.RevisedUniform.OriginalFinalCoreTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.RevisedUniform.OriginalFinalCore
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def smoothing := `JanetCartan.RevisedUniform.OriginalSmoothing
private def background := `JanetCartan.PhysicalBackground.NativeMeasuredCancellation
private def core := `JanetCartan.RevisedUniform.OriginalCore

private def tail (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => tail (.proj ``And 1 h) k
private def part (h : Expr) (k : Nat) : Expr := .proj ``And 0 (tail h k)

/-- The common core uses the original23 inverse and the SAME once-strong-capped
source21 exterior radius; it has no source contraction or history argument. -/
elab "construct_actual_original_final_core" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `χ₂)).type (some 23) fun xs _ => do
    unless xs.size == 23 do throwError "original final core: expected original23"
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let original := #[n] ++ xs[1:21].toArray
    let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[n,xs[1]!,original[20]!]
    let selected := original.set! 20 cap
    let source (q : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.SourceInverseBoundary ++ q)) selected
    let old := mkAppN (mkConst (smoothing ++ `Dsmooth)) xs
    let common := mkAppN (mkConst (ns ++ `commonSmoothingDomain)) #[old,source `rInner,source `hrInner]
    let Dsource ← store (ns ++ `Dsmoothing) xs common true
    let radius ← store (ns ++ `radius) xs (Expr.proj `JanetCartan.LocalDomain 0 Dsource) true
    let Dexpr := mkAppN (mkConst `JanetCartan.LocalDomain.core) #[Dsource,n]
    let D ← store (ns ++ `D) xs Dexpr true
    let h := mkAppN (mkConst (ns ++ `commonSmoothingDomain_spec))
      #[n,old,source `rInner,source `hrInner]
    let t := (← inferType h).replace fun e =>
      if e == common then some Dsource else none
    let h ← store (ns ++ `spec) xs h false (some t)
    for (label,idx) in [(`radius_pos,0),(`isCompact,1),(`nonempty,2),
        (`zero_mem_interior,3),(`interior_nonempty,4)] do
      discard <| store (ns ++ label) xs (part h idx)
    let oldCore := mkAppN (mkConst (core ++ `D)) xs
    let bgCore := mkAppN (mkConst (background ++ `core)) original
    let eucl := mkApp (mkConst `JanetCartan.Euclidean) n
    let subset (A B : Expr) := mkAppOptM ``Set.Subset #[some eucl,some A,some B]
    let hold ← store (ns ++ `subset_inverse_core) xs (part h 5) false
      (some (← subset D oldCore))
    discard <| store (ns ++ `subset_background_core) xs (part h 6) false
      (some (← subset D bgCore))
    discard <| store (ns ++ `smoothing_chart_eq) xs (tail h 7)
    let hs := mkAppN (mkConst (core ++ `subset_solver_domain)) xs
    discard <| store (ns ++ `subset_solver_domain) xs (← mkAppM ``Set.Subset.trans #[hold,hs])
    let zero ← mkAppOptM ``OfNat.ofNat #[eucl,mkNatLit 0,none]
    let ball ← mkAppM ``Metric.closedBall #[zero,radius]
    discard <| store (ns ++ `D_eq_closedBall) xs (← mkEqRefl D) false
      (some (← mkEq D ball))
  logInfo "actual final common core: original23, both native plateaus, positive interior, unchanged inverse chart and no selector changes"

/-- Apply the existing physical smoother to the genuine common defect core and
same original25 reference. No smallness on the larger inverse core is assumed. -/
elab "apply_physical_smoothing_to_original_final_core" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `Gref)).type (some 25) fun xs _ => do
    unless xs.size == 25 do throwError "original final smoothing: expected original25"
    let fixed := xs[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let G := mkAppN (mkConst (regular ++ `Gref)) xs
    let Dsource := mkAppN (mkConst (ns ++ `Dsmoothing)) fixed
    let h := mkAppN (mkConst `JanetCartan.PhysicalSmoothing.exists_original_target_history_smoothing)
      #[n,Dsource,G,xs[23]!,Expr.proj ``And 0 xs[24]!]
    let coreExpr := mkAppN (mkConst `JanetCartan.LocalDomain.core) #[Dsource,n]
    let actualCore := mkAppN (mkConst (ns ++ `D)) fixed
    let t := (← inferType h).replace fun e => if e == coreExpr then some actualCore else none
    discard <| store (ns ++ `source_interval) xs h false (some t)
    let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
    let Gmap ← mkAppM `JanetCartan.FlatReference.map #[G]
    withLocalDeclD `j (mkConst ``Nat) fun j => do
      let normalized := mkAppN (mkConst `JanetCartan.PhysicalSmoothing.normalizedSource_eq)
        #[n,N,j,Dsource]
      forallBoundedTelescope (← inferType normalized) (some 4) fun data _ => do
        discard <| store (ns ++ `normalization) (xs ++ #[j] ++ data)
          (mkAppN normalized (data ++ #[Gmap]))
    let smaller := mkAppN (mkConst (ns ++ `subset_inverse_core)) fixed
    let targetNS := `JanetCartan.RevisedUniform.OriginalTarget
    let hchart := mkAppN (mkConst (targetNS ++ `D_subset_chart)) xs
    discard <| store (ns ++ `D_subset_chart) xs (← mkAppM ``Set.Subset.trans #[smaller,hchart])
    let hclosure := mkAppN (mkConst (targetNS ++ `D_subset_closureChart)) xs
    let hsub ← store (ns ++ `D_subset_closureChart) xs
      (← mkAppM ``Set.Subset.trans #[smaller,hclosure])
    let radius := mkAppN (mkConst (ns ++ `radius)) fixed
    let positive := mkAppN (mkConst (ns ++ `radius_pos)) fixed
    let target := mkAppN (mkConst (targetNS ++ `exists_normalized_revised_step_reduction_on_subcore))
      #[n,G,radius,positive,hsub,xs[23]!,Expr.proj ``And 0 xs[24]!]
    let targetType := (← inferType target).replace fun e => match e with
      | .app _ r => if e.isAppOf `Metric.closedBall && r == radius then some actualCore else none
      | _ => none
    discard <| store (ns ++ `target_reduction) xs target false (some targetType)
  logInfo "actual common-core smoothing/normalization/target: same original reference, final-D defect premise, fixed source support and all revised source profiles; actual uniform correction still required"

end JanetCartan.RevisedUniform.OriginalFinalCoreTemplate
end

construct_actual_original_final_core
apply_physical_smoothing_to_original_final_core
