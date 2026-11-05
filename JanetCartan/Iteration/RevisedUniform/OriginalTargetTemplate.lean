module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Exact same-original target reduction on the native defect core
(`main:prop:seed`). The analytic uniform-step obligation is retained. -/

public meta section
set_option warningAsError true

namespace JanetCartan.RevisedUniform.OriginalTargetTemplate
open Lean Meta Elab Command
open JanetCartan.PhysicalInitialization.OriginalProtectedTemplate

private def src := `JanetCartan.PhysicalInitialization.OriginalRegular
private def coreNS := `JanetCartan.RevisedUniform.OriginalCore
private def ns := `JanetCartan.RevisedUniform.OriginalTarget
private def part (h : Expr) : Nat → Expr
  | 0 => .proj ``And 0 h
  | k+1 => part (.proj ``And 1 h) k

/-- Instantiate the unchanged reference chart inclusion and target reduction
with actual original25 data, retaining the native core and uniform obligation. -/
elab "retain_actual_original_target_reduction" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (src ++ `Gref)).type (some 25) fun xs _ => do
    unless xs.size == 25 do throwError "original target: expected original23 and source interval"
    let fixed := xs[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let hn := xs[1]!
    let original := #[n] ++ xs[1:21].toArray
    let orig (q : Name) := mkAppN (mkConst (src ++ q)) fixed
    let core (q : Name) := mkAppN (mkConst (coreNS ++ q)) fixed
    let boundary (q : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.OriginalBoundary ++ q)) #[n,hn]
    let G := mkAppN (mkConst (src ++ `Gref)) xs
    let U := (← inferType (orig `hUW)).appFn!.appArg!
    let same := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) original[:18].toArray
    let hR ← mkAppM (src ++ `radius_lt_same_chart) #[same,boundary `R_lt_chartRadius]
    let geometry := mkAppN (mkConst (ns ++ `native_core_subset_reference_chart))
      #[n,core `D,U,orig `χ₂,orig `normRadius,boundary `b,boundary `R,G,
        core `subset_solver_domain,part (orig `afterChoice_χ₃) 5,
        orig `hUW,orig `hNormBall,boundary `b_lt_R,hR]
    let geom ← store (ns ++ `reference_domain_geometry) xs geometry
    discard <| store (ns ++ `D_subset_chart) xs (.proj ``And 0 geom)
    let hsub ← store (ns ++ `D_subset_closureChart) xs (.proj ``And 1 geom)
    let target := mkAppN (mkConst (ns ++ `exists_normalized_revised_step_reduction_on_subcore))
      #[n,G,core `radius,core `radius_pos,hsub,xs[23]!, .proj ``And 0 xs[24]!]
    let targetType := (← inferType target).replace fun e ↦ match e with
      | .app _ radius =>
        if e.isAppOf `Metric.closedBall && radius.isAppOf (coreNS ++ `radius) then some (core `D) else none
      | _ => none
    discard <| store (ns ++ `target_reduction) xs target false (some targetType)
  logInfo "actual original25 same-reference target reduction on the original52 D: native PDE/Sobolev domains imply the unchanged Gref chart, and the genuine UniformHistoryCorrection(D) remains explicit"

end JanetCartan.RevisedUniform.OriginalTargetTemplate
end
