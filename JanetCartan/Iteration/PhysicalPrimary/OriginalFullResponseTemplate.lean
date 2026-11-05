module

public import Mathlib.Data.Set.Basic
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Same-history specialization of the actual globally uncut vector solver to
the tensor response. No new inverse, source cutoff, output cutoff or analytic
response estimate enters this construction. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalFullResponseTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalFullResponse
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def native := reg ++ `Current
private def full := `JanetCartan.PhysicalPrimary.OriginalUncutSolver
private def ambient := `JanetCartan.PhysicalPrimary.OriginalAmbientResponse
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | j+1 => part (.proj ``And 1 e) j

private def applyClosed (target : Expr) (name : Name) : MetaM Expr := do
  let goal ← mkFreshExprMVar target
  let goals ← goal.mvarId!.apply (← mkConstWithFreshMVarLevels name)
  unless goals.isEmpty do throwError "actual uncut response: {name} left primitive goals"
  instantiateMVars goal

private def retain (name : Name) (params : Array Expr) (value : Expr)
    (isDef := false) (type : Option Expr := none) : MetaM Expr := do
  let target := ns ++ name
  let result ← store target params value isDef type
  addDocStringCore target "The literal original-history globally uncut ambient completion of the same full inverse, with the original chi2 tensor source and chi-src stress multiplier only (app:ch_response:eq:response-full-map). No response norm estimate or additional output cutoff is introduced."
  return result

elab "construct_original_full_ambient_response" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (full ++ `uncut_solver)).type (some 38) fun params _ => do
    unless params.size == 38 do throwError "actual uncut response: expected the exact original38 solver"
    let fixed := params[:23].toArray
    let current (name : Name) := mkAppN (mkConst (native ++ name)) params
    let mask (name : Name) := mkAppN (mkConst (masks ++ name)) fixed
    let projected := current `projected
    let F ← retain `F params (.proj ``Subtype 0 projected) true
    let geometry := .proj ``Subtype 1 projected
    let hF := part geometry 0
    let Ω := (← inferType hF).appArg!
    let hΩ ← applyClosed (← mkAppM `IsOpen #[Ω]) `Metric.isOpen_ball
    let Q := current `Q
    let hη := mask `χsrc_smooth
    let η := (← inferType hη).appArg!
    let χ₂ := (← inferType (mask `χ₂_smooth)).appArg!
    let S ← retain `sourceSet params (← mkAppM `tsupport #[χ₂]) true
    let E := (← inferType F).bindingDomain!
    let U := mkApp (mkConst ``Set.univ [.zero]) E
    let hU ← applyClosed (← mkAppM `IsOpen #[U]) `isOpen_univ
    let hSU ← mkAppM `Set.subset_univ #[S]
    let hQ ← mkAppM (ns ++ `components_smooth_univ) #[Q,current `hQ]
    let solver := mkAppN (mkConst (full ++ `uncut_solver)) params
    let hsolver := mkAppN (mkConst (full ++ `uncut_solver_smooth)) params
    let args := #[F,Q,η,hU,hQ,hη,hSU,solver,hsolver]
    let rawB ← mkAppM (ambient ++ `uncutAmbientExtension) args
    let B ← retain `B params rawB true
    let rename (type : Expr) := type.replace fun e => if e == rawB then some B else none
    let apply ← mkAppM (ambient ++ `uncutAmbientExtension_apply) args
    discard <| retain `apply params apply false (some (rename (← inferType apply)))
    let smooth ← mkAppM (ambient ++ `uncutAmbientExtension_contDiffOn)
      (args ++ #[hΩ,hF,part geometry 1,part geometry 2])
    discard <| retain `smoothOn params smooth false (some (rename (← inferType smooth)))
    let strain ← mkAppM (ambient ++ `uncutAmbientExtension_linearizedMetric) args
    discard <| retain `linearized_metric params strain false (some (rename (← inferType strain)))
    logInfo "actual original38 ambient B: SAME full inverse/chi3 source extension, original chi2 tensor source and chi-src; global literal completion identity and actual geometric-chart smoothness, no output recut or response-estimate premise"

end JanetCartan.PhysicalPrimary.OriginalFullResponseTemplate
