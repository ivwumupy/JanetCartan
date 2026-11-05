module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Exact weak-original38 application of the uncut smooth-source realization.
No scalar or response estimate is supplied: all-order regularity comes from
Current.fact13 and the literal native Tplus0 Fourier estimate. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalUncutSolverTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def current := regular ++ `Current
private def ns := `JanetCartan.PhysicalPrimary.OriginalUncutSolver

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | k+1 => part (.proj ``And 1 e) k

private def bodyAt (name : Name) (params : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "uncut original inverse: missing native body {name}"
  return value.beta params

private def retain (name : Name) (params : Array Expr) (value : Expr)
    (isDef := false) (type : Option Expr := none) : MetaM Expr := do
  let full := ns ++ name
  let result ← store full params value isDef type
  addDocStringCore full "The SAME original38 inverse acting on the supplied source without another chi2; existing chi3 only extends the inverse input of the globally uncut paired solver (app:ch_regular:thm:exact-correction; app:ch_response:eq:response-graded-reduced)."
  return result

private def applyClosed (target : Expr) (name : Name) : MetaM Expr := do
  let goal ← mkFreshExprMVar target
  let goals ← goal.mvarId!.apply (← mkConstWithFreshMVarLevels name)
  unless goals.isEmpty do
    throwError "uncut original inverse: {name} left primitive goals"
  instantiateMVars goal

elab "construct_original_uncut_solver" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (current ++ `normalized_solver)).type (some 38) fun params _ => do
    unless params.size == 38 do throwError "uncut original inverse: expected exact weak original38"
    let fixed := params[:23].toArray
    let stat (name : Name) := mkAppN (mkConst (regular ++ name)) fixed
    let cur (name : Name) := mkAppN (mkConst (current ++ name)) params
    let rawR ← bodyAt (current ++ `R) params
    unless rawR.isAppOfArity `JanetCartan.ArbitraryAccuracy.ResidualLocalization.localRealCompression 6 do
      throwError "uncut original inverse: native real residual spine changed"
    let hW := rawR.getAppArgs[3]!
    let W := (← inferType hW).appArg!
    let hOpen ← applyClosed (← mkAppM `IsOpen #[W]) `Metric.isOpen_ball
    let hSource := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₃_support_chart) fixed
    let hSupport ← mkAppM `Set.Subset.trans #[hSource,stat `hUW]
    discard <| retain `source_support params hSupport
    let hInv ← forallBoundedTelescope (← inferType (cur `fact13)) (some 3) fun args _ => do
      unless args.size == 3 do throwError "uncut original inverse: all-order inverse signature changed"
      mkLambdaFVars args (.proj ``And 0 (mkAppN (cur `fact13) args))
    let hInv ← retain `inverse_mem params hInv
    let zero ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 0
    let Tzero := mkApp (cur `Tplus) zero
    let hpositive := part (part (part (cur `fact5) 0) 0) 3
    let orderZero := mkApp hpositive zero
    let half ← forallBoundedTelescope (← inferType orderZero) (some 1) fun orders _ => do
      let use := mkAppN orderZero (orders.push Tzero)
      let .forallE _ needed _ _ ← whnf (← inferType use)
        | throwError "uncut original inverse: missing native solver alternative"
      unless needed.isAppOfArity ``Or 2 do
        throwError "uncut original inverse: solver/adjoint alternatives changed"
      let hleft := mkAppN (mkConst ``Or.inl)
        #[needed.getAppArgs[0]!,needed.getAppArgs[1]!,← mkEqRefl Tzero]
      mkLambdaFVars orders (mkApp use hleft)
    let half ← retain `half_solver_tame params half
    let partialResult ← mkAppM (ns ++ `exists_uncut_solver_realization)
      #[hOpen,stat `χ₃,hSupport,cur `Inv,hInv,Tzero]
    let .forallE _ hTtype _ _ ← whnf (← inferType partialResult)
      | throwError "uncut original inverse: missing graph-test regularity input"
    let hT ← forallTelescope hTtype fun args target => do
      unless args.size == 2 do throwError "uncut original inverse: graph-test inputs changed"
      let u := args[0]!
      let s := args[1]!
      let targetArgs := target.getAppArgs
      let order := targetArgs[targetArgs.size-2]!
      let hmem ← mkAppM `JanetCartan.FourierIntegral.graphTest_memVectorFourierSobolev #[order,u]
      let hu := (← inferType hmem).appArg!
      mkLambdaFVars args (.proj ``And 0 (mkAppN half #[s,hu,hmem]))
    let hT ← retain `half_solver_graph_mem params hT
    let result ← retain `initialized params (mkApp partialResult hT)
    let solver ← retain `uncut_solver params (← mkAppM ``Classical.choose #[result]) true
    let spec ← mkAppM ``Classical.choose_spec #[result]
    let .forallE name domain body _ ← whnf (← inferType spec)
      | throwError "uncut original inverse: expected the single all-source solver specification"
    let rawSolver := (← mkAppM ``Classical.choose #[result])
    let specType := (← inferType spec).replace fun e => if e == rawSolver then some solver else none
    let spec ← retain `uncut_solver_spec params spec false (some specType)
    let smooth ← withLocalDeclD name domain fun h =>
      mkLambdaFVars #[h] (.proj ``And 0 (mkApp spec h))
    discard <| retain `uncut_solver_smooth params smooth
    let ae ← withLocalDeclD name domain fun h =>
      mkLambdaFVars #[h] (.proj ``And 1 (mkApp spec h))
    discard <| retain `uncut_solver_ae params ae
    let _ := body
    logInfo "actual original38 uncut solver: native all-order Inv, existing chi3 source extension, SAME Tplus0 pairing; no duplicate chi2, no output recut, no scalar/response premise"

end JanetCartan.PhysicalPrimary.OriginalUncutSolverTemplate
end
