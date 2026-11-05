module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Apply the actual original native output support to the SAME full response.
The output support is inherited; no output cutoff is multiplied into B. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalFullResponseCompactTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalFullResponseCompact
private def response := `JanetCartan.PhysicalPrimary.OriginalFullResponse
private def solver := `JanetCartan.PhysicalPrimary.OriginalUncutSolver
private def support := `JanetCartan.PhysicalPrimary.OriginalSolverSupport
private def ambient := `JanetCartan.PhysicalPrimary.OriginalAmbientResponse
private def native := `JanetCartan.PhysicalInitialization.OriginalRegular.Current

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | j+1 => part (.proj ``And 1 e) j

private def proveBy (target proof : Expr) : MetaM Expr := do
  let goal ← mkFreshExprMVar target
  let goals ← goal.mvarId!.apply proof
  unless goals.isEmpty do throwError "actual compact response: native support proof left goals"
  instantiateMVars goal

private def retain (name : Name) (params : Array Expr) (value : Expr)
    (type : Option Expr := none) : MetaM Expr := do
  let target := ns ++ name
  let result ← store target params value false type
  addDocStringCore target "The SAME globally uncut original response inherits the original native compact output support. Global smoothness follows from the already constructed current geometry near that support; no response bound or additional output cutoff is assumed (main:prop:current-waves; app:ch_response:eq:response-full-map)."
  return result

elab "retain_original_full_response_compact_part " phase:num : command => liftTermElabM do
  let stage := phase.getNat
  let info ← getConstInfo (response ++ `B)
  let some Bbody := info.value? (allowOpaque := true)
    | throwError "actual compact response: missing frozen full response body"
  forallBoundedTelescope info.type (some 38) fun params _ => do
    unless params.size == 38 do throwError "actual compact response: expected exact weak current38"
    let fixed := params[:23].toArray
    let stat (name : Name) := mkAppN (mkConst (support ++ name)) fixed
    let current (name : Name) := mkAppN (mkConst (native ++ name)) params
    let hV := mkAppN (mkConst (solver ++ `uncut_solver_smooth)) params
    let hAE := mkAppN (mkConst (solver ++ `uncut_solver_ae)) params
    let hz := mkAppN (mkConst (support ++ `real_half_solver_zero_off_output)) params
    let hK := stat `outputSupport_compact
    let hKclosed ← mkAppM `IsCompact.isClosed #[hK]
    let supported ← if stage == 0 then do
      let proof ← forallBoundedTelescope (← inferType hAE) (some 1) fun source _ => do
        unless source.size == 1 do throwError "actual compact response: native source binder changed"
        let h := source[0]!
        let smooth := mkApp hV h
        let g := (← inferType smooth).appArg!
        let hg ← mkAppM `ContDiff.continuous #[smooth]
        let start ← mkAppM (support ++ `continuous_tsupport_of_ae_zero) #[hKclosed]
        let .forallE _ localL2 _ _ ← whnf (← inferType start)
          | throwError "actual compact response: missing the native ambient L² source"
        let proof := mkApp hAE h
        let rhs := (← inferType proof).getAppArgs.back!
        let rec obtainSource (v : Expr) (fuel : Nat) : MetaM Expr := do
          if ← isDefEq (← inferType v) localL2 then return v
          match fuel, v with
          | k+1, .app _ a => obtainSource a k
          | _, _ => throwError "actual compact response: native L² representative changed"
        let u ← obtainSource rhs 6
        let n := mkApp (mkConst ``Nat.succ) params[0]!
        let supported := mkAppN (mkConst (support ++ `continuous_tsupport_of_ae_zero))
          #[n,stat `outputSupport,hKclosed,u,g,hg,proof,mkApp hz u.appArg!]
        mkLambdaFVars source supported
      retain `uncut_solver_support params proof
    else pure <| mkAppN (mkConst (ns ++ `uncut_solver_support)) params
    logInfo "native compact: checked all original uncut solver supports"
    let rawB := Bbody.beta params
    unless rawB.isAppOfArity (ambient ++ `uncutAmbientExtension) 14 do
      throwError "actual compact response: the frozen globally uncut response changed"
    let data := rawB.getAppArgs
    let args := #[data[2]!,data[3]!,data[4]!,data[8]!,data[9]!,data[10]!,data[11]!,data[12]!,data[13]!]
    let B := mkAppN (mkConst (response ++ `B)) params
    let rename (type : Expr) := type.replace fun e => if e == rawB then some B else none
    let hS := stat `χ₂_support_output
    if stage == 0 then
      let hsupport ← mkAppM (ambient ++ `uncutAmbientExtension_tsupport_subset)
        (args ++ #[hS,supported])
      discard <| retain `support params hsupport (some (rename (← inferType hsupport)))
      logInfo "native compact: checked global original full response support"
      return
    unless stage == 1 do throwError "unknown compact response part"
    let geometry := .proj ``Subtype 1 (current `projected)
    let hF := part geometry 0
    let Ω := (← inferType hF).appArg!
    let hΩ ← proveBy (← mkAppM `IsOpen #[Ω]) (← mkConstWithFreshMVarLevels `Metric.isOpen_ball)
    let all := mkAppN (mkConst (ambient ++ `uncutAmbientExtension_compact_smooth))
      (data ++ #[stat `outputSupport,Ω,hK,hS,stat `outputSupport_in_wide_geometry,hΩ,hF,
        part geometry 1,part geometry 2,supported])
    let all ← retain `compact_smooth params all (some (rename (← inferType all)))
    for label in [`smooth,`compact_support] do
      let proof ← forallBoundedTelescope (← inferType all) (some 1) fun source _ => do
        mkLambdaFVars source (.proj ``And (if label == `smooth then 0 else 1) (mkAppN all source))
      discard <| retain label params proof
    let schwartz ← mkAppM (ns ++ `compactResponseSchwartz) #[B,all]
    let actualSchwartz ← store (ns ++ `schwartz) params schwartz true
    let identity ← mkAppM (ns ++ `compactResponseSchwartz_apply) #[B,all]
    let identityType := (← inferType identity).replace fun e => if e == schwartz then some actualSchwartz else none
    discard <| retain `schwartz_apply params identity (some identityType)
    logInfo "actual original38 full B is globally smooth and compactly supported in the ORIGINAL native output, on every original chi2 tensor source; exact Schwartz packaging with no new output mask or Cresp premise"

end JanetCartan.PhysicalPrimary.OriginalFullResponseCompactTemplate
