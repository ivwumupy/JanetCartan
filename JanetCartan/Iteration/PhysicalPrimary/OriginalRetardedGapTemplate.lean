module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Restrict the checked original signed cutoff to its actual full current and
reuse that current's already constructed graph momentum estimate. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRetardedGapTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

elab "retain_actual_original_source_gap" : command => liftTermElabM do
  let cur := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
  let inc := `JanetCartan.PhysicalPrimary.OriginalIncidence
  let graph := `JanetCartan.PhysicalInitialization.OriginalRegular.Graph
  let ns := `JanetCartan.PhysicalPrimary.OriginalRetardedGap
  let some body := (← getConstInfo (cur ++ `frame_margin)).value? (allowOpaque := true)
    | throwError "actual source gap: native graph/frame proof is not exposed"
  forallBoundedTelescope (← getConstInfo (cur ++ `sourceFrame)).type (some 38) fun x _ => do
    unless x.size == 38 do throwError "actual source gap: changed common-margin current38"
    let fixed := x[:23].toArray
    let margin := mkAppN (mkConst (cur ++ `frame_margin)) x
    let native := body.beta x
    unless native.isAppOfArity (graph ++ `current_frame_margin) 40 do
      throwError "actual source gap: expected SAME direct native graph/frame application"
    let ga := native.getAppArgs
    let frame := mkAppN (mkConst (cur ++ `sourceFrame)) x
    forallBoundedTelescope (← inferType frame) (some 1) fun patch _ => do
      let a := patch[0]!
      let Q := mkApp frame a
      let sectors := mkAppN (mkConst (cur ++ `fact3)) x
      forallBoundedTelescope (← inferType sectors) (some 1) fun center _ => do
        let p := center[0]!
        let mp := x.push p
        let momentum := mkAppN (mkConst (graph ++ `momentum)) (ga.push p)
        discard <| store (ns ++ `momentum) mp momentum
        discard <| store (ns ++ `original_momentum) mp
          (mkAppN (mkConst (graph ++ `original_momentum)) (ga.push p))
        withLocalDeclD `negative (mkConst ``Bool) fun negative => do
          let args := fixed ++ #[p,negative,a]
          let pars := x ++ #[p,negative,a]
          let small := mkAppN (mkConst (inc ++ `Common.fact1)) args
          let full := mkApp (mkAppN (mkConst (inc ++ `continuation)) args) Q
          let .forallE _ needed _ _ ← whnf (← inferType full)
            | throwError "actual source gap: lost original coefficient-tolerance input"
          let norm := needed.appFn!.appArg!
          let na := norm.getAppArgs
          unless norm.isAppOf `JanetCartan.cNorm && na.size ≥ 3 do
            throwError "actual source gap: original coefficient norm changed"
          let low ← mkAppM `lt_of_lt_of_le
            #[mkApp margin na[na.size-3]!, .proj ``And 0 small]
          discard <| store (ns ++ `source_gap) pars (mkApp full low)
          discard <| store (ns ++ `twice_common_le_gap) pars (.proj ``And 1 small)
  logInfo "actual original signed source gap and SAME full-interval graph momentum at ONE common margin, with unchanged source phase/current/selected multiplier"

end JanetCartan.PhysicalPrimary.OriginalRetardedGapTemplate
