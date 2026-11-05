module

public import JanetCartan.Iteration.PhysicalSampling.OriginalGraphResponse
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrent
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
public meta import Lean

/-!
# The measured Mean/Band prefixes use the actual uncut ambient solver

Reach the original graph42 threshold from the native current49 inequality and
feed the original χ₂ and globally uncut full inverse completion to both
already proved retained current continuations. This is not the joint physical
smoothness or derivative bound of that response, which remains an obligation
on the specified response itself (`app:ch_response:eq:response-full-map`,
`app:ch_waves:eq:sampling-operator-bounds`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredFullResponseApplication
open Lean Meta Elab Command

elab "put_original_full_response_in_measured_current " which:num : command => liftTermElabM <| withTransparency .reducible do
  let measured := `JanetCartan.PhysicalSampling.OriginalMeasuredCurrent
  let graph := `JanetCartan.PhysicalSampling.OriginalGraphResponse
  let joined := `JanetCartan.PhysicalNormalInverse.OriginalComparisonCurrent
  let isMean := which.getNat == 0
  unless isMean || which.getNat == 1 do throwError "actual measured full response: invalid factory"
  let fromName := measured ++ (if isMean then `mean_before_response else `band_before_response)
  let toName := measured ++ (if isMean then `mean_on_full_response else `band_on_full_response)
  forallBoundedTelescope (← getConstInfo fromName).type (some 60) fun x _ => do
    unless x.size == 60 do throwError "actual measured full response: expected fixed43, response budget2, history6 and initial-profile9"
    let reached ← mkAppM `le_trans #[mkAppN (mkConst (joined ++ `S_graph)) x[:43].toArray, x[46]!]
    let g := x[:36].toArray ++ #[x[45]!, reached] ++ x[47:51].toArray
    let source := mkAppN (mkConst (graph ++ `χ₂)) x[:24].toArray
    let B := mkAppN (mkConst (graph ++ `B)) g
    let result := mkAppN (mkConst fromName) (x ++ #[source, B])
    let type ← instantiateMVars (← mkForallFVars x (← inferType result))
    let value ← instantiateMVars (← mkLambdaFVars x result)
    if type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar ||
        type.hasFVar || value.hasFVar || type.hasSorry || value.hasSorry then
      throwError "actual measured full response: recovered/open application"
    addDecl (.thmDecl {name := toName, levelParams := [], type, value}) (forceExpose := true)
    logInfo m!"checked exact original source/uncut B in measured continuation {toName}"

end JanetCartan.PhysicalSampling.OriginalMeasuredFullResponseApplication
end

@[expose] public noncomputable section
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

put_original_full_response_in_measured_current 0
put_original_full_response_in_measured_current 1
