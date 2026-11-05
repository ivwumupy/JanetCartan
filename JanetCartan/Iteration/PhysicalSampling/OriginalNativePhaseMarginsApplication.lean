module

public meta import Lean

/-!
# The actual graph margins on the literal native source map

Normalize only the reference-map projection in the existing current-margin
conclusions. The original graph parameters, source range, reached threshold
and Schwartz history remain unchanged. The result can be joined with the
native31 current because that current uses the SAME literal source dilation;
no native31-only phase-smallness statement is asserted
(`app:ch_seed:setup:seed-current`, `new:sec:order-of-choices`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalNativePhaseMarginsApplication
open Lean Meta Elab Command

elab "cache_original_native_phase_margin " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  let index := which.getNat
  let sources : Array Name := #[`raw_frame_margin, `all_four_phase_margins]
  let targets : Array Name := #[`raw_frame_margin_native, `all_four_phase_margins_native]
  let arities : Array Nat := #[42, 43]
  unless index < sources.size do throwError "native phase margin: invalid field"
  let ns := `JanetCartan.PhysicalSampling.OriginalPhaseMargins
  let source := ns ++ sources[index]!
  let target := ns ++ targets[index]!
  forallBoundedTelescope (← getConstInfo source).type (some arities[index]!) fun params type => do
    unless params.size == arities[index]! do throwError "native phase margin: original prefix changed"
    let referenceName := `JanetCartan.PhysicalInitialization.OriginalRegular.Gref
    let some reference := type.find? (·.isAppOfArity referenceName 25)
      | throwError "native phase margin: SAME original Gref missing"
    let some body := (← getConstInfo referenceName).value? (allowOpaque := true)
      | throwError "native phase margin: actual Gref definition unavailable"
    let sourceReference := body.beta reference.getAppArgs
    unless sourceReference.isAppOfArity `JanetCartan.sourceDilationReference 5 do
      throwError "native phase margin: Gref is not the literal original source dilation"
    let mapEquality := mkAppN (mkConst `JanetCartan.sourceDilationReference_map)
      sourceReference.getAppArgs
    let nativeMap := (← inferType mapEquality).getAppArgs[2]!
    let some oldMap := type.find? (fun e =>
        e.isAppOfArity `JanetCartan.FlatReference.map 2 && e.appArg! == reference)
      | throwError "native phase margin: original current map projection missing"
    let nativeType := type.replace fun e => if e == oldMap then some nativeMap else none
    unless nativeType != type do throwError "native phase margin: map replacement did not occur"
    let type ← mkForallFVars params (← instantiateMVars nativeType)
    let value ← mkLambdaFVars params (mkAppN (mkConst source) params)
    if type.hasMVar || value.hasMVar || type.hasSorry || value.hasSorry ||
        type.hasFVar || value.hasFVar then
      throwError "native phase margin: open or recovered actual declaration"
    addDecl (.thmDecl {name := target, levelParams := [], type, value}) (forceExpose := true)
    logInfo m!"checked SAME actual graph/history margin on literal native source map {target}"

end JanetCartan.PhysicalSampling.OriginalNativePhaseMarginsApplication
