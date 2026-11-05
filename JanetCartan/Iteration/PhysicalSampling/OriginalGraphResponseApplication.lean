module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativePhaseMargins
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullResponse
public meta import Lean

/-!
# The original full uncut response on the measured sampling graph

The phase graph's original source interval and reached threshold imply the
regular weak-current scale and reached threshold of the actual full solver.
Use those implications, not a separate source/history selection. The output
is the existing task13 full inverse completion, with its existing tensor χ₂;
this does not supply its uniform derivative estimates
(`app:ch_response:eq:response-full-map`, `app:ch_waves:eq:sampling-operator-bounds`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalGraphResponseApplication
open Lean Meta Elab Command

private def dest := `JanetCartan.PhysicalSampling.OriginalGraphResponse
private def graph := `JanetCartan.PhysicalInitialization.OriginalRegular.Graph
private def full := `JanetCartan.PhysicalPrimary.OriginalFullResponse
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks

private def save (field : Name) (xs : Array Expr) (proof : Expr) (data := false)
    (result : Option Expr := none) : MetaM Unit := do
  let n := dest ++ field
  let t ← match result with
    | some e => pure e
    | none => inferType proof
  let t ← instantiateMVars (← mkForallFVars xs t)
  let v ← instantiateMVars (← mkLambdaFVars xs proof)
  if t.hasMVar || v.hasMVar || t.hasLevelMVar || v.hasLevelMVar || t.hasFVar || v.hasFVar ||
      t.hasSorry || v.hasSorry then throwError "original graph response: incomplete {field}"
  if data then
    addDecl (.defnDecl {name := n, levelParams := [], type := t, value := v, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name := n, levelParams := [], type := t, value := v}) (forceExpose := true)
  logInfo m!"checked original uncut full response on the SAME measured graph: {field} at {xs.size} inputs"

/-- The regular interval, original order data, and regular reached threshold
are obtained from the exact sampling graph. All four history arguments are
verbatim copies, and the finite map is definitionally the same native map. -/
elab "retain_original_measured_graph_response " which:num : command => liftTermElabM <| withTransparency .reducible do
  let margin := `JanetCartan.PhysicalSampling.OriginalPhaseMargins.raw_frame_margin_native
  forallBoundedTelescope (← getConstInfo margin).type (some 42) fun x tail => do
    let reached ← inferType x[37]!
    unless reached.isAppOfArity ``LE.le 4 do throwError "graph response: missing actual reached threshold"
    let S := reached.getAppArgs[2]!
    unless S.isAppOfArity (graph ++ `S) 34 do throwError "graph response: original graph34 not retained"
    let g := S.getAppArgs
    let source := g[:23].toArray
    let regularScale := mkAppN (mkConst (graph ++ `regular_scale)) g[:27].toArray
    let regularReached := mkAppN (mkConst (graph ++ `regular_reached)) (g ++ x[36:38].toArray)
    let weak := source ++ #[g[25]!, regularScale] ++ g[27:34].toArray ++ #[x[36]!, regularReached] ++ x[38:42].toArray
    unless weak.size == 38 do throwError "graph response: expected the original full solver38 inputs"
    let actual (n : Name) := mkAppN (mkConst (full ++ n)) weak
    match which.getNat with
    | 0 =>
      let smooth := mkAppN (mkConst (masks ++ `χ₂_smooth)) source
      save `χ₂ x[:24].toArray (← inferType smooth).appArg! true
    | 1 => save `B x (actual `B) true
    | 2 =>
      let some F := tail.find? (fun e => e.isAppOf `JanetCartan.RevisedGlobal.finiteMap && e.appArg! == x[39]!)
        | throwError "graph response: phase margin lost the SAME literal physical finiteMap"
      save `same_finite_map x (← mkEqRefl F) false (some (← mkEq (actual `F) F))
    | 3 =>
      let B := mkAppN (mkConst (dest ++ `B)) x
      let type ← inferType (actual `apply)
      let type := type.replace fun e => if e == actual `B then some B else none
      save `apply x (actual `apply) false (some type)
    | 4 =>
      let B := mkAppN (mkConst (dest ++ `B)) x
      let type ← inferType (actual `smoothOn)
      let type := type.replace fun e => if e == actual `B then some B else none
      save `smoothOn x (actual `smoothOn) false (some type)
    | _ => throwError "graph response: invalid field"

end JanetCartan.PhysicalSampling.OriginalGraphResponseApplication
