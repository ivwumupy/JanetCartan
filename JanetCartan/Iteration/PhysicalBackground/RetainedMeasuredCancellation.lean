module

public import JanetCartan.Iteration.PhysicalBackground.Cancellation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedCancellation
import all JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedCancellation
import all JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalMeanCancellation
public meta import Lean

/-!
# Retained full-weight geometry for the literal measured-source cancellation

Replay only the already-proved retained-chart geometry and canonical-mask
certificates. Apply the v2 measured-source cancellation theorem to those same
arguments. Its own source, raw correction and factor-two density are retained;
no old cutoff-zero/factor-four raw correction or density is transported across
this construction. Consumer: the actual current `NativeDensity` base variation
and exact reduced cancellation (`app:ch_background:prop:bg-current`,
`app:ch_background:eq:bg-current-identity`).

This is a retained-data consequence, not the original-data parent: the latter
must apply it to its exact current chart/operator and the ONE protected χ.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

public meta section
namespace JanetCartan.PhysicalBackground.RetainedMeasuredCancellationApplication
open Lean Meta Elab Command Term

/-- Keep actual argument names and values from a checked application. -/
def arguments (application : Expr) : MetaM (Array (Name × Expr)) := do
  let some name := application.getAppFn.constName? |
    throwError "retained measured cancellation: application is not a constant"
  let mut type := (← getConstInfo name).type
  let mut result := #[]
  for arg in application.getAppArgs do
    type ← zetaReduce type
    let .forallE name _ body _ := type |
      throwError "retained measured cancellation: input telescope changed"
    result := result.push (name.eraseMacroScopes, arg)
    type := body.instantiate1 arg
  pure result

/-- Reapply the native factor-two consumer using only the same retained
geometry and mask proofs from the old geometric producer. -/
elab "realize_retained_measured_physical_cancellation" : command => liftTermElabM do
  let retainedName := `JanetCartan.PositiveBackground.retained_physicalDensityMean_uncorrected_core_cancellation
  let maskName := `JanetCartan.PositiveBackground.physicalDensityMean_uncorrected_core_cancellation_of_supplied_masks
  let geometryName := `JanetCartan.PositiveBackground.exists_smooth_physical_background_cancellation_with_exterior
  let consumer := `JanetCartan.PhysicalBackground.physicalDensityMean_core_cancellation
  let retainedInfo ← getConstInfo retainedName
  let some retainedBody := retainedInfo.value? (allowOpaque := true) |
    throwError "retained measured cancellation: retained proof requires import all"
  let maskInfo ← getConstInfo maskName
  let some maskBody := maskInfo.value? (allowOpaque := true) |
    throwError "retained measured cancellation: canonical-mask proof requires import all"
  let prefixArity (type : Expr) (last : Name) : TermElabM Nat := do
    let mut type := type
    let mut count := 0
    while true do
      let .forallE name _ body _ := type |
        throwError "retained measured cancellation: geometric prefix ends before {last}"
      count := count + 1
      if name.eraseMacroScopes == last then return count
      type := body
    throwError "retained measured cancellation: unreachable geometric prefix"
  let maskArity ← prefixArity maskInfo.type `hstress
  let geometryArity ← prefixArity (← getConstInfo geometryName).type `hcoeff
  forallTelescope retainedInfo.type fun params _ => do
    let value ← Core.betaReduce (← zetaReduce (retainedBody.beta params))
    unless value.isAppOfArity ``Exists.intro 4 do
      throwError "retained measured cancellation: full retained geometry does not end in its hH witness ({value.getAppFn})"
    let tail := value.getAppArgs.back!
    lambdaTelescope tail fun oldTail inner => do
      unless oldTail.size == 5 do
        throwError "retained measured cancellation: expected action, old regularity/density/smoothness/AE binders"
      let inner ← Core.betaReduce (← zetaReduce inner)
      let some masks := inner.find? (·.isAppOfArity maskName maskArity) |
        throwError "retained measured cancellation: retained canonical-mask application missing"
      unless !masks.hasLooseBVars do
        throwError "retained measured cancellation: unresolved local geometry witness"
      let maskArgs ← arguments masks
      let maskValue ← Core.betaReduce (← zetaReduce (maskBody.beta masks.getAppArgs))
      let some geometry := maskValue.find? (·.isAppOfArity geometryName geometryArity) |
        throwError "retained measured cancellation: canonical full-weight geometry application missing"
      if geometry.hasLooseBVars then
        throwError "retained measured cancellation: canonical geometry depends on a later chosen density"
      let geometryArgs ← arguments geometry
      let get (name : Name) : TermElabM Expr := do
        match geometryArgs.find? (fun pair => pair.1 == name) with
        | some (_, result) => pure result
        | none =>
          match maskArgs.find? (fun pair => pair.1 == name) with
          | some (_, result) => pure result
          | none => throwError "retained measured cancellation: missing actual geometric argument {name}"
      let consumerInfo ← getConstInfo consumer
      unless consumerInfo.levelParams.length == masks.getAppFn.constLevels!.length do
        throwError "retained measured cancellation: consumer universes changed"
      let mut type := consumerInfo.type
      let mut chosen : Array Expr := #[]
      while true do
        let .forallE name _ body _ := type | break
        let name := name.eraseMacroScopes
        let oldName := if name == `F then `G else if name == `hF then `hG
          else if name == `hgap then `hgap_pos else if name == `hcoercive then `hgap else name
        let arg ← get oldName
        chosen := chosen.push arg
        type := body.instantiate1 arg
      let result := mkAppN (mkConst consumer masks.getAppFn.constLevels!) chosen
      -- The old regularity, density, smoothness and AE proofs are NOT inputs.
      -- The new consumer quantifies its OWN measured raw regularity and its
      -- OWN factor-two representative. Only the unchanged test action is kept.
      let fixed := params ++ #[oldTail[0]!]
      let applicationType ← instantiateMVars (← mkForallFVars fixed (← inferType result))
      let value ← instantiateMVars (← mkLambdaFVars fixed result)
      if applicationType.hasMVar || value.hasMVar || applicationType.hasFVar || value.hasFVar ||
          applicationType.hasLevelMVar || value.hasLevelMVar || applicationType.hasSorry || value.hasSorry then
        throwError "retained measured cancellation: old raw/density assumptions or open geometry leaked"
      addDecl (.thmDecl {
        name := `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation,
        levelParams := retainedInfo.levelParams, type := applicationType, value }) (forceExpose := true)
      logInfo "retained full-weight geometry applied to literal measured-source/factor-two cancellation; no old raw, density or cutoff-zero premise reused"

end JanetCartan.PhysicalBackground.RetainedMeasuredCancellationApplication
end

realize_retained_measured_physical_cancellation
