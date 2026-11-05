module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfilesWhole
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfilesTemplate

/-!
# The stable original physical field of supplied source data

This metadata-only boundary preserves the checked native50/L/source/sample
callback, original component adjoint, whole69 field and native64 detector.
The source is DATA in the original smooth-residual carrier, not a successful
source or mass hypothesis. The final paper forcing and uniform estimates are
separate actual producers (`new:eq:mean-source`, `main:eq:primary`).

The public namespace and command names are retained for existing consumers.
This leaf is independent of subsequent quantitative jet/synthesis metadata.
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
open Lean Meta Elab Command
open OriginalSampledPhysicalProfilesTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def nativeType (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  for arg in value.getAppArgs do
    let .forallE _ _ rest _ := type.consumeMData |
      throwError "actual primary integral: changed published declaration arity"
    type := rest.instantiate1 arg
  return type

private def emit (field : Name) (xs : Array Expr) (proof : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual sampled primary: unresolved declaration {field}"
  let name := ns ++ field
  liftM <| IO.eprintln s!"actual sampled primary: checking {field}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original native stage and unchanged whole response on the old Dsmooth chart, with original scalar, source, cutoff, sample and rates (main:eq:primary-fixed-scales). Quantitative completion still requires the actual fixed-K Picard mass bound."
  logInfo m!"actual original physical wave: checked {field} / {xs.size}"

private def originalBodyAt (name : Name) (args : Array Expr)
    (levels : List Level := []) : MetaM Expr := do
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) |
    throwError "actual primary field: unavailable original producer {name}"
  unless info.levelParams.length == levels.length do
    throwError "actual primary field: native producer universe arguments changed"
  return ((body.instantiateLevelParams info.levelParams levels).beta args).headBeta

/-- Read the SAME selected geometry and component adjoint for supplied source
DATA. Only the original `wideInput` source operand changes; its n/J/index/A/Q0/L
and sample stay literal. The background-only step count is removed and forbidden
from the result. The complete paper source is supplied by the finite-source
producer, not by a successful norm premise (`main:eq:primary`). -/
def withActualSelectedSourceWave
    (next : Array Expr → Expr → Expr → Expr → Expr → Array Expr →
      Array (Name × Expr) → MetaM Unit) : MetaM Unit := do
  withActualSelectedFinalWave fun oldParams oldInput oldField native64 detector => do
    let actualInput ← originalBodyAt oldInput.getAppFn.constName! oldInput.getAppArgs
    unless actualInput.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalSource.finalWideInput 54 do
      throwError "actual supplied-source wave: original selected input changed"
    let originalInput ← originalBodyAt actualInput.getAppFn.constName! actualInput.getAppArgs
    unless originalInput.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalInput.wideInput 8 do
      throwError "actual supplied-source wave: missing literal original component input"
    let inputArgs := originalInput.getAppArgs
    let fixedInput := mkAppN originalInput.getAppFn inputArgs[:6].toArray
    let .forallE _ sourceType _ _ := (← nativeType fixedInput).consumeMData |
      throwError "actual supplied-source wave: original smooth source data type changed"
    let literal ← originalBodyAt oldField.getAppFn.constName! oldField.getAppArgs
    unless literal.isAppOfArity (wave ++ `Combined.field) 69 do
      throwError "actual supplied-source wave: original combined field changed"
    let oldSteps := oldParams[51]!
    withLocalDeclNoLocalInstanceUpdate `source .default sourceType fun source => do
      let input := mkAppN originalInput.getAppFn (inputArgs.set! 6 source)
      let combinedArgs := literal.getAppArgs.set! 68 input
      let field := app (wave ++ `Combined.field) combinedArgs
      let i := oldParams[52]!
      let index ← inferType i
      unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
        throwError "actual supplied-source wave: literal original outer sample changed"
      let hweight := mkAppN (mkConst (ns ++ `original_sample_weight_ne_zero) [.zero])
        (index.getAppArgs.push i)
      let smooth := app (wave ++ `Combined.active_smooth)
        (combinedArgs[:68].toArray ++ #[hweight,input])
      let params := oldParams[:51].toArray ++ #[source,i]
      for e in #[input,field,smooth] ++ native64 ++ detector.map Prod.snd do
        if (e.find? (· == oldSteps)).isSome ||
            (e.find? (fun t => t.isConstOf `JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate ||
              t.isConstOf `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterate)).isSome then
          throwError "actual supplied-source wave: background-only iterate or step count leaked"
      next params source input field smooth native64 detector

/-- The literal whole field of the original component adjoint applied to source
DATA, not a source or Fourier-mass bound. No new sampling choice is made. -/
elab "publish_quantitative_original_source_combined_wave" : command => liftTermElabM do
  withActualSelectedSourceWave fun params _ _ field smooth _ _ => do
    emit `selectedSourceCombinedWave params field true (some (← nativeType field))
    let smoothType ← nativeType smooth
    unless smoothType.isAppOfArity ``ContDiffOn 11 do
      throwError "actual supplied-source wave: original chart smoothness changed"
    let target := mkAppN smoothType.getAppFn
      (smoothType.getAppArgs.set! 9 (app (ns ++ `selectedSourceCombinedWave) params))
    emit `selectedSourceCombinedWave_smooth params smooth false (some target)

end JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
end
