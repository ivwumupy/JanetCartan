module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.DataTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.DataTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! The exact selected application of the checked native strain comparison.
Its proposition and proof are checked separately; the public endpoint then
  retains that same inequality through its exact proposition heads
  (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.SelectedCoreTemplate
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer
private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p

elab "retain_original_selected_primary_strain " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "selected primary strain: invalid publication mode"
  DataTemplate.withData fun d => do
    unless d.native.size == 50 && d.selected.size == 52 && d.sourceArgs.size == 53 do
      throwError "selected primary strain: original data boundary changed"
    let run := d.sourceArgs[51]!
    unless run.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterateWithForcing 53 &&
        run.getAppArgs[52]! == d.steps && run.getAppArgs[51]! ==
          app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSource d.selected do
      throwError "selected primary strain: not the SAME full forcing and finite Picard count"
    let native := app (root ++ `native_node_strain_le_discrepancies) d.sourceArgs
    let atFrame ← inferType native
    unless atFrame.isForall && atFrame.bindingDomain!.isAppOfArity ``LE.le 4 do
      throwError "selected primary strain: native numerical frame gate changed"
    let hGamma := app `JanetCartan.PhysicalSampling.OriginalBareScale.γ_le_ambient d.native[:24].toArray
    unless ← isDefEq (← inferType hGamma) atFrame.bindingDomain! do
      throwError "selected primary strain: original bare scale does not supply the SAME ambient tolerance"
    let atScale := mkApp native hGamma
    forallBoundedTelescope (← inferType atScale) (some 2) fun point _ => do
      unless point.size == 2 do throwError "selected primary strain: original point/core changed"
      let params := d.selected ++ #[d.steps,d.sample] ++ point
      let nativeStatement := app (root ++ `native_node_strain_le_discrepancies_statement)
        (d.sourceArgs ++ #[hGamma] ++ point)
      let key := if mode.getNat == 0 then `selected_node_strain_le_discrepancies_statement
        else `selected_node_strain_le_discrepancies
      let target := if mode.getNat == 0 then mkSort .zero else
        app (root ++ `selected_node_strain_le_discrepancies_statement) params
      let proof := if mode.getNat == 0 then nativeStatement else mkAppN atScale point
      let type ← instantiateMVars (← mkForallFVars params target)
      let value ← instantiateMVars (← mkLambdaFVars params proof)
      let env ← getEnv
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
            e.hasLooseBVars || e.hasSorry then
          throwError "selected primary strain: unresolved or extra numerical/analytic input"
        let missing := e.getUsedConstants.filter fun c => (env.find? c).isNone
        unless missing.isEmpty do throwError "selected primary strain: missing original metadata {missing.toList}"
        for old in #[`JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate,
            `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterate,
            `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
          if e.getUsedConstants.contains old then throwError "selected primary strain: old incomplete forcing escaped"
      let (type,value) := Lean.ShareCommon.shareCommon (type,value)
      let name := root ++ key
      IO.println s!"Kernel checking SAME selected primary strain {key}/56"
      (← IO.getStdout).flush
      if mode.getNat == 0 then
        addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
        addDocStringCore name "The exact selected52/N/sample pointwise primary-strain proposition, obtained from the SAME native statement using the original bare-scale frame bound. This is a proposition definition, not a new hypothesis (main:eq:primary-strain)."
      else
        addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
        addDocStringCore name "The checked selected52/N/sample application of the original native full complex-strain comparison. The original bare scale supplies the frame bound; no source-decay, response-success, or auxiliary profile premise is added (main:eq:primary-strain)."
      let ax ← collectAxioms name
      unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
        throwError "selected primary strain: nonstandard axioms {ax}"
      logInfo m!"PASS SAME selected primary strain {key}/56: {ax}"

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.SelectedCoreTemplate
end
