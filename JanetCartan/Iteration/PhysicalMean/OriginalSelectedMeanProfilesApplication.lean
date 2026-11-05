module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfilesTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-! Execute only actual declared original-data producers. The common profile's
literal full-source iterate fixes J before N; W and H use that exact same J.
No analytic success assumption is inserted in the final telescope.
This file is staged until the actual117/116/canonical14 imports have their GO. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanProfilesApplication
open Lean Meta Elab Command
open OriginalSelectedMeanProfilesTemplate
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)
elab "construct_original_selected_mean_profile " mode:num : command => liftTermElabM do
  unless mode.getNat < 6 do throwError "actual mean profile: unknown construction mode"
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native native39 _ => do
    withTransparency .default do
      let selected := p[:52].toArray
      let N := p[53]!
      let early := selected[:33].toArray.push N
      let fixed := native[:44].toArray
      let allq := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.iterate_profile selected
      let allqType ← inferType allq
      let some run := allqType.find? (·.isAppOfArity
          `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterateWithForcing 53)
        | throwError "actual mean profile: lost genuine full-source iterate53"
      let J := run.getAppArgs[50]!
      unless !J.hasLooseBVars && J.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 do
        throwError "actual mean profile: J changed after Picard count"
      let wroot := `JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles
      let CW := app (wroot ++ `CW) early
      let hCW := app (wroot ++ `CW_nonneg) early
      let fullGate ← termWith [(`S,app (wroot ++ `SfullW) fixed),(`R0,native[44]!)] "S ≤ R0"
      let bufferGate ← termWith
        [(`S,app `JanetCartan.PhysicalMean.OriginalNormalCompletionBufferProfiles.Sbuffer fixed),(`R0,native[44]!)] "S ≤ R0"
      let targetProfile := app `JanetCartan.PhysicalMean.OriginalSelectedMeanData.normalizedTarget_cNorm_profile selected
      forallBoundedTelescope allqType (some 1) fun aux _ => do
        unless aux.size == 1 do throwError "actual mean profile: initial auxiliary reach changed"
        let hAux := aux[0]!
        withLocalDeclNoLocalInstanceUpdate `hFullW .default fullGate fun hFullW => do
          withLocalDeclNoLocalInstanceUpdate `hNormalBuffer .default bufferGate fun hBuffer => do
            forallBoundedTelescope (← inferType targetProfile) (some 1) fun target _ => do
              unless target.size == 1 do throwError "actual mean profile: current-stage target reach changed"
              let wProfile := app (wroot ++ `initializedField_strain_profile)
                (selected ++ #[hAux,N,hFullW])
              let d : ActualPacket := {
                selected,native,native39,fields := f,J,N,hAux,hBuffer,hTarget := target[0]!,
                extraInitialGates := #[hFullW],CW,hCW,hWprofile := wProfile }
              match mode.getNat with
              | 0 => publishBudget d false
              | 1 => publishBudget d true
              | 2 => publishPhysicalBudget d false
              | 3 => publishPhysicalBudget d true
              | 4 => publishCompletedProfile d
              | 5 => publishPhysicalProfile d
              | _ => throwError "actual mean profile: unknown mode"
end JanetCartan.PhysicalMean.OriginalSelectedMeanProfilesApplication
end
