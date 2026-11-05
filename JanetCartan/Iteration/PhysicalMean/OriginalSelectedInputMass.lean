module
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMass
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmission
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmission
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# The original selection discharges both numerical mass-admission guards

Use the SAME selected gamma, source interval and reached initial threshold.
The unweighted input mass theorem now has only selected39, fixed Fourier
prefix, smooth source DATA and original sample index. No gamma/R90, source
profile or successful mass premise remains. The genuine all-order full-source
Picard profile is still required for the Cmass(N)*h consequence
(`main:eq:primary-fixed-scales`, `app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
open Lean Meta Elab Command
open JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate (withSelectedAtPoint)
run_elab withSelectedAtPoint fun native selected point => do
  unless native.size == 53 && selected.size == 42 && point.size == 47 do
    throwError "selected original mass: changed canonical admission boundary"
  withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
    let name := `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.fourierMass_le
    let p := native[:50].toArray ++ #[point[27]!,point[39]!,L]
    let base := mkAppN (mkConst name) p
    forallBoundedTelescope (← inferType base) (some 2) fun sources _ => do
      unless sources.size == 2 do throwError "selected original mass: source/index boundary changed"
      let proof := mkAppN base sources
      let params := selected[:39].toArray ++ #[L] ++ sources
      let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
      let value ← instantiateMVars (← mkLambdaFVars params proof)
      let env ← getEnv
      for e in #[type,value] do
        let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
        unless missing.isEmpty do throwError "selected original mass: unavailable {missing.toList}"
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
          throwError "selected original mass: extra row, point or numeric guard escaped"
      let (type,value) := Lean.ShareCommon.shareCommon (type,value)
      let name := `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.selected_fourierMass_le
      addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      addDocStringCore name "Actual unweighted Fourier mass on the SAME original selected data and global inverse: both numerical gamma/R90 guards are proved by the single canonical admission. Only selected39, fixed prefix, arbitrary smooth source DATA and original sample index; no mass/source success premise (main:eq:primary-fixed-scales)."
      logInfo "actual selected unweighted mass42: SAME input/global inverse, original39 admission supplies both numeric guards, fixed prefix/source DATA/sample"
end
