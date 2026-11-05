module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianProfilesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNativeIdentity
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceChartRepresentative
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalWeightMass
public meta import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingScaled
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalPairs.OriginalSourceNativeTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
meta import Lean
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineNodeNative
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaselineApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseGeometry
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedSourceEstimates
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineAmplitudeProfiles
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives

public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.SelectedFields

/-!
# Original full-self prerequisite: NativeSourceProfile

The actual complete-forcing native source profile for the same named source field and fixed cutoff count.
The public names, original choices and checked proof bodies are retained from
the combined producer. Consumer: the actual `full_self_profile`, and for the
identity leaves the original signed-pair self ledger
(`main:eq:mean-normal-field`, `main:prop:mean`, `main:prop:pairs`).
-/

open scoped BigOperators
open scoped ContDiff Matrix.Norms.Frobenius
/- Actual component: NamedNativeProfile. -/
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
run_meta do
  let root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
  let name := root ++ `native_source_profile
  forallBoundedTelescope (← getConstInfo name).type (some 56) fun p target => do
    unless p.size == 56 do throwError "selected native source profile56 ABI changed"
    let some D := target.find? (·.isAppOfArity `JanetCartan.PhysicalMean.individualNativeInverseField 9)
      | throwError "selected native source profile has lost its actual complete nativeD"
    let some J := D.find? (·.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1)
      | throwError "selected native source profile has lost the same fixed cutoff"
    unless !J.hasLooseBVars && !(J.containsFVar p[53]!.fvarId!) do
      throwError "selected native source profile has a Picard-depth-dependent cutoff"
    let named := mkAppN (mkConst (root ++ `nativeSourceField)) (p[:52].toArray ++ #[J,p[53]!,p[54]!])
    let expected := target.replace fun e => if e == D then some named else none
    let type ← instantiateMVars (← mkForallFVars p expected)
    let value ← instantiateMVars (← mkLambdaFVars p (mkAppN (mkConst name) p))
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "selected native source profile alias retained unresolved input"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let out := root ++ `native_source_profile_on_selected_fields
    addDecl (.thmDecl {name := out,levelParams := [],type,value}) (forceExpose := true)
    let axioms ← collectAxioms out
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "selected native source alias has nonstandard axioms: {axioms}"
    logInfo m!"PASS same selected nativeD/source-profile56/std3: {axioms}"
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.native_source_profile_on_selected_fields

