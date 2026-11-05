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
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.BaselineAlias

/-!
# Original full-self prerequisite: BaselineProfile

The actual full-parent baseline profiles transfer to the same sampled baseline at the true current scale.
The public names, original choices and checked proof bodies are retained from
the combined producer. Consumer: the actual `full_self_profile`, and for the
identity leaves the original signed-pair self ledger
(`main:eq:mean-normal-field`, `main:prop:mean`, `main:prop:pairs`).
-/

open scoped BigOperators
open scoped ContDiff Matrix.Norms.Frobenius
/- Actual component: SampledBaseline. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.SampledBaseline
private meta def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private meta def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private meta def termWith (vars : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code)
private meta def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0
  (Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k)
private meta def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual baseline profile: additional analytic input escaped {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual baseline profile: missing producer {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual baseline R-profile {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual baseline profile: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual baseline R-profile {key}/{p.size}/std3: {axioms}"
/-112's exact parent_slice_profile57 is now canonical/default/std3. This file
introduces no assumed profile; the selected-baseline application below is its
literal same-sample specialization followed by the existing T≤R transfer. -/
run_meta do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    let atX := (mkApp f[5]! p[54]!).headBeta
    let a := atX.getAppArgs
    let .forallE _ sample _ _ ← inferType a[6]! | throwError "actual baseline profile: missing original sample"
    unless sample.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "actual baseline profile: not the same filtered original samples"
    let sa := sample.getAppArgs
    let fixed := native[:44].toArray
    let U := app (root ++ `sourceChart) p[:33].toArray
    let hU := app (root ++ `sourceChart_open) p[:33].toArray
    let CB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline fixed
    let hCB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline_nonneg fixed
    let hInitial ← mkAppM ``le_trans
      #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,native[45]!]
    let facts ← mkAppM ``fixedPicard_history_scale_facts #[hInitial,native[46]!]
    let hT := part facts 1
    let T := (← inferType hT).getAppArgs[3]!
    let R := (← inferType (part facts 0)).getAppArgs[3]!
    let hT0 ← termWith [(`hT,hT)] "(zero_le_one.trans hT)"
    withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => do
      let row ← termWith [(`i,i)] "i.1"
      let node ← termWith [(`i,i)] "i.2.val"
      let cell ← termWith [(`a,node)] "a.1"
      let color ← mkAppM ``JanetCartan.SeparatedSampling.color #[sa[1]!,cell]
      let shift := mkApp sa[6]! row
      let hweight ← termWith [(`i,i)] "(Finset.mem_filter.mp i.2.property).2"
      let rc := native ++ #[row,color,sa[4]!,sa[5]!,shift,node,hweight]
      let parentProfile := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.parent_slice_profile rc
      let eq := app (root ++ `sampled_baseline_eq_parent) (p[:39].toArray.push i)
      forallBoundedTelescope (← inferType eq) (some 2) fun xy equality => do
        let P ← mkLambdaFVars #[xy[0]!] equality.getAppArgs[2]!
        let B := mkApp (app (root ++ `sampledBaseline) p[:39].toArray) i
        let proof := app ``OriginalSelectedHermitianProfiles.sampled_baseline_profile_of_parent
          #[a[1]!.appArg!,a[0]!.appArg!,U,hU,B,P,eq,Expr.proj ``And 0 parentProfile,CB,hCB,T,R,hT0,
            part facts 2,Expr.proj ``And 1 parentProfile]
        save `sampled_baseline_profile (p[:39].toArray.push i) proof (← inferType proof)
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.SampledBaseline
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.sampled_baseline_profile

