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


/-!
# Original full-self prerequisite: BaselineAlias

Identify the original sampled baseline with the genuine full parent amplitude on its original chart.
The public names, original choices and checked proof bodies are retained from
the combined producer. Consumer: the actual `full_self_profile`, and for the
identity leaves the original signed-pair self ledger
(`main:eq:mean-normal-field`, `main:prop:mean`, `main:prop:pairs`).
-/

open scoped BigOperators
open scoped ContDiff Matrix.Norms.Frobenius
/- Actual component: ParentAlias. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.ParentAlias
private meta def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private meta def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private meta def openApp (e : Expr) : MetaM Expr := do
  let .const name levels := e.getAppFn | throwError "actual baseline H: expected original application"
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) | throwError "actual baseline H: unavailable {name}"
  return ((body.instantiateLevelParams info.levelParams levels).beta e.getAppArgs).headBeta
private meta def termWith (vars : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code)
private meta def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual baseline H: unresolved declaration {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual baseline H: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking exact whole-chart baseline {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual baseline H: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS exact whole-chart baseline {key}/{p.size}/std3: {axioms}"
run_meta do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    let atX := (mkApp f[5]! p[54]!).headBeta
    let a := atX.getAppArgs
    let Z := a[7]!.getAppArgs[2]!
    let base := Z.getAppArgs[4]!
    let packed ← openApp base
    unless packed.isAppOf ``OriginalCanonicalSampled.sampledPositiveBaseline do
      throwError "actual baseline H: changed original collected baseline"
    let .forallE _ sample _ _ ← inferType a[6]! | throwError "actual baseline H: missing original sample type"
    unless sample.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "actual baseline H: sample must be the same original filtered SampleIndex7"
    let sa := sample.getAppArgs
    withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => do
      let row ← termWith [(`i,i)] "i.1"
      let node ← termWith [(`i,i)] "i.2.val"
      let cell ← termWith [(`a,node)] "a.1"
      let color ← mkAppM ``JanetCartan.SeparatedSampling.color #[sa[1]!,cell]
      let shift := mkApp sa[6]! row
      let hweight ← termWith [(`i,i)] "(Finset.mem_filter.mp i.2.property).2"
      let rc := native ++ #[row,color,sa[4]!,sa[5]!,shift,node,hweight]
      unless rc.size == 57 do throwError "actual baseline H: changed original baseline-node ABI"
      let statement := app `JanetCartan.PhysicalPairs.OriginalBaselineNode.amplitude_on_original_statement rc
      forallBoundedTelescope (← openApp statement) (some 2) fun xy eq => do
        let x := xy[0]!
        let mut nativeEq ← openApp (app `JanetCartan.PhysicalPairs.OriginalBaselineNode.native_demodulation_statement rc)
        for v in xy do nativeEq := nativeEq.bindingBody!.instantiate1 v
        let fn := nativeEq.getAppArgs[1]!
        unless fn.isAppOfArity `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude 17 do
          throwError "actual baseline H: native full derivative changed"
        let T := fn.getAppArgs[5]!
        unless T.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.T 53 do
          throwError "actual baseline H: original source geometry53 changed"
        let chart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart T.getAppArgs[:23].toArray
        let z ← mkAppM ``JanetCartan.torusQuotient #[x]
        let collectorName := ``OriginalCanonicalSampled.sampledPositiveBaseline_apply
        let collector := mkAppN (mkConst collectorName ((← getConstInfo collectorName).levelParams.map (fun _ => .zero)))
          (packed.getAppArgs ++ #[z,i])
        let collected := (← inferType collector).getAppArgs[2]!
        let some slice := collected.find? (·.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.positiveBaseline 54)
          | throwError "actual baseline H: original positive baseline54 missing at same node"
        let observed ← openApp slice
        unless observed.isAppOfArity ``OriginalCanonicalBaseline.observedBaseline 12 do
          throwError "actual baseline H: changed original observed extension"
        let oa := observed.getAppArgs
        let hn := app `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.positiveBaseline_native (slice.getAppArgs.push z)
        let nEq := (← inferType hn).getAppArgs
        let hr := app `JanetCartan.PhysicalPairs.OriginalSourcePlateau.representative_on_original_chart
          (chart.getAppArgs ++ xy)
        let hg := app `JanetCartan.PhysicalPairs.OriginalSourcePlateau.germ_on_original_chart
          (chart.getAppArgs ++ xy)
        let hone ← mkAppM ``Filter.EventuallyEq.eq_of_nhds #[hg]
        let rep := (← inferType hr).getAppArgs[1]!
        let remove := app ``JanetCartan.PhysicalPairs.OriginalSourceChartTemplate.remove_observation
          #[oa[0]!,oa[1]!,oa[6]!,oa[4]!,nEq[1]!,rep,x,hn,hr,hone]
        let collected ← mkAppM ``Eq.trans #[collector,remove]
        let parent := eq.getAppArgs[2]!
        let w := parent.appArg!
        unless w.isAppOfArity ``Prod.mk 4 && w.getAppArgs[3]!.isAppOfArity ``Prod.mk 4 do
          throwError "actual baseline H: changed parent physical/outer point"
        let coordinate := w.getAppArgs[3]!.getAppArgs[2]!
        let hcoordinate := app ``OriginalBackgroundHermitianSupportTemplate.outer_sampling_node #[slice.getAppArgs[52]!]
        let ce := (← inferType hcoordinate).getAppArgs
        unless ← isDefEq ce[1]! coordinate do
          throwError "actual baseline H: not the original outer sampling point"
        let converted := parent.replace fun e => if e == coordinate then some ce[2]! else none
        let hparent ← withLocalDeclNoLocalInstanceUpdate `outerCoordinate .default (← inferType coordinate) fun y => do
          let family ← mkLambdaFVars #[y] (parent.replace fun e => if e == coordinate then some y else none)
          mkAppM ``congrArg #[family,hcoordinate]
        let reverse ← mkAppM ``Eq.symm #[hparent]
        let lhs ← termWith [(`base,base),(`z,z),(`i,i)] "base.val z i"
        let target ← mkEq lhs parent
        let proof := mkAppN (mkConst ``Eq.trans [.succ .zero])
          #[eq.getAppArgs[0]!,lhs,converted,parent,collected,reverse]
        save `sampled_baseline_eq_parent (p[:39].toArray ++ #[i] ++ xy) proof target
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.ParentAlias
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.sampled_baseline_eq_parent

