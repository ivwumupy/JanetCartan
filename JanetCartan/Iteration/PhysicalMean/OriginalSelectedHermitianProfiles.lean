module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianProfilesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNative
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalWeightMass
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineAmplitudeProfiles
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
import all JanetCartan.Iteration.PhysicalMean.PhysicalHermitianProfile
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# Static budgets for the original FULL sampled Hermitian tensor

The common all-order D_N and the original baseline/total-weight budgets determine
CH_N before the initial scale, history, target, smoothing accuracy, prefix, source
and sample. This is the actual cost used by the full physical-buffer profile and
by the completed mean's independent fixed-budget convolution
(`main:eq:mean-normal-field`, `main:prop:mean`, `new:sec:order-of-choices`).

This initial publication contains actual static data and nonnegativity only.
It does NOT yet assert the still-separate actual full-tensor profile. The source,
baseline, whole-chart and unchanged11a/12 applications remain explicit until
those checked proof declarations are appended. The single original weight is
outside the tensor once; this is Cweight, not the unweighted source Cmass.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped BigOperators
public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.SourceBudget
private def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def openApp (e : Expr) : MetaM Expr := do
  let .const name levels := e.getAppFn | throwError "actual source budget: expected original application"
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) | throwError "actual source budget: original body unavailable {name}"
  return ((body.instantiateLevelParams info.levelParams levels).beta e.getAppArgs).headBeta
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual source budget: nonstatic/unresolved declaration {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual static source budget {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The true physical native-source cost C_s(COMMON D_N), with N fixed before the physical history and the whole complete forcing retained. No mass, sample-count, oscillatory phase jets or Fourier support replaces its all-order input (main:prop:mean; new:sec:order-of-choices)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual source budget: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual source budget {key}/{p.size}/std3: {axioms}"
run_meta do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    let atX := (mkApp f[5]! p[54]!).headBeta
    let a := atX.getAppArgs
    let Z := a[7]!.getAppArgs[2]!
    let source := Z.getAppArgs[5]!.getAppArgs[5]!
    let .forallE _ sample _ _ ← inferType a[6]! | throwError "missing original sample type"
    withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => do
      let static := p[:33].toArray.push p[53]!
      let D := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.D static
      let hD := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.D_nonneg static
      let moment := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
      let hγ := app (moment ++ `AtPoint.gamma_le_tolerance) p[:21].toArray
      let hR := app (moment ++ `moment_reached) p[:35].toArray
      let stem := app `JanetCartan.PhysicalPairs.OriginalSourceNative.source_cNorm_profile
        (native ++ #[hγ,hR,p[52]!,source,i])
      withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
        let shaped := mkAppN stem #[s,D,hD]
        forallTelescope (← inferType shaped) fun tail target => do
          unless tail.size == 6 do throwError "actual source budget: changed real scale/source boundary {tail.size}"
          let raw ← openApp target
          let some cost := raw.find? (·.isAppOfArity ``nativeIndividualPhysicalProfileConstant 17)
            | throwError "actual source budget: lost fixed native C_s(D_N)"
          let value ← mkLambdaFVars #[s] cost
          save `Csource static value (← inferType value) true
          let c := cost.getAppArgs
          unless c[11]! == D do throwError "actual source budget: not the common all-q D_N"
          let hCinv := app `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles.Cinv_nonneg native[:44].toArray
          let nonneg := app ``nativeIndividualPhysicalProfileConstant_nonneg
            (c[:15].toArray ++ #[hCinv,hD,c[15]!,c[16]!])
          let conclusion := (← inferType nonneg).replace fun e =>
            if e == cost then some (mkApp (app (root ++ `Csource) static) s) else none
          save `Csource_nonneg static (← mkLambdaFVars #[s] nonneg) (← mkForallFVars #[s] conclusion)
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.SourceBudget

namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.FullBudget
private def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def termWith (vars : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code)
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual full-H budget: later data or unresolved constant {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual full-H budget: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual static full-H budget {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The full sampled Hermitian budget CH_N, closed on selected33+N BEFORE history or target: exact Cweight times the complementary-order product constant of the prefix sum of the baseline cost plus the whole native C_s(D_N). No squared sqrt-weight sum, sample count, source mass or cF is introduced (main:eq:mean-normal-field; main:prop:mean)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual full-H budget: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual full-H budget {key}/{p.size}/std3: {axioms}"
elab "define_original_selected_hermitian_budget " mode:num : command => liftTermElabM do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p _ native _ _ => do
    let fixed := native[:44].toArray
    let static := p[:33].toArray.push p[53]!
    let CB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline fixed
    let hCB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline_nonneg fixed
    let CD := app (root ++ `Csource) static
    let hCD := app (root ++ `Csource_nonneg) static
    let Cw := app `JanetCartan.PhysicalMean.OriginalCanonicalWeightMass.Cweight fixed
    let hCw := app `JanetCartan.PhysicalMean.OriginalCanonicalWeightMass.Cweight_nonneg fixed
    if mode.getNat == 0 then
      let A ← termWith [(`CB,CB),(`CD,CD)] "(fun q : ℕ => (∑ j ∈ Finset.range (q+1), CB j)+CD q)"
      let C ← termWith [(`Cw,Cw),(`A,A)] "(fun s : ℕ => Cw*JanetCartan.PhysicalMean.hermitianPhysicalOrderConstant A s)"
      save `CH static C (← inferType C) true
    else
      withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
        let proof := app ``OriginalSelectedHermitianProfiles.full_hermitian_budget_nonneg
          #[Cw,CB,CD,hCw,hCB,hCD,s]
        let raw ← inferType proof
        let cost := raw.getAppArgs[3]!
        let expected := raw.replace fun e => if e == cost then some (mkApp (app (root ++ `CH) static) s) else none
        save `CH_nonneg static (← mkLambdaFVars #[s] proof) (← mkForallFVars #[s] expected)
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.FullBudget
end

define_original_selected_hermitian_budget 0
define_original_selected_hermitian_budget 1
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.Csource
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.Csource_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.CH
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.CH_nonneg
