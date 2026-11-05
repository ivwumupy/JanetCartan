module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Quadratures
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData.Basic
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawCombinedNative
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalSynthesis
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceDiscrepancy
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawCombinedNative
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalPrimaryStrainMaskData
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Actual raw-primary tensor and inverse input, without another source cutoff

The source datum is the original full strain with its single `χ₂`, projected
by the same current's full stress frame and original `χsrc`. Its compact tensor
admission is proved from the actual raw-wave and history smoothness. The
discrepancy is the existing smooth representative on `χ₃ * Inv(input)`.
Consumer: `main:eq:primary-strain` and the original observed residual family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
private def old := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native
private def disc := `JanetCartan.PhysicalPrimary.OriginalSourceDiscrepancy
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def body (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "actual primary tensor source: unavailable original body {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta
private def termWith (p : List (Name × Expr)) (text : String)
    (target : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith p text target)

private def save (key : Name) (p : Array Expr) (proof target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "actual primary tensor source: unresolved input in {key}"
    unless (e.getUsedConstants.filter fun n => (env.find? n).isNone).isEmpty do
      throwError "actual primary tensor source: missing private metadata in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual primary tensor source {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original raw primary source quadrature is admitted to the original full uncut inverse. Its tensor already contains χ₂ once; neither the input nor the response is recut. All smoothness/support and the actual source-minus-identity representative are derived from the original construction (main:eq:primary-strain; app:ch_response:eq:response-full-map)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual primary tensor source: nonstandard axioms {name}: {ax}"
  logInfo m!"PASS actual primary tensor source {key}/{p.size}: {ax}"

structure Context where
  params : Array Expr
  graph : Array Expr
  weak : Array Expr
  rawArgs : Array Expr
  rawSmoothArgs : Array Expr
  F : Expr
  rawWave : Expr
  tensorField : Expr
  quadrature : Expr
  tensor : Expr
  input : Expr

def withSource (next : Context → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (old ++ `selectedSourceCombinedWave)).type (some 53) fun p _ => do
    unless p.size == 53 do throwError "actual primary tensor source: original source53 changed"
    let combined ← body (app (old ++ `selectedSourceCombinedWave) p)
    unless combined.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Combined.field 69 do
      throwError "actual primary tensor source: original combined raw operands changed"
    let native := combined.getAppArgs
    let nativeTensor := app (raw ++ `source) native
    let tensorBody ← body nativeTensor
    unless tensorBody.isAppOfArity ``JanetCartan.CorrectedAtoms.complexAtomicSource 5 do
      throwError "actual primary tensor source: not the complete original cutoff strain"
    let ta := tensorBody.getAppArgs
    let F := ta[2]!
    let χ := ta[3]!
    let rawWave := ta[4]!
    let sm ← body (app (old ++ `selectedSourceCombinedWave_smooth) p)
    unless sm.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Combined.active_smooth 70 do
      throwError "actual primary tensor source: original active raw smoothness changed"
    let hRaw := app (raw ++ `raw_smooth) sm.getAppArgs
    let hRawType ← inferType hRaw
    unless hRawType.isAppOfArity ``ContDiffOn 11 do
      throwError "actual primary tensor source: raw smoothness is not on the original chart"
    let chart := hRawType.getAppArgs[10]!
    let sum ← body combined
    let base ← body sum.getAppArgs[4]!
    let corrected ← body base
    unless corrected.isAppOfArity ``JanetCartan.CorrectedAtoms.complexCorrectedAtom 6 do
      throwError "actual primary tensor source: original correction changed"
    let B := corrected.getAppArgs[4]!
    unless B.isAppOfArity `JanetCartan.PhysicalSampling.OriginalGraphResponse.B 42 do
      throwError "actual primary tensor source: not the original graph42 response"
    let fullB ← body B
    unless fullB.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalFullResponse.B 38 do
      throwError "actual primary tensor source: not the original full uncut response38"
    let weak := fullB.getAppArgs
    let fixed := weak[:23].toArray
    let hChart := app (masks ++ `chart_open) fixed
    let hχ := app (masks ++ `χ₂_smooth) fixed
    let hc := app (masks ++ `χ₂_compact) fixed
    let hχChart := app (masks ++ `χ₂_support_chart) fixed
    let actualF := app `JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native.sourceF p[:50].toArray
    let finite ← body actualF
    unless finite.isAppOfArity ``JanetCartan.RevisedGlobal.finiteMap 5 do
      throwError "actual primary tensor source: not the same original history map"
    let fa := finite.getAppArgs
    unless fa[3]!.isAppOfArity ``JanetCartan.FlatReference.map 2 do
      throwError "actual primary tensor source: missing the original flat reference"
    let G := fa[3]!.appArg!
    let hF := app (root ++ `finite_reference_smooth) #[fa[0]!,fa[2]!,G,fa[4]!,chart]
    let admissions := app ``JanetCartan.PrimarySourceAdmission.cutoff_strain_quadratures_mem
      #[ta[0]!,ta[1]!,F,rawWave,χ,chart,hχ,hc,hChart,hF,hRaw,hχChart]
    let mapper := app (disc ++ `tensor_input) weak
    let mapperFn ← mkAppM ``DFunLike.coe #[mapper]
    let tensorType := (← inferType mapperFn).bindingDomain!
    withLocalDeclD `imaginary (mkConst ``Bool) fun q => do
      let admitted := app ``quadrature_admitted
        #[ta[0]!,← mkAppM ``tsupport #[χ],nativeTensor,
          Expr.proj ``And 0 admissions,Expr.proj ``And 1 admissions,q]
      let membership ← inferType admitted
      unless membership.isAppOfArity ``Membership.mem 5 do
        throwError "actual primary tensor source: compact tensor membership changed"
      let quadrature := membership.getAppArgs[4]!
      let subtype ← whnf tensorType
      unless subtype.isAppOfArity ``Subtype 2 do
        throwError "actual primary tensor source: compact tensor subtype changed"
      let tensor := mkAppN (mkConst ``Subtype.mk subtype.getAppFn.constLevels!)
        (subtype.getAppArgs ++ #[quadrature,admitted])
      let input := mkApp mapperFn tensor
      next {
        params := p.push q
        graph := B.getAppArgs
        weak := weak
        rawArgs := native
        rawSmoothArgs := sm.getAppArgs
        F := F
        rawWave := rawWave
        tensorField := nativeTensor
        quadrature := quadrature
        tensor := tensor
        input := input }

elab "publish_original_primary_source_data " mode:num : command => liftTermElabM do
  unless mode.getNat < 6 do throwError "actual primary tensor source: unknown mode"
  withSource fun c => do
    let t := app (root ++ `tensor) c.params
    let mapper := app (disc ++ `tensor_input) c.weak
    let value ← mkAppM ``DFunLike.coe #[mapper]
    let value := mkApp value t
    let input := app (root ++ `input) c.params
    if mode.getNat == 0 then
      save `tensor c.params c.tensor (← inferType c.tensor) true
    else if mode.getNat == 1 then
      save `input c.params value (← inferType value) true
    else if mode.getNat == 2 then
      let value ← mkAppM ``DFunLike.coe #[app (disc ++ `discrepancy) c.weak]
      let value := mkApp value input
      save `discrepancy c.params value (← inferType value) true
    else if mode.getNat == 3 then
      let proof := app (disc ++ `discrepancy_smooth) (c.weak.push input)
      let value ← mkAppM ``DFunLike.coe #[app (disc ++ `discrepancy) c.weak]
      let value := mkApp value input
      let target := (← inferType proof).replace fun e =>
        if e == value then some (app (root ++ `discrepancy) c.params) else none
      save `discrepancy_smooth c.params proof target
    else if mode.getNat == 4 then
      let proof := app (disc ++ `tensor_input_ae) (c.weak.push t)
      let target := (← inferType proof).replace fun e => if e == value then some input else none
      save `input_ae c.params proof target
    else
      let he := app (root ++ `input_ae) c.params
      let Q := app `JanetCartan.PhysicalInitialization.OriginalRegular.Current.Q c.weak
      let η := (← inferType (app (masks ++ `χsrc_smooth) c.weak[:23].toArray)).appArg!
      let localInput ← mkAppM ``Subtype.val #[input]
      let proof ← mkAppM ``cutoff_stress_input_support #[Q,η,t,localInput,he]
      save `input_support c.params proof (← inferType proof)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate
end
