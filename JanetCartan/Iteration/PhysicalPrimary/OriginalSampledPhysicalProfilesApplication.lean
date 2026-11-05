module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfiles
public import JanetCartan.Iteration.PhysicalPrimary.Basic
public import JanetCartan.Iteration.PhysicalPrimary.WeightedSynthesis
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActualTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalWeights

/-!
# Actual selected-source physical jets with their literal Fourier mass

This proof uses the checked original source53 field, the same finite prefix,
ONE selected shift, original detector, and native64 whole response. It integrates
the already checked corrected-atom physical jets over the actual input density.
The separate positive baseline is unscaled. The inner angular factor is handled
without deleting its zero labels. No source norm or mass estimate is assumed.

The conclusion retains the literal integral of the norm of weightedWideDensity.
Its actual full-forcing low-Sobolev bound is a separate producer. Only after that
bound is supplied may the unchanged original weighted synthesis yield the final
physical Sobolev profiles (`main:eq:primary-fixed-scales`). These physical
carrier-scale jets are not the demodulated R-scale pair-amplitude estimates.

The actual Schwartz aggregate below is the original physicalCutoff Dsmooth times
the raw sampled primary. Its DATA uses only the existing native smoothness
producer, not a successful mass or primary-norm premise. The original finite-row
majorant is also applied to the checked literal source mass jets. Its equality germ is preserved on Dsmooth.core; no
identity on the entire original source chart is asserted (`main:eq:primary`,
`main:eq:metric-ledger`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

publish_quantitative_original_selected_mass_jets 1

end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalSourceUniformJetsApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (Nat.repeat (fun e => Expr.proj ``And 1 e) j h)
private def exactType (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  for arg in value.getAppArgs do
    let .forallE _ _ rest _ := type.consumeMData | throwError "unchanged source-jet signature moved"
    type := rest.instantiate1 arg
  if type.isAppOf (ns ++ `selectedSourceCombinedWave_mass_statement) then
    let statement ← getConstInfo type.getAppFn.constName!
    let some body := statement.value? (allowOpaque := true) |
      throwError "actual source mass-jet statement body is unavailable"
    return (body.beta type.getAppArgs).headBeta
  return type
private def termWith (vars : List (Name × Expr)) (code : String) (target : Expr) : MetaM Expr :=
  Term.TermElabM.run' (JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code (some target))

elab "publish_actual_source_uniform_physical_jets" mode:num : command => liftTermElabM do
  let mode := mode.getNat
  unless mode < 2 do throwError "unknown actual uniform source physical jet mode"
  OriginalSampledPhysicalProfilesQuantitativeTemplate.withActualSelectedSourceWave
    fun params _ _ _ _ _ _ => do
      let original := app (ns ++ `selectedSourceCombinedWave_mass_jets) params
      let rates := app `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope.stage_rates params[:50].toArray
      let hLam := part rates 2
      let row := Expr.proj ``Sigma 0 params[52]!
      forallBoundedTelescope (← exactType original) (some 3) fun point _ => do
        unless point.size == 3 do throwError "actual physical jet/point/membership tail changed"
        let h := mkAppN original point
        let type ← exactType h
        unless type.isAppOfArity ``LE.le 4 do throwError "actual physical jet is not its norm bound"
        let rhs := type.getAppArgs[3]!
        unless rhs.isAppOfArity ``HMul.hMul 6 do throwError "actual physical jet lost its literal mass factor"
        let atom := rhs.getAppArgs[4]!
        let totalMass := rhs.getAppArgs[5]!
        unless atom.isAppOfArity ``HMul.hMul 6 do throwError "actual physical jet lost its common carrier power"
        let cost := atom.getAppArgs[4]!
        let scale := atom.getAppArgs[5]!
        let uniform := mkApp (app (ns ++ `uniformPhysicalCost) params[:44].toArray) point[0]!
        let hrow := app (ns ++ `physicalCost_le_uniform) (params[:44].toArray ++ #[row,point[0]!])
        let zero ← withLCtx {} #[] <| mkNumeral (mkConst ``Real) 0
        let nonneg (e : Expr) := mkAppN type.getAppFn ((type.getAppArgs.set! 2 zero).set! 3 e)
        let hscale ← termWith [(`hLam,hLam)]
          "(by exact Real.rpow_nonneg (le_of_lt hLam) _)" (nonneg scale)
        let hmass ← termWith []
          "(by exact add_nonneg zero_le_one (MeasureTheory.integral_nonneg fun _ => norm_nonneg _))" (nonneg totalMass)
        let target := type.replace fun e => if e == cost then some uniform else none
        unless target.getUsedConstantsAsSet.contains (ns ++ `uniformPhysicalCost) do
          throwError "actual row-majorant replacement did not occur"
        let result ← termWith [(`h,h),(`hrow,hrow),(`hscale,hscale),(`hmass,hmass)]
          "(by exact le_trans h (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrow hscale) hmass))"
          target
        let all := params ++ point
        let statement := ns ++ `selectedSourceCombinedWave_uniform_mass_statement
        let type ← instantiateMVars (← mkForallFVars all (if mode == 0 then mkSort .zero else app statement all))
        let value ← instantiateMVars (← mkLambdaFVars all (if mode == 0 then target else result))
        for e in #[type,value] do
          if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
            throwError "actual uniform source physical jets left unresolved data"
        let (type,value) := Lean.ShareCommon.shareCommon (type,value)
        let name := if mode == 0 then statement else ns ++ `selectedSourceCombinedWave_uniform_mass_jets
        liftM <| IO.eprintln s!"checking actual uniform source physical jets mode {mode} / {all.size}"
        if mode == 0 then
          addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
        else
          addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
        addDocStringCore name "Same-source physical jets with the original row-only prehistory cost, common carrier power, unscaled baseline and literal Fourier mass; no source mass estimate is assumed (main:eq:primary-fixed-scales)."
        logInfo m!"Checked actual source uniform physical jets mode {mode} / {all.size}; final full-source mass bound remains a separate producer."
end JanetCartan.PhysicalPrimary.OriginalSourceUniformJetsApplication
end
publish_actual_source_uniform_physical_jets 0
publish_actual_source_uniform_physical_jets 1

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalSourcePrimaryApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def exactType (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  for arg in value.getAppArgs do
    let .forallE _ _ rest _ := type.consumeMData | throwError "changed actual primary signature"
    type := rest.instantiate1 arg
  return type
private def termWith (vars : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code)
private def save (key : Name) (params : Array Expr) (value : Expr) (data : Bool)
    (expected : Option Expr := none) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params (expected.getD (← inferType value)))
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for e in #[type,value] do
    let unknown := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless unknown.isEmpty do throwError "actual primary lacks original private producers: {unknown.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual primary has a sample index, mass premise or unresolved extra input"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"checking actual original source primary {key} / {params.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original sampled source family, original nonnegative outer weights and ONE shift define the genuine Schwartz aggregate with b=δR^RevisedScales.forcingExponent n. No mass or norm success input; global cutoff-times-aggregate value and core germ only (main:eq:primary, main:eq:metric-ledger)."
  logInfo m!"Checked actual source primary {key} / {params.size}; δ DATA, no sample i or analytic success premise."

elab "publish_actual_source_primary" mode:num : command => liftTermElabM do
  let mode := mode.getNat
  unless mode < 3 do throwError "unknown actual source primary mode"
  OriginalSampledPhysicalProfilesQuantitativeTemplate.withActualSelectedSourceWave
    fun params _ _ _ _ _ _ => do
      let source := params[:52].toArray
      let index ← inferType params[52]!
      unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
        throwError "actual primary changed original sample7"
      let s := index.getAppArgs
      let rows := s[0]!
      unless rows.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
        throwError "actual primary changed original row22"
      let cube ← getConstInfo `JanetCartan.PhysicalSampling.OriginalWeights.exists_cube
      let some cubeProof := cube.value? (allowOpaque := true) | throwError "missing original finite cube"
      let cubeProof := (cubeProof.beta rows.getAppArgs).headBeta
      unless cubeProof.isAppOfArity `JanetCartan.PhysicalSampling.exists_finite_original_carrier_weight_bounds 5 do
        throwError "changed original finite carrier cube"
      let finiteRows := cubeProof.getAppArgs[1]!
      unless cubeProof.getAppArgs[0]! == rows do throwError "original row Fintype changed"
      let finite ← withLocalDecl `instOriginalRows .instImplicit
          (mkApp (mkConst ``Fintype [.zero]) rows) fun inst => do
        let value ← synthInstance (mkApp (mkConst ``Fintype [.zero]) index)
        return (← mkLambdaFVars #[inst] value).beta #[finiteRows]
      let wave := app (ns ++ `selectedSourceCombinedWave) params
      let smooth := app (ns ++ `selectedSourceCombinedWave_smooth) params
      let smType ← exactType smooth
      unless smType.isAppOfArity ``ContDiffOn 11 do throwError "changed original source smoothness"
      let chart := smType.getAppArgs[10]!
      unless chart.isAppOfArity `JanetCartan.LocalDomain.chart 2 do throwError "lost original Dsmooth chart"
      let D := chart.getAppArgs[0]!
      let n := chart.getAppArgs[1]!
      let V := smType.getAppArgs[5]!
      unless V.isAppOfArity ``EuclideanSpace 2 && V.getAppArgs[1]!.isAppOfArity ``Fin 1 do
        throwError "changed original physical codomain"
      let N := V.getAppArgs[1]!.appArg!
      let Z ← mkLambdaFVars #[params[52]!] wave
      let hZ ← mkLambdaFVars #[params[52]!] smooth
      let μ := mkAppN (mkConst `JanetCartan.CanonicalRowComparison.sampleWeight [.zero]) s
      let rates := app `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope.stage_rates params[:50].toArray
      let currentType ← inferType (.proj ``And 0 rates)
      let R := currentType.appArg!
      withLocalDeclNoLocalInstanceUpdate `δ .default (mkConst ``Real) fun δ => do
        let b ← termWith [(`δ,δ),(`R,R),(`n,n)] "(δ * R ^ JanetCartan.RevisedScales.forcingExponent n)"
        let args := #[n,N,index,finite,D,b,μ,Z,hZ]
        let raw := mkAppN (mkConst `JanetCartan.PhysicalPrimary.cutSampledPrimary [.zero]) args
        let all := source.push δ
        let named := app (ns ++ `selectedSourcePrimary) all
        if mode == 0 then
          save `selectedSourcePrimary all raw true
        else if mode == 1 then
          let applied := mkAppN (mkConst `JanetCartan.PhysicalPrimary.cutSampledPrimary_apply [.zero]) args
          forallBoundedTelescope (← exactType applied) (some 1) fun point _ => do
            let proof := mkAppN applied point
            let target := (← exactType proof).replace fun e => if e == raw then some named else none
            unless target.getUsedConstantsAsSet.contains (ns ++ `selectedSourcePrimary) do
              throwError "global value identity lost actual primary DATA"
            save `selectedSourcePrimary_apply (all ++ point) proof false (some target)
        else
          let info ← getConstInfo `JanetCartan.PhysicalPrimary.cutSampledPrimary
          let some body := info.value? (allowOpaque := true) | throwError "missing original cutoff aggregate value"
          let expanded := (body.instantiateLevelParams info.levelParams [.zero] |>.beta args).headBeta
          unless expanded.isAppOfArity `JanetCartan.PhysicalPrimary.cutSchwartz 5 do
            throwError "actual primary is no longer the original cutSchwartz"
          let applied := app `JanetCartan.PhysicalPrimary.cutSchwartz_eventuallyEq expanded.getAppArgs
          forallBoundedTelescope (← exactType applied) (some 2) fun point _ => do
            let proof := mkAppN applied point
            let target := (← exactType proof).replace fun e => if e == expanded then some named else none
            unless target.getUsedConstantsAsSet.contains (ns ++ `selectedSourcePrimary) do
              throwError "core germ lost actual primary DATA"
            save `selectedSourcePrimary_eventuallyEq (all ++ point) proof false (some target)
end JanetCartan.PhysicalPrimary.OriginalSourcePrimaryApplication
end
publish_actual_source_primary 0
publish_actual_source_primary 1
publish_actual_source_primary 2
