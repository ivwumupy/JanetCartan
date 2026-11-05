module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawBaselineProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.Literal
import all JanetCartan.Iteration.PhysicalPairs.OriginalBaselineAmplitudeProfiles
import all JanetCartan.Iteration.PhysicalPairs.OriginalBaselineNodeNative
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-! # Exact unscaled original raw baseline differential

Consumer: main:eq:primary-strain. Use the original outer-node and raw retained
leading regularity with background_differential_eq. The old corrected atom
metadata supplies only this unchanged parameter/regularity spine; its derivative
identity and response are not used. No angular nonzero gate or weight scales the
baseline, and the amplitude is the independently proved raw baseline56. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalPrimary.OriginalRawBaselineRealizationApplication
open OriginalRawPrimaryRealizationApplication
private def output := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual
private def old := `JanetCartan.PhysicalPairs.OriginalBaselineNode
private def waves := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geometry := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def publish (key : Name) (p : Array Expr) (value target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "raw baseline differential: unresolved field {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "raw baseline differential: missing metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := output ++ key
  IO.println s!"checking unscaled raw baseline {key}/{p.size}"
  (← IO.getStdout).flush
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Literal unscaled BEFORE-B baseline at the SAME original outer node, including zero inner angular labels: its raw Jacobian has the unchanged ordinary carrier factor and actual raw baseline56 matrix. No corrected derivative identity, new source, weight, phase, or profile hypothesis is used (main:eq:primary-strain)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "raw baseline differential: nonstandard axioms {name}: {axioms}"
  logInfo m!"checked unscaled raw baseline {key}/{p.size}: {axioms}"
/-- Open the original outer-node telescope without repeatedly substituting
its entire remaining body. Every binder domain and theorem remains identical. -/
private def baselineTelescope (type : Expr)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop 57 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => next p (type.instantiateRev p)
    | k+1, type, p => do
      let .forallE key domain body bi := type.consumeMData |
        throwError "raw baseline differential: outer57 ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl key bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate key bi domain fun x => loop k body (p.push x)

elab "check_actual_raw_baseline_differential " mode:num : command => liftTermElabM do
  let statement := old ++ `native_demodulation_statement
  baselineTelescope (← getConstInfo statement).type fun p _ => do
    unless p.size == 57 do throwError "raw baseline differential: original outer57 changed"
    forallBoundedTelescope (← bodyAt (app statement p)) (some 2) fun xy _ => do
      let metadata ← bodyAt (app (old ++ `native_demodulation) (p ++ xy))
      unless metadata.isAppOf `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude_eq_demodulated do
        throwError "raw baseline differential: original retained regularity spine changed"
      let known ← arguments metadata
      let w ← get known `w
      unless w.isAppOfArity ``Prod.mk 4 do throwError "raw baseline differential: original outer point changed"
      let c := w.getAppArgs[3]!
      let z ← mkAppM ``Prod.fst #[c]
      let proof ← applyNamed `JanetCartan.Sampling.RetainedBackground.background_differential_eq
        (#[(`x,xy[0]!),(`z,z)] ++ known)
      let type ← inferType proof
      unless type.isAppOfArity ``Eq 3 do throwError "raw baseline differential: raw retained derivative changed"
      let sides := type.getAppArgs
      let matrix := sides[1]!
      unless (matrix.find? (·.isAppOfArity
          `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix 2)).isSome do
        throwError "raw baseline differential: original raw matrix conversion changed"
      let some derivative := matrix.find? (·.isAppOf ``fderiv) |
        throwError "raw baseline differential: not the original differential"
      let da := derivative.getAppArgs
      let raw := da[da.size-2]!
      unless (raw.find? (·.isAppOf `JanetCartan.RawPrimary.fullPrimaryAtom)).isSome do
        throwError "raw baseline differential: derivative is not the original raw atom"
      let named := app (output ++ `baseline_wave) p[:56].toArray
      if mode.getNat == 0 then
        publish `baseline_wave p[:56].toArray raw (← inferType raw) true
      else if mode.getNat == 1 || mode.getNat == 4 then
        let namedDerivative := mkAppN derivative.getAppFn (da.set! (da.size-2) named)
        let lhs := matrix.replace fun e => if e == derivative then some namedDerivative else none
        let rhs := sides[2]!
        unless rhs.isAppOfArity ``HSMul.hSMul 6 do throwError "raw baseline differential: carrier factor changed"
        let amplitude := mkApp (app `JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles.baseline p[:56].toArray) xy[0]!
        let rhs := mkAppN rhs.getAppFn (rhs.getAppArgs.set! 5 amplitude)
        let all := p ++ xy
        if mode.getNat == 1 then
          publish `baseline_factor_statement all (← mkEq lhs rhs) (mkSort .zero) true
        else
          publish `baseline_factor all proof (app (output ++ `baseline_factor_statement) all)
      else
        let T ← get known `T
        unless T.isAppOfArity (waves ++ `T) 53 do
          throwError "raw baseline differential: same source53 family changed"
        let source := T.getAppArgs
        let hc := app (geometry ++ `outer_weight_parameter) (source ++ p[52:57].toArray)
        if mode.getNat == 2 then
          let smooth := app (waves ++ `raw_on_source_chart) (source ++ #[c,hc])
          let target ← inferType smooth
          unless target.isAppOfArity ``ContDiffOn 11 do throwError "raw baseline differential: source chart changed"
          let target := mkAppN target.getAppFn (target.getAppArgs.set! 9 named)
          publish `baseline_smooth_on_source p smooth target
        else if mode.getNat == 3 then
          let native := app (waves ++ `outer_active_raw) (source ++ p[52:57].toArray)
          publish `baseline_eq_original_raw p (← mkEqRefl named) (← mkEq named native)
        else throwError "raw baseline differential: unknown stage"
end JanetCartan.PhysicalPrimary.OriginalRawBaselineRealizationApplication
end
