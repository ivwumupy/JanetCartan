module

public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.SelectedInput
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.SmoothingTails
public import JanetCartan.Iteration.PhysicalSmoothing
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Both original smoothing tails on the final common core

Extract the finite-moment data from the very smoothing theorem that selected
`OriginalCompleteForcing.targetDilation`.  The metric interval, smoothing
domain, input defect and smoothed tensor are unchanged.  The threshold and
both constants precede every initial frequency, finite history and target
dilation.  The consumer is the two smoothing clauses of
`RevisedStage.increment_estimates_of_physicalSobolev_profiles`
(`main:lem:smoothing`, `main:eq:metric-two-errors` in `paper-v2.tex`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalUniformSmoothingApplication

open Lean Meta Elab Command
open OriginalUniformCorrectionTemplate

private def root := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args

private def save (key : Name) (parameters : Array Expr) (value target : Expr)
    (data := true) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars parameters target)
  let value ← instantiateMVars (← mkLambdaFVars parameters value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "original uniform smoothing: unresolved or additional analytic input {key}"
    let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
    unless missing.isEmpty do throwError "original uniform smoothing: missing {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual two-tail smoothing of the SAME original metric defect on the final common core, extracted from the identical targetDilation witness. The threshold and constants precede every history and target parameter; no new interval, smoother, tensor or smoothing-success premise (main:lem:smoothing; main:eq:metric-two-errors)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original uniform smoothing: nonstandard axioms {axioms}"
  logInfo m!"original uniform smoothing {key}/{parameters.size}: {axioms}"


run_meta do
  withSelectedStage fun stage => do
    let p := stage.selected52
    let m := p[47]!
    let hm := p[48]!
    let early := stage.parameters ++ #[m,hm]
    let S := app (root ++ `smoothingFrequency) early
    withLocalDeclD `hSmoothingFrequency (← mkAppM ``LE.le #[S,stage.scale]) fun hFrequency => do
      let hInitial := app `JanetCartan.RevisedUniform.OriginalSelectedPrehistory.two_le_Tref stage.dimension
      let hTwo ← mkAppM ``le_trans #[hInitial,stage.stageParameters[8]!]
      let hDelta := app (forcing ++ `prescribed_defect_pos) #[p[33]!,hTwo,p[35]!,p[49]!]
      let hs0 ← mkAppM ``le_of_lt #[stage.stageParameters[14]!]
      let hsCommon ← mkAppM ``And.intro #[hs0,stage.stageParameters[15]!]
      let arguments := early ++ #[p[45]!,hsCommon,p[33]!,hTwo,p[35]!,p[36]!,p[37]!,p[38]!,
        hFrequency,stage.delta,hDelta,p[51]!]
      let producer := root ++ `original_smoothing_bounds
      let both := app producer arguments
      let target ← instantiateForall (← getConstInfo producer).type arguments
      save `smoothing_bounds (stage.stageParameters.push hFrequency) both target false


end JanetCartan.RevisedUniform.OriginalUniformSmoothingApplication
end

#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.smoothing_bounds
