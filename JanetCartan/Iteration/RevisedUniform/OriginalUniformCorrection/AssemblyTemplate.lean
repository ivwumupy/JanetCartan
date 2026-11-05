module

public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.Target
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairInitial
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# Final assembly on the original metric and history

This elaboration helper applies the actual `OriginalStepEstimates.step` to
the exact `RevisedGlobal.UniformHistoryCorrection.correction` binder. The
original-data initial and current-scale gates are supplied by `Tpair` and
`T_reaches`. It creates no mathematical assumption or intermediate success
record. Execution requires the actual, axiom-checked `C`, `C_nonneg`, `T` and
`step` declarations to have been imported.

Consumers are `main:thm:step`, `main:prop:current-scale` and the unchanged
Euclidean obligation for `main:thm:main` in `Main.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalUniformCorrectionAssemblyTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def stepRoot := `JanetCartan.RevisedUniform.OriginalStepEstimates
private def prehistory := `JanetCartan.RevisedUniform.OriginalSelectedPrehistory
private def preparation := `JanetCartan.RevisedUniform.OriginalMetricPreparation
private def pairInitial := `JanetCartan.PhysicalPairs.OriginalSelectedPairInitial
private def uniformName := `JanetCartan.RevisedGlobal.UniformHistoryCorrection
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def termWith (bindings : List (Name × Expr)) (code : String)
    (target? : Option Expr := none) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code target?)

private def checkedProducer (name : Name) : MetaM Unit := do
  let _ ← getConstInfo name
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual uniform correction: unfinished producer {name}: {axioms}"

private def save (key : Name) (fixed : Array Expr) (proof target : Expr)
    (documentation : String) : MetaM Unit := do
  unless fixed.size == 7 do
    throwError "actual uniform correction: an extra geometric or analytic input entered {key}"
  let type ← instantiateMVars (← mkForallFVars fixed target)
  let value ← instantiateMVars (← mkLambdaFVars fixed proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual uniform correction: unresolved or additional input in {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do
      throwError "actual uniform correction: unavailable original producer {missing.toList}"
  let name := root ++ key
  if (env.find? name).isSome then
    throwError "actual uniform correction: duplicate declaration {name}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name documentation
  checkedProducer name
  logInfo m!"actual original uniform correction {key}/7: {← collectAxioms name}"

/-- Build the exact final proof term from its five fixed-metric producer
terms. The actual publication supplies the named original producers; the
Scratch conditional audit supplies local theorem parameters to check this
same 21-to-13 assembly without declaring any additional production theorem. -/
def correctionTerm (fixed : Array Expr) (C hC T T_reaches step : Expr) :
    MetaM (Expr × Expr) := do
  unless fixed.size == 7 do
    throwError "actual uniform correction: changed original dimension/metric7"
  let dh := fixed[:2].toArray
  let one ← mkNumeral (mkConst ``Real) 1
  let initial := app (pairInitial ++ `Tpair) (dh.push one)
  let reducer := app (root ++ `local_metric_of_uniform_correction)
    (fixed ++ #[initial,C,T])
  let reductionType ← inferType reducer
  unless reductionType.isForall &&
      reductionType.bindingDomain!.isAppOfArity uniformName 11 do
    throwError "actual uniform correction: original coordinate consumer changed"
  let raw := reductionType.bindingDomain!.getAppArgs
  let uniformArgs := raw.set! 2 (app (prehistory ++ `Gmap) dh)
    |>.set! 4 (app (root ++ `targetFamily) fixed)
  unless raw[8]! == initial && raw[9]! == C && raw[10]! == T do
    throwError "actual uniform correction: the final threshold or common C/T changed"
  let target := app uniformName uniformArgs
  let staticProofs := #[
    app (prehistory ++ `D_isCompact) dh,
    Expr.proj ``And 0 (app (preparation ++ `metricCap_spec) fixed),
    mkConst `JanetCartan.PhysicalMean.OriginalCanonicalStaticReach.one_le_historyBand,
    app (pairInitial ++ `two_le_Tpair) (dh.push one),hC]
  let constructor := app (uniformName ++ `mk) (uniformArgs ++ staticProofs)
  let afterStatic ← inferType constructor
  unless afterStatic.isForall do
    throwError "actual uniform correction: missing correction field"
  let correction ← forallTelescopeReducing afterStatic.bindingDomain! fun p expected => do
    unless p.size == 13 && expected.isAppOfArity ``Exists 2 do
      throwError "actual uniform correction: changed original thirteen stage binders"
    let initialReaches := app (pairInitial ++ `initial_reaches)
      (dh ++ #[one,p[0]!,p[6]!])
    let hOld ← mkAppM ``le_trans #[
      app `JanetCartan.RevisedUniform.OriginalFinalReach.oldTref_le_Tfinal dh,
      Expr.proj ``And 0 initialReaches]
    let R := app `JanetCartan.iterationScale
      #[p[0]!,mkConst `JanetCartan.growthExponent,p[2]!]
    let reaches := mkAppN T_reaches #[p[3]!,R,p[10]!]
    let hPreparation := Expr.proj ``And 0 reaches
    let arguments := #[p[0]!,hOld,p[2]!,p[4]!,p[5]!,p[11]!,
      p[1]!,p[7]!,p[8]!,p[3]!,hPreparation,p[12]!,p[6]!,p[10]!]
    unless fixed.size + arguments.size == 21 do
      throwError "actual uniform correction: changed original step21 application"
    let originalProof := mkAppN step arguments
    let actualType ← inferType originalProof
    unless actualType.isAppOfArity ``Exists 2 do
      throwError "actual uniform correction: the step still asks for an analytic input"
    -- Keep the SAME existential witness. Components writes the literal band
    -- two and -(2*k); UHC names historyBand and writes -2*k.
    let proof ← if ← isDefEq actualType expected then pure originalProof else
      termWith [(`hStep,originalProof)]
        "(by\n  rcases hStep with ⟨U, hBand, hL2, hMetric⟩\n  refine ⟨U, ?_, hL2, ?_⟩\n  · simpa only [JanetCartan.PhysicalMean.OriginalCanonicalStaticReach.historyBand] using hBand\n  · simpa only [neg_mul] using hMetric)"
        (some expected)
    mkLambdaFVars p proof
  return (mkApp constructor correction,target)

/-- Instantiate the checked actual-constant deduction with the genuine
step21 producer. The resulting theorem has only original metric inputs. -/
def publishCorrection : MetaM Unit := do
  for key in #[`C,`C_nonneg,`T,`T_reaches,`step] do
    checkedProducer (stepRoot ++ key)
  let deduction := root ++ `uniformCorrection_of_step
  checkedProducer deduction
  forallBoundedTelescope (← getConstInfo (preparation ++ `metricCap)).type (some 7)
      fun fixed result => do
    unless fixed.size == 7 && result.isConstOf ``Real do
      throwError "actual uniform correction: changed original dimension/metric7"
    let actualStep := app (stepRoot ++ `step) fixed
    let proof := app deduction (fixed.push actualStep)
    let target ← inferType proof
    unless target.isAppOfArity uniformName 11 &&
        target.getAppArgs[9]! == app (stepRoot ++ `C) fixed &&
        target.getAppArgs[10]! == app (stepRoot ++ `T) fixed do
      throwError "actual uniform correction: actual C/T changed in the checked deduction"
    unless proof.getUsedConstants.contains (stepRoot ++ `step) do
      throwError "actual uniform correction: actual step21 was not instantiated"
    save `uniformHistoryCorrection fixed proof target
      "The actual uniform history correction on the original dimension-only reference/core and the original normalized metric family. The fixed initial threshold is Tpair(d,hn,1); all current gates and common error/displacement prices come from the actual original-data C/T/step producers. No analytic or source-success hypothesis remains (main:thm:step; main:prop:current-scale; new:sec:order-of-choices)."

/-- The same original coordinate reduction used by actual publication and
by the Scratch conditional proof of the exact original-metric conclusion. -/
def localMetricTerm (fixed : Array Expr) (uniformProof : Expr) : MetaM (Expr × Expr) := do
  let uniform ← inferType uniformProof
  unless fixed.size == 7 && uniform.isAppOfArity uniformName 11 do
    throwError "actual uniform correction: unexpected remaining local-metric input"
  let args := uniform.getAppArgs
  let reducer := app (root ++ `local_metric_of_uniform_correction)
    (fixed ++ #[args[8]!,args[9]!,args[10]!])
  let proof := mkApp reducer uniformProof
  let target ← inferType proof
  unless target.isAppOfArity ``Exists 2 do
    throwError "actual uniform correction: no original Euclidean metric realization"
  return (proof,target)

/-- Apply the already proved coordinate/dilation reduction to the actual UHC,
thereby closing the Euclidean original-metric obligation in dimension d+1. -/
def publishLocalMetric : MetaM Unit := do
  let name := root ++ `uniformHistoryCorrection
  checkedProducer name
  forallBoundedTelescope (← getConstInfo name).type (some 7) fun fixed uniform => do
    unless fixed.size == 7 && uniform.isAppOfArity uniformName 11 do
      throwError "actual uniform correction: unexpected remaining local-metric input"
    let (proof,target) ← localMetricTerm fixed (app name fixed)
    save `local_metric fixed proof target
      "Every original smooth positive definite metric near zero in dimension d+1≥5 has a smooth local realization in the exact Janet–Cartan dimension, on an open neighborhood contained in its original domain. This applies the actual uniform history correction and restores the same original coordinates and metric (main:thm:main)."

end JanetCartan.RevisedUniform.OriginalUniformCorrectionAssemblyTemplate
end
