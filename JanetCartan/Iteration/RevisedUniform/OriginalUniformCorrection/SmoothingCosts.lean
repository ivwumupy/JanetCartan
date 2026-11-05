module

public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.Target
public meta import JanetCartan.Iteration.RevisedUniform.OriginalMetricPreparationTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalMetricPreparationTemplate
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
# Fixed data for both original smoothing tails on the final common core

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
namespace JanetCartan.RevisedUniform.OriginalUniformSmoothingTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def tail (p : Expr) (i : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) i p
private def part (p : Expr) (i : Nat) := Expr.proj ``And 0 (tail p i)
private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ v b _ => head (b.instantiate1 v)
  | t => t
private def typePart (type : Expr) (i : Nat) : Expr :=
  (Nat.repeat (fun e => (head e).getAppArgs[1]!) i type).getAppArgs[0]!

private def choose (proof type : Expr) : MetaM (Expr × Expr × Expr) := do
  let type := head type
  unless type.isAppOfArity ``Exists 2 do
    throwError "original uniform smoothing: changed finite-moment existential"
  let witness := mkAppN (mkConst ``Classical.choose type.getAppFn.constLevels!)
    (type.getAppArgs.push proof)
  let spec := mkAppN (mkConst ``Classical.choose_spec type.getAppFn.constLevels!)
    (type.getAppArgs.push proof)
  return (witness,spec,head (type.getAppArgs[1]!.beta #[witness]))

/-- Read the existing interval's exact finite-moment witness.  This operation
never invokes a second existential selection for the target interval. -/
def withSmoothing (arguments : Array Expr) (m hm : Expr)
    (next : Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  let ci ← getConstInfo (forcing ++ `targetDilation)
  let some value := ci.value? (allowOpaque := true)
    | throwError "original uniform smoothing: original interval body unavailable"
  let original := head (value.beta arguments)
  unless original.isAppOfArity ``Classical.choose 3 do
    throwError "original uniform smoothing: original interval is not its selected witness"
  let intervalSpec := mkAppN (mkConst ``Classical.choose_spec original.getAppFn.constLevels!)
    original.getAppArgs
  let compactExists := tail intervalSpec 3
  let (_,compactSpec,_) ← choose compactExists (← inferType compactExists)
  let momentExists := mkAppN (tail compactSpec 2) #[m,hm]
  let mut proof := momentExists
  let mut type ← inferType momentExists
  let mut chosen := #[]
  for _ in [:5] do
    let (witness,spec,specType) ← choose proof type
    chosen := chosen.push witness
    proof := spec
    type := specType
  unless chosen.size == 5 do throwError "original uniform smoothing: missing actual finite data"
  next chosen proof type

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

def renameCosts (fixed : Array Expr) (m hm : Expr) (w : Array Expr) (e : Expr) : Expr :=
  let early := fixed ++ #[m,hm]
  e.replace fun t =>
    if t == w[0]! then some (app (root ++ `smoothingFrequency) early)
    else if t == w[3]! then some (app (root ++ `CsmoothingSmall) early)
    else if t == w[4]! then some (app (root ++ `CsmoothingHigh) early)
    else none

def publish (mode : Nat) : MetaM Unit := do
  unless mode < 7 do throwError "original uniform smoothing: unknown data/fact mode"
  OriginalMetricPreparationTemplate.withDimensionMetric fun d => do
    let fixed := d.dimension ++ d.metric
    let capSpec := app `JanetCartan.RevisedUniform.OriginalMetricPreparation.metricCap_spec fixed
    let capType := head (← inferType capSpec)
    unless capType.isAppOfArity ``And 2 && capType.getAppArgs[1]!.isAppOfArity ``And 2 do
      throwError "original uniform smoothing: original cap specification changed"
    let upper := capType.getAppArgs[1]!.getAppArgs[0]!
    unless upper.isAppOfArity ``LE.le 4 do
      throwError "original uniform smoothing: original physical cap bound disappeared"
    let interval := upper.getAppArgs[3]!
    unless interval.isAppOfArity (forcing ++ `targetDilation) 50 do
      throwError "original uniform smoothing: not the SAME original target interval"
    let arguments := interval.getAppArgs
    withLocalDeclD `m (mkConst ``Nat) fun m => do
      withLocalDeclD `hm (← mkAppM ``LE.le #[mkNatLit 1,m]) fun hm => do
        withSmoothing arguments m hm fun chosen spec type => do
          let early := fixed ++ #[m,hm]
          if mode < 3 then
            let (key,index) := #[(`smoothingFrequency,0),(`CsmoothingSmall,3),(`CsmoothingHigh,4)][mode]!
            save key early chosen[index]! (mkConst ``Real)
          else
            let (key,index) := #[(`smoothingFrequency_two_le,0),(`smoothingFrequency_moment_le,1),
              (`CsmoothingSmall_nonneg,4),(`CsmoothingHigh_nonneg,5)][mode-3]!
            let proof := part spec index
            save key early proof (renameCosts fixed m hm chosen (typePart type index)) false

run_meta publish 0
run_meta publish 1
run_meta publish 2
run_meta publish 3
run_meta publish 4
run_meta publish 5
run_meta publish 6


end JanetCartan.RevisedUniform.OriginalUniformSmoothingTemplate
end

#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.smoothingFrequency
#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.CsmoothingSmall_nonneg
#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.CsmoothingHigh_nonneg
