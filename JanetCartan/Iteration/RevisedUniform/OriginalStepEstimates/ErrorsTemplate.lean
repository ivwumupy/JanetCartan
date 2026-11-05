module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.NormsTemplate
public import JanetCartan.Iteration.RevisedUniform.OriginalSelectedMeanStep
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanResidualCore
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# Use the actual mean and pair errors on the same final core

These term-building helpers apply the original requested mean precision and
the actual pair metric lag. The pair estimate is restricted by the existing
containment of the final common core in the physical core; no cutoff, primary,
self tensor or residual is redefined. The execution leaf must import the
actual pair-core theorem. Consumer: `main:thm:step` through
`OriginalStepEstimates.increment_estimates_of_source_profiles`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate

open Lean Meta Elab Command

private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p
private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ value body _ => head (body.instantiate1 value)
  | value => value
private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

/-- Apply the already proved requested precision on its original final core,
with the same Picard count used by all norm and source fields. -/
def originalMeanError (selected : Array Expr) (J count meanOrder : Expr)
    (hAux hPrecision hError hMoment hFrame : Expr) : MetaM Expr := do
  unless selected.size == 52 do throwError "actual step mean error: selected52 changed"
  let accuracy ← termWith [(`q,meanOrder)] "(q : ℝ)"
  let first := selected[:33].toArray ++ #[accuracy] ++ selected[33:].toArray ++
    #[hAux,hPrecision,hError,hMoment]
  unless first.size == 57 do throwError "actual step mean error: precision prefix57 changed"
  let bound := app `JanetCartan.RevisedUniform.OriginalSelectedMeanStep.mean_error_le_requested_precision first
  let result ← forallBoundedTelescope (← inferType bound) (some 2) fun point atFrame => do
    unless point.size == 2 && atFrame.isForall do
      throwError "actual step mean error: original point/core/frame boundary changed"
    let proof := mkAppN bound (point.push hFrame)
    let target ← inferType proof
    let sameMean := app `JanetCartan.PhysicalMean.OriginalSelectedMeanData.physicalMean
      (selected ++ #[J,count])
    let some actualMean := target.find?
        (·.isAppOfArity `JanetCartan.PhysicalMean.OriginalSelectedMeanData.physicalMean 54)
      | throwError "actual step mean error: the original physical mean disappeared"
    -- The requested-precision producer forms accuracy+1 internally. Its
    -- elaborated coercion can differ syntactically from the same supplied
    -- finite count, so check the unchanged arguments by definitional equality.
    for i in [:54] do
      unless actualMean.getAppArgs[i]! == sameMean.getAppArgs[i]! do
        unless ← isDefEq actualMean.getAppArgs[i]! sameMean.getAppArgs[i]! do
          throwError "actual step mean error: different original mean operand {i}"
    mkLambdaFVars point proof
  return result

private def restrictOriginalPhysicalCore (native : Array Expr) (bound target : Expr) : MetaM Expr := do
  let fixed := native[:44].toArray
  let core := app `JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCore.core fixed
  let subset := Expr.proj ``And 1
    (app `JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCore.core_subsets fixed)
  forallBoundedTelescope target (some 1) fun point onPhysical => do
    unless point.size == 1 && onPhysical.isForall do
      throwError "actual step residual: original physical-core point boundary changed"
    let x := point[0]!
    let domain ← termWith [(`x,x),(`D,core)] "x ∈ D"
    withLocalDeclNoLocalInstanceUpdate `hxFinal .default domain fun hx => do
      let physical := mkAppN subset #[x,hx]
      let proof := mkAppN bound #[x,physical]
      mkLambdaFVars #[x,hx] proof

/-- Restrict the actual complete signed metric lag to the already selected
final core. The source/physical domain is not replaced or shrunk. -/
def originalPairError (selected native : Array Expr) (count Cscale delta pairOrder : Expr)
    (hAux hSigned : Expr) : MetaM Expr := do
  unless selected.size == 52 && native.size == 50 do
    throwError "actual step pair error: selected52/native50 changed"
  let args := selected ++ #[hAux,count,Cscale,hSigned,delta,pairOrder]
  let bound := app `JanetCartan.PhysicalPairs.OriginalSelectedPairCore.metric_lag args
  restrictOriginalPhysicalCore native bound (← inferType bound)

/-- Instantiate the actual primary-strain producer on the same original
source/Picard count, and use the same final-core containment as for the pair.
The execution leaf imports its actual checked producer. -/
def originalPrimaryError (selected native : Array Expr) (count delta primaryOrder : Expr)
    (hAux hOperator hDelta : Expr) : MetaM Expr := do
  unless selected.size == 52 && native.size == 50 do
    throwError "actual step primary error: selected52/native50 changed"
  let hDeltaNonneg ← mkAppM ``le_of_lt #[hDelta]
  let args := selected ++ #[hAux,hOperator,count,primaryOrder,delta,hDeltaNonneg]
  let bound := app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.strain_bound args
  let statement := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.strain_statement
  let result := head (← inferType bound)
  unless result.isAppOfArity statement 58 do
    throwError "actual step primary error: original strain statement58 changed"
  let some body := (← getConstInfo statement).value? (allowOpaque := true)
    | throwError "actual step primary error: original strain statement body is not exposed"
  -- Only unfold this named proposition's head. The physical fields, prices
  -- and original-data choices remain opaque operands of the same bound.
  let target := head (body.beta result.getAppArgs)
  unless target.isForall do
    throwError "actual step primary error: original pointwise strain body changed"
  restrictOriginalPhysicalCore native bound target

end JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate
end
