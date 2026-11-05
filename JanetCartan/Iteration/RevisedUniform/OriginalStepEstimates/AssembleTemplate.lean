module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ErrorsTemplate
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ActualBasics
public import JanetCartan.Iteration.RevisedUniform.Powers
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairInitial
public import JanetCartan.Iteration.PhysicalMean.OriginalNormalizedTargetProfiles
import all JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ActualBasics
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# Assemble the literal original physical step

This term builder discharges the numerical gates from the initial `Tpair`
and the original current-stage reaches, applies every original norm, mean
and pair producer, and supplies actual current-map differentiability. The
execution leaf supplies the original smoothing and primary-strain proof
terms. They are not added as mathematical hypotheses by this helper.

Consumer: the original-data `main:thm:step` and
`RevisedGlobal.UniformHistoryCorrection.correction`. Every eventual theorem
is kernel checked by its execution leaf.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate

open Lean Meta Elab Command

private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def tail (p : Expr) (i : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) i p
private def part (p : Expr) (i : Nat) := Expr.proj ``And 0 (tail p i)

private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

/-- The precise primary-strain input of the already checked component
consumer, with its norm instance and coercions retained literally. -/
def originalStrainInputType (n targetDimension F P D Cstrain delta R Qp : Expr) : MetaM Expr := do
  let input := `JanetCartan.RevisedUniform.OriginalStepEstimates.increment_estimates_of_source_profiles
  forallBoundedTelescope (← getConstInfo input).type (some 44) fun p _ => do
    unless p.size == 44 &&
        (← p[43]!.fvarId!.getDecl).userName.eraseMacroScopes == `hstrain do
      throwError "actual step strain interface: original component input changed"
    let type ← inferType p[43]!
    let keep := #[p[0]!,p[1]!,p[2]!,p[3]!,p[9]!,p[15]!,p[19]!,p[20]!,p[23]!]
    let interface ← mkLambdaFVars keep type
    if interface.hasFVar || interface.hasMVar || interface.hasLevelMVar || interface.hasSorry then
      throwError "actual step strain interface: an extra component was assumed"
    pure ((interface.beta #[n,targetDimension,F,P,D,Cstrain,delta,R,Qp]).headBeta)

/-- Return the original fields' exact finite-step proof. The proof-valued
arguments are actual producer outputs at the execution site, not additional
axioms or a public success contract. `Tpair` uses the fixed pair scale one. -/
def originalStepProof (dimension selected native a : Array Expr) (J : Expr)
    (hInitialPair hTensor hPrecision hFrame : Expr)
    (Csmall Cfast hSmall hFast Cstrain hStrain : Expr) : MetaM Expr := do
  unless dimension.size == 2 && selected.size == 52 && native.size == 50 && a.size == 10 do
    throwError "actual step assembly: changed original dimension/selected/native/source data"
  let n := app ``Nat.succ #[dimension[0]!]
  let targetDimension := app `JanetCartan.embeddingDimension #[n]
  unless ← isDefEq n a[0]! do
    throwError "actual step assembly: the original source dimension changed"
  unless ← isDefEq targetDimension a[1]! do
    throwError "actual step assembly: the original target dimension changed"
  -- Keep the source operands themselves unchanged. Only the two dimension
  -- parameters use the same spelling as the actual fields and early costs.
  let a := (a.set! 0 n).set! 1 targetDimension
  let R := a[4]!
  let delta := a[6]!
  let k := selected[49]!
  let order (key : Name) := app (`JanetCartan.RevisedUniform.OriginalUniformCorrection ++ key) #[n,k]
  let m := order `smoothingOrder
  let Qp := order `primaryOrder
  let Qm := order `meanOrder
  let q := order `pairOrder
  let kCut := order `cutoffOrder
  unless ← isDefEq selected[47]! m do
    throwError "actual step assembly: the finite smoother is not the original joint order"
  let accuracy ← termWith [(`Qm,Qm)] "(Qm : ℝ) + 1"
  let count := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.precisionSteps #[n,accuracy]
  let Cscale ← mkNumeral (mkConst ``Real) 1
  let initial := app `JanetCartan.PhysicalPairs.OriginalSelectedPairInitial.initial_reaches
    (dimension ++ #[Cscale,native[44]!,hInitialPair])
  let allInitial := app `JanetCartan.RevisedUniform.OriginalFinalReach.initial_gates
    (dimension ++ #[native[44]!,part initial 0])
  let hTwo := part allInitial 0
  let hError := part allInitial 3
  let hBuffer := part allInitial 5
  let hFullW := part allInitial 6
  let hAux := tail allInitial 7
  let hSize := part initial 1
  let hSigned := tail initial 2
  let hCap := app `JanetCartan.PhysicalPairs.OriginalSelectedPairGates.history_covers_size
    #[dimension[0]!]
  let facts := app `JanetCartan.RevisedUniform.iteration_scale_power_facts
    #[native[44]!,hTwo,native[46]!,k,n]
  let hR := part facts 0
  let hDelta := part facts 1
  let hDeltaOne := part facts 2
  let norms ← originalNormInputs selected native a J count Cscale kCut
    hAux hFullW hBuffer hTensor hSigned hCap hSize hDelta
  let moment := app `JanetCartan.PhysicalMean.OriginalNormalizedTargetProfiles.moment_le_Starget
    #[n,a[3]!,selected[47]!,selected[48]!]
  let hMoment ← mkAppM ``le_trans #[moment,hTensor]
  let meanError ← originalMeanError selected J count Qm hAux hPrecision hError hMoment hFrame
  let pairError ← originalPairError selected native count Cscale delta q hAux hSigned
  let Cpair := app `JanetCartan.PhysicalPairs.OriginalSelectedPairEstimates.Clag
    (selected[:33].toArray ++ #[count,Cscale,q])
  let CF := app `JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles.CF dimension
  let hCF := app `JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles.CF_nonneg dimension
  let D := app `JanetCartan.RevisedUniform.OriginalSelectedPrehistory.D dimension
  let F := app `JanetCartan.RevisedGlobal.finiteMap #[n,targetDimension,a[2]!,a[8]!,a[9]!]
  let eR := app `JanetCartan.PhysicalSmoothing.smoothedDefect (a[:6].toArray ++ a[7:].toArray)
  let hDF := app `JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles.current_first_derivative
    (dimension ++ #[native[44]!,hTwo,native[46]!,native[47]!,native[48]!,native[49]!])
  let everywhere := actualCurrentDifferentiable dimension[0]! dimension[1]! native[46]! native[47]!
  let hF ← withLocalDeclD `x (app `JanetCartan.Euclidean #[n]) fun x => do
    let membership ← termWith [(`x,x),(`D,D)] "x ∈ D"
    withLocalDeclD `hx membership fun hx => mkLambdaFVars #[x,hx] (mkApp everywhere x)
  let Q ← termWith [(`k,k)] "2 * (k : ℝ)"
  let budgets := actualAccuracyProofs n k
  let proof := app `JanetCartan.RevisedUniform.OriginalStepEstimates.increment_estimates_of_source_profiles #[
    n,targetDimension,F,norms.primaryField,norms.meanField,norms.signedField,a[7]!,eR,norms.fullSelf,D,
    norms.CP,norms.CV,norms.CS,Csmall,Cfast,Cstrain,Cpair,norms.CPL2,CF,delta,R,Q,
    m,Qp,Qm,q,kCut,norms.hCP,norms.hCV,norms.hCS,hCF,hDelta,hDeltaOne,hR,
    part budgets 0,part budgets 1,part budgets 2,part budgets 3,part budgets 4,tail budgets 5,
    hF,hSmall,hFast,hStrain,meanError,pairError,hDF,norms.primaryLow,norms.meanAll,norms.signedAll,
    norms.primaryL2,norms.primaryHigh]
  let type ← inferType proof
  unless (type.find? (·.isAppOf `JanetCartan.RevisedStage.increment)).isSome do
    throwError "actual step assembly: literal constructed increment lost"
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "actual step assembly: unresolved original producer application"
  return proof

end JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate
end
