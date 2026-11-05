module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.NormsTemplate
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ThresholdsTemplate
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairGates
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairProfiles.StaticCosts
public meta import Lean

/-!
# The actual step coefficient before the history

The common coefficient is formed from the original CP/CV/CS families and
their existing L² scalar, the same smoother's two costs, the original signed
lag coefficient, and the actual background coefficient. Only the pending
primary-strain coefficient is supplied to this independent deduction.
Its actual producer is `OriginalSelectedPrimaryStrain`.

This is elaboration metadata for `step_of_primary_strain`, not an additional
analytic hypothesis record (`main:thm:step`, `main:prop:current-scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate

open Lean Meta Elab Command

private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

/-- Construct the literal coefficient and its nonnegativity proof on fixed7,
the correction order and the primary-strain price, before any history.
The mean and signed coefficients come from their original static producers. -/
def originalStepCost (fixed dimension selected33 : Array Expr) (k Cstrain : Expr) :
    MetaM (Expr × Expr) := do
  unless fixed.size == 7 && dimension.size == 2 && selected33.size == 33 do
    throwError "actual step cost: changed original static metric/geometry boundary"
  let n := mkApp (mkConst ``Nat.succ) dimension[0]!
  let order (key : Name) := app (`JanetCartan.RevisedUniform.OriginalUniformCorrection ++ key) #[n,k]
  let m := order `smoothingOrder
  let hm := Expr.proj ``And 0
    (app `JanetCartan.RevisedUniform.OriginalUniformCorrection.orders_spec #[n,k])
  let meanOrder := order `meanOrder
  let accuracy ← termWith [(`q,meanOrder)] "(q : ℝ) + 1"
  let count := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.precisionSteps #[n,accuracy]
  let early := selected33.push count
  let one ← mkNumeral (mkConst ``Real) 1
  let hCap := app `JanetCartan.PhysicalPairs.OriginalSelectedPairGates.history_covers_size #[dimension[0]!]
  let CP := app `JanetCartan.RevisedUniform.OriginalSelectedPrimaryNorms.CP early
  let CV := app `JanetCartan.PhysicalMean.OriginalSelectedMeanProfiles.CphysicalMean early
  let (lag,_,CS,_) ← PhysicalPairs.OriginalSelectedPairProfiles.StaticCosts.rawCosts
    selected33 count one hCap
  let Cpair := mkApp lag (order `pairOrder)
  let (CPL2,_) ← originalPrimaryL2Witness early
  let Csmall := app `JanetCartan.RevisedUniform.OriginalUniformCorrection.CsmoothingSmall
    (fixed ++ #[m,hm])
  let Cfast := app `JanetCartan.RevisedUniform.OriginalUniformCorrection.CsmoothingHigh
    (fixed ++ #[m,hm])
  let m0 := app `JanetCartan.RevisedScales.baselineOrder #[n]
  let hi ← mkAppM ``HAdd.hAdd #[m0,order `cutoffOrder]
  let costs ← termWith [(`Csmall,Csmall),(`Cfast,Cfast),(`Cstrain,Cstrain),(`Cpair,Cpair),
      (`CP,CP),(`CV,CV),(`CS,CS),(`CPL2,CPL2),(`m0,m0)]
    "(![Csmall, Cfast, Cstrain, Cpair, CP m0, CV m0, CS m0, CPL2, CV 0 + CS 0] : Fin 9 → ℝ)"
  let C := app `JanetCartan.RevisedUniform.OriginalStepEstimates.lowerConstant #[costs]
  let hC := app `JanetCartan.RevisedUniform.OriginalStepEstimates.lowerConstant_nonneg #[costs]
  let CH ← termWith [(`CP,CP),(`CV,CV),(`CS,CS),(`hi,hi)] "CP hi + CV hi + CS hi"
  let CF := app `JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles.CF dimension
  let value := app `JanetCartan.RevisedUniform.OriginalStepEstimates.finalConstant #[n,C,CF,CH]
  let proof := app `JanetCartan.RevisedUniform.OriginalStepEstimates.finalConstant_nonneg #[n,C,CF,CH,hC]
  return (value,proof)

end JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate
end
