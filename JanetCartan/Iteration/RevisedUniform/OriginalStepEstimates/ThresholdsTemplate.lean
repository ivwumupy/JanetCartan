module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ActualBasics
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.SmoothingCosts
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# The five original current-stage thresholds

Prepare the fixed-metric, accuracy-dependent maximum for the actual physical
step. Every entry comes from an existing original producer: source preparation,
the same finite-moment smoother, target tensor regularity, requested mean
precision, and the original frame constant. Initial geometry and signed-size
gates stay in `Tpair`; none is paid at the current scale instead
(`main:thm:step`, `main:prop:current-scale`, `new:sec:order-of-choices`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

/-- The exact five fixed-metric frequency data, before every physical
history. The current source/tensor/precision declarations are supplied by
their original selection module at the execution site. -/
def originalStageFrequencies (fixed dimension : Array Expr) (k : Expr) : MetaM (Array Expr) := do
  unless fixed.size == 7 && dimension.size == 2 do
    throwError "actual step frequency: original metric7/dimension2 changed"
  let n := mkApp (mkConst ``Nat.succ) dimension[0]!
  let m := app (root ++ `smoothingOrder) #[n,k]
  let hm := Expr.proj ``And 0 (app (root ++ `orders_spec) #[n,k])
  let q := app (root ++ `meanOrder) #[n,k]
  let accuracy ← withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith [(`q,q)] "(q : ℝ) + 1")
  let preparation := app (root ++ `preparationFrequency) (fixed.push k)
  let smoothing := app (root ++ `smoothingFrequency) (fixed ++ #[m,hm])
  let tensor := app (root ++ `tensorFrequency) (dimension ++ #[m,hm])
  let precision := app (root ++ `precisionFrequency) (dimension.push accuracy)
  let frame := app `JanetCartan.UniformStep.projectedStressResidualConstant #[n,dimension[1]!]
  return #[preparation,smoothing,tensor,precision,frame]

end JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate
end
