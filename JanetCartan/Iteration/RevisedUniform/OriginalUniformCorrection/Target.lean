module

public import JanetCartan.Iteration.RevisedUniform.OriginalMetricPreparation
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# The original metric family for the final uniform correction

The consumer is the unchanged Euclidean obligation in `Main.lean`.  Use the
same original coordinates, dilation, reference and compact core as the physical
source construction.  The final initial threshold is a parameter of the
already-proved coordinate reduction: it need not equal the older preliminary
threshold.  Actual construction of `UniformHistoryCorrection` is still a
separate obligation (`main:thm:main`, `main:eq:displacement-budget`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RevisedUniform.OriginalUniformCorrection

/-- The original metric after the already selected coordinate normalization
and the same reference dilation.  No new target is selected at a stage. -/
def targetFamily (d : ℕ) (hn : 5 ≤ d + 1)
    (g : MetricField (d + 1)) (V : Set (Euclidean (d + 1)))
    (hV : IsOpen V) (h0 : (0 : Euclidean (d + 1)) ∈ V)
    (hg : IsRiemannianMetricOn g V) : ℝ → MetricField (d + 1) :=
  fun s ↦ scaledMetric
    (coordinatePullback g (@OriginalMetricPreparation.metricCoordinates d hn g V hV h0 hg))
    (s * OriginalSelectedPrehistory.sigma d hn)

end JanetCartan.RevisedUniform.OriginalUniformCorrection
end

public meta section
namespace JanetCartan.RevisedUniform.OriginalUniformCorrectionTargetTemplate
open Lean Meta Elab Command

run_meta do
  let source := `JanetCartan.RevisedUniform.OriginalMetricPreparation.metricChartDilation_reduction
  let preparation := `JanetCartan.RevisedUniform.OriginalMetricPreparation
  let prehistory := `JanetCartan.RevisedUniform.OriginalSelectedPrehistory
  let app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p
  forallBoundedTelescope (← getConstInfo source).type (some 7) fun fixed _ => do
    unless fixed.size == 7 do throwError "original uniform target: metric boundary changed"
    let cap := app (preparation ++ `metricCap) fixed
    let hcap := app (preparation ++ `metricCap_spec) fixed
    let hpos := Expr.proj ``And 0 hcap
    let hchart := Expr.proj ``And 1 (Expr.proj ``And 1 hcap)
    let kMin := app (prehistory ++ `kMin) #[fixed[0]!]
    let B := mkConst `JanetCartan.PhysicalMean.OriginalCanonicalStaticReach.historyBand
    let reducer := app source (fixed ++ #[cap,hpos,hchart,kMin,B])
    forallBoundedTelescope (← inferType reducer) (some 3) fun thresholds _ => do
      unless thresholds.size == 3 do throwError "original uniform target: final threshold/price boundary changed"
      let gap := app (prehistory ++ `kMin_cubic) #[fixed[0]!]
      let proof := mkAppN reducer (thresholds.push gap)
      let target ← inferType proof
      unless target.isForall &&
          target.bindingDomain!.isAppOf `JanetCartan.RevisedGlobal.UniformHistoryCorrection do
        throwError "original uniform target: actual same-data correction premise disappeared"
      let type ← mkForallFVars (fixed ++ thresholds) target
      let value ← mkLambdaFVars (fixed ++ thresholds) proof
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
          throwError "original uniform target: unresolved original data"
      let (type,value) := Lean.ShareCommon.shareCommon (type,value)
      let name := `JanetCartan.RevisedUniform.OriginalUniformCorrection.local_metric_of_uniform_correction
      addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      addDocStringCore name "Restore the original coordinates after the genuine uniform correction on the SAME dimension-only reference/core and original metric family. The initial threshold is arbitrary and fixed; the existing cap and cubic-order witnesses are supplied internally, with no new geometry or analytic premise beyond the explicit UniformHistoryCorrection (main:thm:main)."
      let axioms ← collectAxioms name
      unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
        throwError "original uniform target: nonstandard axioms {axioms}"
      logInfo m!"original uniform target: arbitrary final initial threshold, {axioms}"
end JanetCartan.RevisedUniform.OriginalUniformCorrectionTargetTemplate
end
