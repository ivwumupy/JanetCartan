module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.ActualStatic
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.Smoothing
public meta import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.AssemblyTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity

/-!
# The original uniform correction and local metric realization

The original finite-stage producers fill every field of the exact revised
uniform history correction. The existing iteration and coordinate reduction
then realize every original smooth positive definite metric near zero in the
unchanged Janet–Cartan target dimension (`main:thm:main`, `main:thm:step`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

run_meta JanetCartan.RevisedUniform.OriginalUniformCorrectionAssemblyTemplate.publishCorrection
run_meta JanetCartan.RevisedUniform.OriginalUniformCorrectionAssemblyTemplate.publishLocalMetric

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RevisedUniform.OriginalUniformCorrection

/-- The Euclidean original-metric input for the exact manifold Theorem 1.1,
in every dimension n≥5 (`main:thm:main`). -/
theorem exists_local_metric (n : ℕ) (hn : 5 ≤ n)
    (g : MetricField n) (V : Set (Euclidean n))
    (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ V)
    (hg : IsRiemannianMetricOn g V) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ (0 : Euclidean n) ∈ U ∧ U ⊆ V ∧
      ∃ F : Euclidean n → Euclidean (embeddingDimension n),
        ContDiffOn ℝ ∞ F U ∧ IsIsometricOn g F U := by
  cases n with
  | zero => omega
  | succ d => exact @local_metric d hn g V hV h0 hg

end JanetCartan.RevisedUniform.OriginalUniformCorrection
end

#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.uniformHistoryCorrection
#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.local_metric
#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.exists_local_metric
