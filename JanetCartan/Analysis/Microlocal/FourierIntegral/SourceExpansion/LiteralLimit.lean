module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.LiteralLimit.Frequency
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.LiteralKernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization

/-!
# Removing compact frequency cutoffs on actual graph tests

For `app:ch_regular_base:thm:actual-calculus`, Step 1, the literal iterated
integral converges pointwise after removal of a genuine compact frequency
cutoff. Source integration by parts uses exactly the fixed reserve `n+2`,
including derivatives of the test function and all cutoffs already in `A`.
The consumer is `graphTestOutput_eq_of_strong_regularization_limit` and the
final literal realization of the source Fourier expansion.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ}

/-- Absolute integrability in physical frequency after the original source
integration on an actual graph test. Its proof uses source integration by
parts and the test-product Leibniz bound, without any graph L² estimate
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem integrable_graphTest_sourceIntegral
    (_hn : 0 < n) {R : ℝ} (A : FullAmplitude n r)
    (_hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2)) (μ : ℕ) {B : ℝ}
    (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (S : Euclidean n → Euclidean n → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (u : graphTestSpace n r) (x : Euclidean n) :
    Integrable (fun η ↦ ∫ y, graphOscillation S x y η •
      (A x y η).mulVec ((u.val y).ofLp)) := by
  exact integrable_graph_sourceIntegral A hA μ hb S hS.continuous
    (fun y ↦ (u.val y).ofLp) (PiLp.contDiff_ofLp.comp u.property.1)
    (u.property.2.comp_left rfl) x

private theorem graph_sourceIntegral_frequency_smul
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (v : Euclidean n → Fin r → ℂ) (θ : Euclidean n → ℂ) (x η : Euclidean n) :
    (∫ y, graphOscillation S x y η • (θ η • A x y η).mulVec (v y)) =
      θ η • ∫ y, graphOscillation S x y η • (A x y η).mulVec (v y) := by
  simp only [Matrix.smul_mulVec, smul_comm (graphOscillation S x _ η) (θ η), integral_smul]

/-- Pointwise removal of smooth compact frequency cutoffs in the literal full
amplitude graph integral, with physical covectors and unchanged `(2π)⁻ⁿ`
normalization. The integrable majorant follows from the fixed `n+2` source
reserve and actual test-product derivatives, not from a graph operator bound.
Consumed by `graphTestOutput_eq_of_strong_regularization_limit`
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem tendsto_graphTestOutput_frequency_cutoff
    (hn : 0 < n) {R : ℝ} (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2)) (μ : ℕ) {B : ℝ}
    (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (S : Euclidean n → Euclidean n → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (θ : ℕ → Euclidean n → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (_hθc : ∀ j, HasCompactSupport (θ j)) (hθb : ∀ j η, ‖θ j η‖ ≤ 1)
    (hθlim : ∀ η, Tendsto (fun j ↦ θ j η) atTop (𝓝 1))
    (u : graphTestSpace n r) (x : Euclidean n) :
    Tendsto (fun j ↦ graphTestOutput S (fun x y η ↦ θ j η • A x y η) u x)
      atTop (𝓝 (graphTestOutput S A u x)) := by
  let F := fun η ↦ ∫ y, graphOscillation S x y η • (A x y η).mulVec ((u.val y).ofLp)
  have hF : Integrable F := integrable_graphTest_sourceIntegral hn A hs hA μ hb S hS u x
  have ht : Tendsto (fun j ↦ ∫ η, θ j η • F η) atTop (𝓝 (∫ η, F η)) := by
    apply tendsto_integral_of_dominated_convergence (fun η ↦ ‖F η‖)
    · intro j
      exact (hθ j).continuous.aestronglyMeasurable.smul hF.aestronglyMeasurable
    · exact hF.norm
    · intro j
      exact Eventually.of_forall fun η ↦ by
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_right (hθb j η) (norm_nonneg _)).trans_eq (one_mul _)
    · exact Eventually.of_forall fun η ↦ by simpa using (hθlim η).smul_const (F η)
  have ht' := ht.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)
  have ht'' := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).tendsto
    (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, F η) |>.comp ht'
  simpa only [graphTestOutput, graphOperator, graph_sourceIntegral_frequency_smul, F, Function.comp_def] using ht''

end JanetCartan.FourierIntegral.SourceExpansion
