module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence.MatrixTests
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence.RegularizedBounds

/-!
# The original radial carrier limit with both matrix sums

The source-first limit of `app:ch_background:eq:bg-full-complex-amplitude`
retains the full normalized reflected matrix action, before Taylor reduction.
The uniform jets below are produced by
`exists_reflected_regularized_source_bounds_of_primitiveNorms`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n N : ℕ}

/-- The ORIGINAL matrix amplitude with the squared radial carrier cutoff
converges under compact physical tests. Both matrix sums, the reflection and
`k = 2πξ` are retained. No source Fourier integrability or normal identity is
an input. The parent construction supplies the actual geometry and identifies
these Euclidean integrals with its torus test pairing
(`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem tendsto_integral_reflectedMatrixTestAction_carrierCutoff
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ : ℝ → ℝ) (hχ : ∀ t ∈ Icc (0 : ℝ) 1, χ t = 1)
    {Cupper : ℝ} (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (hc : ∀ R : ℝ, 1 ≤ R → ∀ i j : Fin n,
      ContDiff ℝ ∞ (fun p : Variables n ↦
        (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
          (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)))
    (M : Fin n → Fin n → ℕ → ℝ)
    (hM : ∀ R : ℝ, 1 ≤ R → ∀ i j x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦
        (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
          (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)) (x, y, ξ)‖ ≤ M i j k)
    (f v : Fin n → Euclidean n → ℂ)
    (hf : ∀ j, ContDiff ℝ (n + 1) (f j)) (hfc : ∀ j, HasCompactSupport (f j))
    (hv : ∀ i, Continuous (v i)) (hvc : ∀ i, HasCompactSupport (v i)) :
    Tendsto (fun R : ℝ ↦ ∫ x, ∑ i : Fin n, v i x *
      reflectedMatrixTestAction (regularizedCoefficients a χ R) J u Ω K f x i) atTop
      (𝓝 (∫ x, ∑ i : Fin n, v i x * reflectedMatrixTestAction a J u Ω K f x i)) := by
  let c := fun (R : ℝ) (i j : Fin n) x y ξ ↦
    (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
      (x, y, (2 * Real.pi) • ξ) i j : ℂ)
  change Tendsto (fun R : ℝ ↦ ∫ x, ∑ i : Fin n, v i x *
    ∑ j : Fin n, fullAmplitudeOperator (c R i j) (f j) x) atTop
    (𝓝 (∫ x, ∑ i : Fin n, v i x * ∑ j : Fin n, fullAmplitudeOperator (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) (f j) x))
  simp_rw [Finset.mul_sum]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ ∑ i : Fin n, ∑ j : Fin n, ‖v i x‖ * ∫ ξ, sourceTestMajorant (f j) (M i j) ξ)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    apply Finset.aestronglyMeasurable_fun_sum
    intro j _
    exact (hv i).aestronglyMeasurable.mul
      (stronglyMeasurable_fullAmplitudeOperator (c R i j) (hc R hR i j).continuous
        (f j) (hf j).continuous).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    filter_upwards [] with x
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_fullAmplitudeOperator_le (c R i j) (hc R hR i j) (f j) (hf j) (hfc j)
        (M i j) (hM R hR i j) x) (norm_nonneg _)
  · apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact ((hv i).integrable_of_hasCompactSupport (hvc i)).norm.mul_const _
  · filter_upwards [] with x
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact tendsto_const_nhds.mul
      (tendsto_reflected_fullAmplitudeOperator_carrierCutoff a J u Ω K χ hχ hupper i j
        (fun R hR ↦ hc R hR i j) (M i j) (fun R hR ↦ hM R hR i j)
        (f j) (hf j) (hfc j) x)

end JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
