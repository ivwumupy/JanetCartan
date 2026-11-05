module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence.PrimitiveBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.TestReduction

/-!
# Matrix source tests of the original full normal amplitude

The literal frequency-cutoff kernels converge against two compact physical
tests, retaining both finite matrix sums and `k = 2πξ`. The limiting action is
exactly `reflectedMatrixTestAction`, before Taylor or diagonal completion.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n N : ℕ}

/-- The ORIGINAL reflected matrix kernel converges under compact source and
output tests. Primitive joint jets suffice; the theorem assumes no kernel
limit or Fourier integrability. The primitive producer is
`exists_reflected_source_bounds_of_primitiveNorms`.
Consumer: the full-amplitude limit in `realNormal_principal_reduction_of_test_limit`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem tendsto_integral_reflectedMatrixTestAction_cutoff
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (hc : ∀ i j : Fin n, ContDiff ℝ ∞ (fun p : Variables n ↦
      (reflectedSymbolAmplitude a J u Ω K (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)))
    (M : Fin n → Fin n → ℕ → ℝ)
    (hM : ∀ i j x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦
        (reflectedSymbolAmplitude a J u Ω K (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ))
        (x, y, ξ)‖ ≤ M i j k)
    (f v : Fin n → Euclidean n → ℂ)
    (hf : ∀ j, ContDiff ℝ (n + 1) (f j)) (hfc : ∀ j, HasCompactSupport (f j))
    (hv : ∀ i, Continuous (v i)) (hvc : ∀ i, HasCompactSupport (v i))
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχ0 : χ 0 = 1)
    (hχc : HasCompactSupport χ) {C : ℝ} (hC : ∀ ξ, |χ ξ| ≤ C) :
    Tendsto (fun R : ℝ ↦ ∫ x, ∑ i : Fin n, ∑ j : Fin n, v i x *
      ∫ y, f j y • amplitudeKernel (fun x y ξ ↦ χ (R⁻¹ • ξ) •
        (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) x y) atTop
      (𝓝 (∫ x, ∑ i : Fin n, v i x * reflectedMatrixTestAction a J u Ω K f x i)) := by
  let c := fun (i j : Fin n) x y ξ ↦
    (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)
  have hir (R : ℝ) (i j : Fin n) := integrable_test_fullAmplitudeOperator_cutoff
    (c i j) (hc i j) (f j) (hf j) (hfc j) (M i j) (hM i j) (v i) (hv i) (hvc i) χ hχ hC R
  have hi (i j : Fin n) := integrable_test_fullAmplitudeOperator
    (c i j) (hc i j) (f j) (hf j) (hfc j) (M i j) (hM i j) (v i) (hv i) (hvc i)
  have ht := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦
    tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun j _ ↦
      tendsto_integral_test_fullAmplitudeOperator_cutoff (c i j) (hc i j)
        (f j) (hf j) (hfc j) (M i j) (hM i j) (v i) (hv i) (hvc i) χ hχ hχ0 hC))
  have hsum (R : ℝ) :
      (∫ x, ∑ i : Fin n, ∑ j : Fin n, v i x *
        fullAmplitudeOperator (fun x y ξ ↦ χ (R⁻¹ • ξ) • c i j x y ξ) (f j) x) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, v i x *
        fullAmplitudeOperator (fun x y ξ ↦ χ (R⁻¹ • ξ) • c i j x y ξ) (f j) x := by
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hir R i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ ↦ hir R i j)
  have hsum₀ : (∫ x, ∑ i : Fin n, v i x * reflectedMatrixTestAction a J u Ω K f x i) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, v i x * fullAmplitudeOperator (c i j) (f j) x := by
    change (∫ x, ∑ i : Fin n, v i x * ∑ j : Fin n,
      fullAmplitudeOperator (c i j) (f j) x) = _
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ ↦ hi i j)
  rw [hsum₀]
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [← hsum R]
  apply integral_congr_ae
  filter_upwards [] with x
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  refine fullAmplitudeOperator_eq_integral_amplitudeKernel
    (fun x y ξ ↦ χ (R⁻¹ • ξ) • c i j x y ξ) (f j) x ?_
  exact integrable_frequency_cutoff_amplitude_test (c i j) (f j) _ x
    ((hc i j).continuous.comp (f := fun p : Euclidean n × Euclidean n ↦ (x, p.2, p.1))
      (by fun_prop)) (hf j).continuous (hfc j)
    (hχ.comp (continuous_const.smul continuous_id)) (hχc.comp_smul (inv_ne_zero hR.ne'))

end JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
