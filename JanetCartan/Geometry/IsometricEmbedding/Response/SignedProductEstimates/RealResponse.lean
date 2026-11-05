module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Sources
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Hermitian
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# The same real response and the complex full strain error

The fixed-response analytic endpoints use complex oscillatory sources. The
signed product in `app:ch_pairs:lem:pairs-ledger` is their real quadrature.
Here realification contracts the FULL strain error for the same response and
source cutoff. No estimate on that complex error is assumed or proved here;
its producer is the original fixed-response construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.SignedProductEstimates

open ResponseSourceExtension ResponseTransfer ResponseTransfer.SourceNegative

variable {n N : ℕ} {ι : Type*}

/-- Realification of the SAME complex response gives the complete real
strain error with Frobenius contraction (`app:ch_pairs:eq:pairs-lag-one-error`).
This transfers a future complex analytic estimate without changing the solver
or inserting an assumed bound for an individual signed source. -/
theorem norm_real_response_strain_error_le
    (F : Euclidean n → Euclidean N)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) {x : Euclidean n}
    (hB : DifferentiableAt ℝ (complexifyResponse B h) x) :
    ‖linearizedMetric F (B (tensorFieldRealPart h)) x - tensorFieldRealPart h x‖ ≤
      ‖WKB.complexLinearizedMetric F (complexifyResponse B h) x - h x‖ := by
  have he : B (tensorFieldRealPart h) = euclideanRealPart ∘ complexifyResponse B h := by
    ext y l
    exact (complexifyResponse_re B h y l).symm
  have hd : fderiv ℝ (B (tensorFieldRealPart h)) x =
      euclideanRealPart.comp (fderiv ℝ (complexifyResponse B h) x) := by
    rw [he]
    exact (euclideanRealPart.hasFDerivAt.comp x hB.hasFDerivAt).fderiv
  have herr : linearizedMetric F (B (tensorFieldRealPart h)) x - tensorFieldRealPart h x =
      (WKB.complexLinearizedMetric F (complexifyResponse B h) x - h x).map Complex.re := by
    ext a b
    change linearizedMetric F (B (tensorFieldRealPart h)) x a b - (h x a b).re =
      (WKB.complexLinearizedMetric F (complexifyResponse B h) x a b - h x a b).re
    simp only [linearizedMetric, partialDeriv, hd]
    simp [WKB.complexLinearizedMetric, partialDeriv, PiLp.inner_apply,
      RCLike.inner_apply, Finset.sum_add_distrib, mul_comm]
  rw [herr]
  exact frobenius_norm_re_le _

/-- The exact plus-source error is bounded by the complex full error at its
true frequency, using the original cutoff and the same `B`
(`app:ch_pairs:eq:pairs-lag-one-error`). On the measurement plateau the source
being subtracted is the original uncut tensor. Doubled carriers are included. -/
theorem norm_plusSource_strain_error_le_complex
    (F : Euclidean n → Euclidean N)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (χ : Euclidean n → ℝ) (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (i j : ι) {ρ : ℝ} (hρ : ρ ≠ 0) {x : Euclidean n} (hχ : χ x = 1)
    (hB : DifferentiableAt ℝ (complexifyResponse B (modulatedSource χ
      (fun y ↦ (θ i y + θ j y) / ρ)
      (fun y ↦ symmetricBilinearTensor (A i y) (A j y)) ρ)) x) :
    ‖linearizedMetric F (B (fun y ↦ χ y • ProductSum.plusSource θ A i j y)) x -
        ProductSum.plusSource θ A i j x‖ ≤
      ‖WKB.complexLinearizedMetric F (complexifyResponse B (modulatedSource χ
          (fun y ↦ (θ i y + θ j y) / ρ)
          (fun y ↦ symmetricBilinearTensor (A i y) (A j y)) ρ)) x -
        modulatedSource χ (fun y ↦ (θ i y + θ j y) / ρ)
          (fun y ↦ symmetricBilinearTensor (A i y) (A j y)) ρ x‖ := by
  have hb := norm_real_response_strain_error_le F B _ hB
  rw [← cutoff_plusSource_eq_real_modulatedSource χ θ A i j hρ] at hb
  simpa only [hχ, one_smul] using hb

/-- The distinct minus-source error uses the conjugated complete amplitude
and the SAME response (`app:ch_pairs:eq:pairs-lag-one-error`). The nonzero true
frequency is supplied by `sample_minus_represented_with_beat`; the difference
diagonal is never needed. This is a contraction, not the missing complex
fixed-response accuracy theorem. -/
theorem norm_minusSource_strain_error_le_complex
    (F : Euclidean n → Euclidean N)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (χ : Euclidean n → ℝ) (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (i j : ι) {ρ : ℝ} (hρ : ρ ≠ 0) {x : Euclidean n} (hχ : χ x = 1)
    (hB : DifferentiableAt ℝ (complexifyResponse B (modulatedSource χ
      (fun y ↦ (θ i y - θ j y) / ρ)
      (fun y ↦ symmetricBilinearTensor (A i y) ((A j y).map conj)) ρ)) x) :
    ‖linearizedMetric F (B (fun y ↦ χ y • ProductSum.minusSource θ A i j y)) x -
        ProductSum.minusSource θ A i j x‖ ≤
      ‖WKB.complexLinearizedMetric F (complexifyResponse B (modulatedSource χ
          (fun y ↦ (θ i y - θ j y) / ρ)
          (fun y ↦ symmetricBilinearTensor (A i y) ((A j y).map conj)) ρ)) x -
        modulatedSource χ (fun y ↦ (θ i y - θ j y) / ρ)
          (fun y ↦ symmetricBilinearTensor (A i y) ((A j y).map conj)) ρ x‖ := by
  have hb := norm_real_response_strain_error_le F B _ hB
  rw [← cutoff_minusSource_eq_real_modulatedSource χ θ A i j hρ] at hb
  simpa only [hχ, one_smul] using hb

end JanetCartan.SignedProductEstimates
