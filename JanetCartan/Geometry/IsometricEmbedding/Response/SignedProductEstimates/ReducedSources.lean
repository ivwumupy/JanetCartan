module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Sources
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.CanonicalEndpoint

/-!
# The literal reduced signed sources

Step 1 of `app:ch_pairs:prop:pairs-lag-sum` applies the fixed reduced solver to
one half of the original stress contraction. These identities connect the
actual `ProductSum` sources with its complex modulated-source input. Neither
source cutoff is removed and the stress row is never replaced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open ResponseSourceExtension ResponseTransfer.SourceNegative Sampling.BackgroundModulation
variable {n N : ℕ}

/-- The literal half stress contraction commutes with realification
(`app:ch_pairs:eq:pairs-ambient-U`). This identifies the reduced source used
by `UniformStep.cut_sampled_ambient_product_stage_error_le_of_reduced_residual`. -/
theorem stressSource_realPart_eq
    (Q : Euclidean n → Fin n → MetricTensor n)
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    (fun x ↦ WithLp.toLp 2 (AmbientResponse.stressSource Q (tensorFieldRealPart h) x)) =
      (fun x ↦ euclideanRealPart ((1 / 2 : ℝ) • complexStressContraction (Q x) (h x))) := by
  ext x i
  simp [AmbientResponse.stressSource, tensorPairing, tensorFieldRealPart,
    complexStressContraction, Finset.mul_sum]

/-- The complete reduced source is the real part of the same modulated
source with its actual row multiplier (`app:ch_response:eq:response-graded-reduced`).
Both the original source cutoff and the reduced cutoff are retained. -/
theorem cutoff_stressSource_real_modulated_eq
    (Q : Euclidean n → Fin n → MetricTensor n)
    (χ η φ : Euclidean n → ℝ) (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ) (ρ : ℝ) :
    (fun x ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η
      (AmbientResponse.stressSource Q (tensorFieldRealPart (modulatedSource χ φ a ρ))) x)) =
    (fun x ↦ euclideanRealPart (modulatedSource χ φ
      (fun y ↦ η y • ((1 / 2 : ℝ) • complexStressContraction (Q y) (a y))) ρ x)) := by
  ext x i
  simp [AmbientResponse.cutoffSource, AmbientResponse.stressSource, tensorPairing,
    tensorFieldRealPart, modulatedSource, complexStressContraction, Finset.mul_sum,
    Finset.sum_sub_distrib, mul_sub, Complex.mul_re, mul_assoc, mul_left_comm, mul_comm]

variable {ι : Type*}

/-- Exact reduced-source substitution for every actual plus term, including
the doubled diagonal (`app:ch_pairs:prop:pairs-lag-sum`, Step 1). The original
row, half factor, both cutoffs and complete tensor amplitude are unchanged. -/
theorem cutoff_stressSource_plus_eq_real_modulatedSource
    (Q : Euclidean n → Fin n → MetricTensor n)
    (χ η : Euclidean n → ℝ) (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ) (i j : ι)
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    (fun x ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η
      (AmbientResponse.stressSource Q (fun y ↦ χ y • ProductSum.plusSource θ A i j y)) x)) =
    (fun x ↦ euclideanRealPart (modulatedSource χ (fun y ↦ (θ i y + θ j y) / ρ)
      (fun y ↦ η y • ((1 / 2 : ℝ) • complexStressContraction (Q y)
        (symmetricBilinearTensor (A i y) (A j y)))) ρ x)) := by
  rw [cutoff_plusSource_eq_real_modulatedSource χ θ A i j hρ]
  exact cutoff_stressSource_real_modulated_eq Q χ η _ _ ρ

/-- Exact reduced-source substitution for the actual difference term
(`app:ch_pairs:prop:pairs-lag-sum`, Step 1). Conjugation acts only on the second
complete amplitude; the same stress row and both source cutoffs remain. -/
theorem cutoff_stressSource_minus_eq_real_modulatedSource
    (Q : Euclidean n → Fin n → MetricTensor n)
    (χ η : Euclidean n → ℝ) (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ) (i j : ι)
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    (fun x ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η
      (AmbientResponse.stressSource Q (fun y ↦ χ y • ProductSum.minusSource θ A i j y)) x)) =
    (fun x ↦ euclideanRealPart (modulatedSource χ (fun y ↦ (θ i y - θ j y) / ρ)
      (fun y ↦ η y • ((1 / 2 : ℝ) • complexStressContraction (Q y)
        (symmetricBilinearTensor (A i y) ((A j y).map conj)))) ρ x)) := by
  rw [cutoff_minusSource_eq_real_modulatedSource χ θ A i j hρ]
  exact cutoff_stressSource_real_modulated_eq Q χ η _ _ ρ

end JanetCartan.SignedProductEstimates
