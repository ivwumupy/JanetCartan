module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.ComponentOperator
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.Comparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRealization.NormalPositivity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.SmoothFamilyNorms.Sobolev

/-!
# Sharp bounds for the constructed canonical changes

Apply the comparison of `main:prop:canonical` to the literal component built
from the smooth raw derivative, fixed zero atom and original measurement.
Positivity of the actual cut auxiliary normal is proved, and its decomposition
is definitional. The weighted and accumulated bounds use no individual sample
weight inverse and no additional sample-count or update-count factor.

The original raw derivative bounds, reference-normal bound and common sampled
normal comparison remain inputs from their producers. They must hold for these
SAME component maps. The original fixed inverse is retained through its L² norm;
no canonical-adjoint or final current-mean bound is assumed.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius RealInnerProductSpace

namespace JanetCartan.CanonicalChange

open ContinuumRow CurrentMean CurrentMean.SmoothPeriodicFamily

variable {n : ℕ} {ι m : Type*} [Fintype ι] [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]

/-- Square-root comparison with the actual positive auxiliary term in
`main:prop:canonical`, used for both physical and Sobolev raw sizes. -/
private theorem sqrt_sum_weighted_raw_size_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (reference Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    {K M ε B : ℝ} (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hreference : ‖reference‖ ≤ M)
    (hcomparison : ‖completeCanonicalNormal c χmeas χsrc ψ μ A hK - reference‖ ≤ ε)
    (size : ∀ i, Raw i → ℝ) (hsize : ∀ i v, 0 ≤ size i v)
    (hraw : ∀ i v, size i v ≤ B * ‖v‖) (r : OutputL2 n) :
    Real.sqrt (∑ i, μ i * size i ((A i).adjoint (Q₀ r)) ^ 2) ≤
      B * Real.sqrt (M + ε) * ‖Q₀‖ * ‖r‖ := by
  have hp : 0 ≤ M + ε := add_nonneg ((norm_nonneg _).trans hreference)
    ((norm_nonneg _).trans hcomparison)
  have hrawSq (i : ι) (v : Raw i) : size i v ^ 2 ≤ B ^ 2 * ‖v‖ ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (hsize i v) (by positivity)).2 (hraw i v)
  apply (Real.sqrt_le_left (by positivity)).2
  calc
    _ ≤ B ^ 2 * (M + ε) * ‖Q₀‖ ^ 2 * ‖r‖ ^ 2 :=
      sum_weighted_size_sq_le_of_normal_comparison μ hμ A
        (AuxiliaryRawBand.cutAuxiliaryNormal c χmeas χsrc ψ hK) reference Q₀ size
        (sq_nonneg B) (AuxiliaryRealization.cutAuxiliaryNormal_inner_nonneg c χmeas χsrc ψ hK)
        hreference hcomparison hrawSq r
    _ = _ := by simp only [mul_pow, Real.sq_sqrt hp]

variable (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ι → ℝ)
    (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (reference Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
include hμ

local notation "component" => smoothRawCrossOperator base C hC G CG hG

/-- The weighted physical derivative estimate of
`app:ch_mean_pairs:eq:mean-canonical-weighted-C`, for the actual constructed
component and canonical derivative. The auxiliary positivity and complete
normal decomposition are discharged on the original channels. -/
theorem weightedPeriodicCNorm_smoothCanonicalDerivative_le (s : ℕ)
    {K M ε B : ℝ} (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hreference : ‖reference‖ ≤ M)
    (hcomparison : ‖completeCanonicalNormal c χmeas χsrc ψ μ component hK - reference‖ ≤ ε)
    (hraw : ∀ i v, cNorm (fundamentalCell n) s (periodicLift (fun x ↦ (G i v).val x ())) ≤
      B * K ^ ((s : ℝ) + (n : ℝ) / 2) * ‖v‖) (r : OutputL2 n) :
    weightedPeriodicCNorm μ s (smoothCanonicalDerivative component G Q₀ r).val ≤
      B * Real.sqrt (M + ε) * ‖Q₀‖ * K ^ ((s : ℝ) + (n : ℝ) / 2) * ‖r‖ := by
  have hb := sqrt_sum_weighted_raw_size_le c χmeas χsrc ψ μ hμ component reference Q₀ hK
    (mul_nonneg hB (Real.rpow_nonneg (zero_le_one.trans hK) _)) hreference hcomparison
    (fun i v ↦ cNorm (fundamentalCell n) s (periodicLift (fun x ↦ (G i v).val x ())))
    (fun _ _ ↦ cNorm_nonneg _ _ _) hraw r
  change weightedPeriodicCNorm μ s (smoothCanonicalDerivative component G Q₀ r).val ≤ _ at hb
  exact hb.trans_eq (by ring)

/-- The weighted Fourier Sobolev estimate of
`app:ch_mean_pairs:eq:mean-canonical-weighted-low`, with the sharp half-order
raw exponent. Only the original inverse's L² norm enters this estimate. -/
theorem weightedPeriodicSobolevNorm_smoothCanonicalDerivative_le (s : ℕ)
    {K M ε B : ℝ} (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hreference : ‖reference‖ ≤ M)
    (hcomparison : ‖completeCanonicalNormal c χmeas χsrc ψ μ component hK - reference‖ ≤ ε)
    (hraw : ∀ i v, periodicSobolevNorm s (fun x ↦ (G i v).val x ()) ≤
      B * K ^ ((s : ℝ) + 1 / 2) * ‖v‖) (r : OutputL2 n) :
    weightedPeriodicSobolevNorm μ s (smoothCanonicalDerivative component G Q₀ r).val ≤
      B * Real.sqrt (M + ε) * ‖Q₀‖ * K ^ ((s : ℝ) + 1 / 2) * ‖r‖ := by
  have hb := sqrt_sum_weighted_raw_size_le c χmeas χsrc ψ μ hμ component reference Q₀ hK
    (mul_nonneg hB (Real.rpow_nonneg (zero_le_one.trans hK) _)) hreference hcomparison
    (fun i v ↦ periodicSobolevNorm s (fun x ↦ (G i v).val x ()))
    (fun _ _ ↦ Real.sqrt_nonneg _) hraw r
  change weightedPeriodicSobolevNorm μ s (smoothCanonicalDerivative component G Q₀ r).val ≤ _ at hb
  exact hb.trans_eq (by ring)

omit G CG hG reference in
/-- Accumulating the SAME canonical changes in `main:lem:mean-recurrence`
preserves the sharp physical exponent. The actual raw estimates and normal
comparisons are used separately at each band; the residual norm sum is
retained explicitly, without an additional update-count factor. -/
theorem weightedPeriodicCNorm_sum_smoothCanonicalDerivative_le
    (G : ℕ → ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ℕ → ι → ℝ)
    (hG : ∀ l i v, periodicL2Norm (fun x ↦ (G l i v).val x ()) ≤ CG l i * ‖v‖)
    (reference : ℕ → OutputL2 n →L[ℝ] OutputL2 n) (K : ℕ → ℝ) (hK : ∀ l, 1 ≤ K l)
    (s : ℕ) {M ε B Kmax : ℝ} (hB : 0 ≤ B) (I : ℕ)
    (hKmax : ∀ l < I, K l ≤ Kmax)
    (hreference : ∀ l < I, ‖reference l‖ ≤ M)
    (hcomparison : ∀ l < I, ‖completeCanonicalNormal c χmeas χsrc ψ μ
      (smoothRawCrossOperator base C hC (G l) (CG l) (hG l)) (hK l) - reference l‖ ≤ ε)
    (hraw : ∀ l < I, ∀ i v,
      cNorm (fundamentalCell n) s (periodicLift (fun x ↦ (G l i v).val x ())) ≤
        B * K l ^ ((s : ℝ) + (n : ℝ) / 2) * ‖v‖) (e : ℕ → OutputL2 n) :
    let A := fun l ↦ smoothRawCrossOperator base C hC (G l) (CG l) (hG l)
    weightedPeriodicCNorm μ s
      (∑ l ∈ Finset.range I, smoothCanonicalDerivative (A l) (G l) Q₀ (e l)).val ≤
      B * Real.sqrt (M + ε) * ‖Q₀‖ * Kmax ^ ((s : ℝ) + (n : ℝ) / 2) *
        ∑ l ∈ Finset.range I, ‖e l‖ := by
  dsimp only
  rw [← cSeminorm_eq μ hμ]
  apply MeanRecurrence.seminorm_sum_le
  intro l hl
  rw [cSeminorm_eq]
  apply (weightedPeriodicCNorm_smoothCanonicalDerivative_le base C hC (G l) (CG l) (hG l)
    c χmeas χsrc ψ μ hμ (reference l) Q₀ s (hK l) hB (hreference l hl)
      (hcomparison l hl) (hraw l hl) (e l)).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (zero_le_one.trans (hK l)) (hKmax l hl) (by positivity)

omit G CG hG reference in
/-- The SAME finite canonical sum satisfies the weighted Sobolev estimate
of `main:lem:mean-recurrence`. Its exponent remains `s+1/2`, with only the
sum of source residual norms and the original L² inverse norm. -/
theorem weightedPeriodicSobolevNorm_sum_smoothCanonicalDerivative_le
    (G : ℕ → ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (CG : ℕ → ι → ℝ)
    (hG : ∀ l i v, periodicL2Norm (fun x ↦ (G l i v).val x ()) ≤ CG l i * ‖v‖)
    (reference : ℕ → OutputL2 n →L[ℝ] OutputL2 n) (K : ℕ → ℝ) (hK : ∀ l, 1 ≤ K l)
    (s : ℕ) {M ε B Kmax : ℝ} (hB : 0 ≤ B) (I : ℕ)
    (hKmax : ∀ l < I, K l ≤ Kmax)
    (hreference : ∀ l < I, ‖reference l‖ ≤ M)
    (hcomparison : ∀ l < I, ‖completeCanonicalNormal c χmeas χsrc ψ μ
      (smoothRawCrossOperator base C hC (G l) (CG l) (hG l)) (hK l) - reference l‖ ≤ ε)
    (hraw : ∀ l < I, ∀ i v, periodicSobolevNorm s (fun x ↦ (G l i v).val x ()) ≤
      B * K l ^ ((s : ℝ) + 1 / 2) * ‖v‖) (e : ℕ → OutputL2 n) :
    let A := fun l ↦ smoothRawCrossOperator base C hC (G l) (CG l) (hG l)
    weightedPeriodicSobolevNorm μ s
      (∑ l ∈ Finset.range I, smoothCanonicalDerivative (A l) (G l) Q₀ (e l)).val ≤
      B * Real.sqrt (M + ε) * ‖Q₀‖ * Kmax ^ ((s : ℝ) + 1 / 2) *
        ∑ l ∈ Finset.range I, ‖e l‖ := by
  dsimp only
  rw [← matrixSobolevSeminorm_eq μ hμ]
  apply MeanRecurrence.seminorm_sum_le
  intro l hl
  rw [matrixSobolevSeminorm_eq]
  apply (weightedPeriodicSobolevNorm_smoothCanonicalDerivative_le base C hC (G l) (CG l) (hG l)
    c χmeas χsrc ψ μ hμ (reference l) Q₀ s (hK l) hB (hreference l hl)
      (hcomparison l hl) (hraw l hl) (e l)).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (zero_le_one.trans (hK l)) (hKmax l hl) (by positivity)

end JanetCartan.CanonicalChange
