module
public import JanetCartan.Iteration.PhysicalMean.PhysicalHermitianProfile
import all JanetCartan.Iteration.PhysicalMean.PhysicalHermitianProfile

/-!
# Full phase-cancelled Hermitian profiles from the exact total sample mass

Consumer: the actual original fullSampledSelf in main:prop:mean. Reuses the
complementary-order SINGLE Hermitian estimate and sums over the unchanged
packed sample type. Only ACTIVE outer weights require amplitude smoothness
and true-R profiles; zero weights contribute literally zero without division.
The actual mass producer is OriginalCanonicalWeightMass.weight_mass_le;
actual baseline/source amplitude inputs belong to tasks112/15 and must still
be instantiated before claiming an actual original full-self profile. No
sample-count, square-root-mass square, K/λ-to-R conversion or profile weakening.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set
open scoped BigOperators ContDiff Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.FullHermitianProfiles
open CurrentMean
/-- Exact O(1)-mass sum of full Hermitian tensors, with complementary derivative
orders and inactive labels retained (main:prop:mean; main:eq:mean-fine-size). -/
theorem weighted_full_self_profile {n N : ℕ} {ι : Type*} [Fintype ι]
    {K : Set (Euclidean n)} (hK : IsCompact K) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hZ : ∀ i, μ i ≠ 0 → ContDiff ℝ ∞ (Z i)) (A : ℕ → ℝ) (hA : ∀ q, 0 ≤ A q)
    {R C : ℝ} (hR : 1 ≤ R) (hmass : ∑ i, μ i ≤ C) (s : ℕ)
    (hp : ∀ i, μ i ≠ 0 → ∀ q, q ≤ s → cNorm K q (Z i) ≤ A q*R^q) :
    cNorm K s (fun x ↦ weightedHermitianTensor μ (fun y i ↦ Z i y) x) ≤
      (C*hermitianPhysicalOrderConstant A s)*R^s := by
  have hself (i : ι) (hi : μ i ≠ 0) : ContDiff ℝ s (fun x ↦ hermitianTensor (Z i x)) := by
    have hbil := ((hermitianContinuousBilinear (m := Fin N) (n := Fin n)).contDiff.comp (hZ i hi)).clm_apply (hZ i hi)
    have hbil' := hbil.of_le (by simp : (s : ℕ∞ω) ≤ ∞)
    have he : (fun x ↦ hermitianContinuousBilinear (Z i x) (Z i x)) = (fun x ↦ hermitianTensor (Z i x)) :=
      funext fun x ↦ (hermitianContinuousBilinear_apply (Z i x) (Z i x)).trans (mixedHermitianTensor_self (Z i x))
    exact he ▸ hbil'
  have hweighted (i : ι) : ContDiff ℝ s (fun x ↦ μ i • hermitianTensor (Z i x)) := by
    by_cases hi : μ i = 0
    · simpa only [hi,zero_smul] using
        (contDiff_const : ContDiff ℝ s (fun _ : Euclidean n ↦ (0 : Matrix (Fin n) (Fin n) ℝ)))
    · exact (hself i hi).const_smul (μ i)
  have hc : 0 ≤ hermitianPhysicalOrderConstant A s*R^s :=
    mul_nonneg (hermitianPhysicalOrderConstant_nonneg A hA s) (pow_nonneg (zero_le_one.trans hR) _)
  have hterm (i : ι) : cNorm K s (fun x ↦ μ i • hermitianTensor (Z i x)) ≤
      μ i*(hermitianPhysicalOrderConstant A s*R^s) := by
    by_cases hi : μ i = 0
    · simp only [hi,zero_smul,zero_mul]
      change cNorm K s (0 : Euclidean n → Matrix (Fin n) (Fin n) ℝ) ≤ 0
      exact (cNorm_zero K s).le
    · change cNorm K s (μ i • (fun x ↦ hermitianTensor (Z i x))) ≤ _
      rw [cNorm_smul (μ i) (hself i hi),Real.norm_of_nonneg (hμ i)]
      exact mul_le_mul_of_nonneg_left
        (physicalHermitian_cNorm_le_profile hK s A hA hR (Z i) (hZ i hi) (hp i hi)) (hμ i)
  change cNorm K s (fun x ↦ ∑ i, μ i • hermitianTensor (Z i x)) ≤ _
  calc
    _ ≤ ∑ i, cNorm K s (fun x ↦ μ i • hermitianTensor (Z i x)) := by
      simpa using cNorm_sum_le Finset.univ hK (fun i _ ↦ hweighted i)
    _ ≤ ∑ i, μ i*(hermitianPhysicalOrderConstant A s*R^s) := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (∑ i, μ i)*(hermitianPhysicalOrderConstant A s*R^s) := (Finset.sum_mul ..).symm
    _ ≤ C*(hermitianPhysicalOrderConstant A s*R^s) := mul_le_mul_of_nonneg_right hmass hc
    _ = _ := by ring
end JanetCartan.PhysicalMean.FullHermitianProfiles
