module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.ZeroOrder

/-!
# Measurement-contracted nonlinear increments

The actual nonlinear term of `main:eq:full-recursion`, with the weighted C⁰/L²
estimate used in `main:lem:mean-recurrence` and `MeanRecurrence.finite_mean_bounds`.
These proofs use the Hermitian polarization identity and weighted energies;
no nonlinear contraction is assumed.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean

variable {d : ℕ} {ι m n G : Type*} [Fintype ι] [Fintype m] [Fintype n]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

set_option backward.isDefEq.respectTransparency false in
/-- `main:lem:mean-recurrence`: the complete measurement-contracted quadratic
increment costs the uniform measurement bound times the weighted C⁰/L² sizes. -/
theorem periodicL2Norm_contracted_weightedHermitianTensor_add_sub_le
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (S D : Torus d → ι → Matrix m n ℂ)
    (hS : ∀ i, IsSmoothPeriodic (fun x ↦ S x i))
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) {c : ℝ}
    (hc : 0 ≤ c) (hC : ∀ x, ‖C x‖ ≤ c) :
    periodicL2Norm (fun x ↦ C x (weightedHermitianTensor μ (S+D) x) -
      C x (weightedHermitianTensor μ S x)) ≤
      c * (2 * weightedPeriodicCNorm μ 0 S + weightedPeriodicCNorm μ 0 D) *
        weightedPeriodicL2Norm μ D := by
  apply periodicL2Norm_le_weighted_energy μ hμ D (fun i ↦ (hD i).1) _
    (A := c * (2 * weightedPeriodicCNorm μ 0 S + weightedPeriodicCNorm μ 0 D))
    (by unfold weightedPeriodicCNorm; positivity)
  intro x
  have heq : weightedHermitianTensor μ (S+D) x - weightedHermitianTensor μ S x =
      (2 : ℝ) • weightedHermitianBilinear μ S D x + weightedHermitianBilinear μ D D x := by
    simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, weightedHermitianBilinear_self] using
      congrFun (weightedHermitianTensor_add_sub μ S D) x
  have hpoint : ‖C x (weightedHermitianTensor μ (S+D) x) - C x (weightedHermitianTensor μ S x)‖ ≤
      (c * (2 * weightedPeriodicCNorm μ 0 S + weightedPeriodicCNorm μ 0 D)) *
        Real.sqrt (∑ i, μ i * ‖D x i‖ ^ 2) := by
    rw [← map_sub, heq]
    calc
      _ ≤ c * ‖(2 : ℝ) • weightedHermitianBilinear μ S D x + weightedHermitianBilinear μ D D x‖ :=
        ((C x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
      _ ≤ c * (2 * ‖weightedHermitianBilinear μ S D x‖ + ‖weightedHermitianBilinear μ D D x‖) := by
        apply mul_le_mul_of_nonneg_left _ hc
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
          norm_add_le ((2 : ℝ) • weightedHermitianBilinear μ S D x) (weightedHermitianBilinear μ D D x)
      _ ≤ c * (2 * (weightedPeriodicCNorm μ 0 S * Real.sqrt (∑ i, μ i * ‖D x i‖ ^ 2)) +
          weightedPeriodicCNorm μ 0 D * Real.sqrt (∑ i, μ i * ‖D x i‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
          (norm_weightedHermitianBilinear_le_cNorm μ hμ S D hS x) (by norm_num))
          (norm_weightedHermitianBilinear_le_cNorm μ hμ D D hD x)) hc
      _ = _ := by ring
  simpa only [mul_pow, Real.sq_sqrt
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hμ i) (sq_nonneg _)))] using
    pow_le_pow_left₀ (norm_nonneg _) hpoint 2

set_option backward.isDefEq.respectTransparency false in
/-- `main:lem:mean-recurrence`: the actual nonlinear increment is at most
`5 c U V ε a` after substituting the separate accumulated and update size bounds.
This discharges the nonlinear estimate, leaving the canonical sizes to its producer. -/
theorem periodicL2Norm_contracted_weightedHermitianTensor_add_sub_le_of_sizes
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (S D : Torus d → ι → Matrix m n ℂ)
    (hS : ∀ i, IsSmoothPeriodic (fun x ↦ S x i))
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) {c U V ε a : ℝ}
    (hc : 0 ≤ c) (hC : ∀ x, ‖C x‖ ≤ c)
    (hU : 0 ≤ U) (hε : 0 ≤ ε) (haε : a ≤ ε)
    (hpast : weightedPeriodicCNorm μ 0 S ≤ 2 * U * ε)
    (hnewC : weightedPeriodicCNorm μ 0 D ≤ U * a)
    (hnewL2 : weightedPeriodicL2Norm μ D ≤ V * a) :
    periodicL2Norm (fun x ↦ C x (weightedHermitianTensor μ (S+D) x) -
      C x (weightedHermitianTensor μ S x)) ≤ 5 * c * U * V * ε * a := by
  have hcoef : 2 * weightedPeriodicCNorm μ 0 S + weightedPeriodicCNorm μ 0 D ≤ 5 * U * ε := by
    have := mul_le_mul_of_nonneg_left haε hU
    linarith
  calc
    _ ≤ c * (2 * weightedPeriodicCNorm μ 0 S + weightedPeriodicCNorm μ 0 D) *
        weightedPeriodicL2Norm μ D :=
      periodicL2Norm_contracted_weightedHermitianTensor_add_sub_le μ hμ S D hS hD C hc hC
    _ ≤ (c * (5 * U * ε)) * (V * a) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcoef hc) hnewL2 (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- `main:lem:mean-recurrence`: inserting the weighted canonical C⁰ and L²
band powers yields `C ε Kmax^((d+1)/2) a`, with no sample-count factor. -/
theorem periodicL2Norm_contracted_weightedHermitianTensor_add_sub_le_of_band_sizes
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (S D : Torus d → ι → Matrix m n ℂ)
    (hS : ∀ i, IsSmoothPeriodic (fun x ↦ S x i))
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) {c u v ε a K : ℝ}
    (hc : 0 ≤ c) (hC : ∀ x, ‖C x‖ ≤ c)
    (hu : 0 ≤ u) (hε : 0 ≤ ε) (haε : a ≤ ε) (hK : 0 < K)
    (hpast : weightedPeriodicCNorm μ 0 S ≤ 2 * (u * K ^ ((d : ℝ)/2)) * ε)
    (hnewC : weightedPeriodicCNorm μ 0 D ≤ (u * K ^ ((d : ℝ)/2)) * a)
    (hnewL2 : weightedPeriodicL2Norm μ D ≤ (v * K ^ (1/2 : ℝ)) * a) :
    periodicL2Norm (fun x ↦ C x (weightedHermitianTensor μ (S+D) x) -
      C x (weightedHermitianTensor μ S x)) ≤
      (5 * c * u * v) * ε * K ^ (((d : ℝ)+1)/2) * a := by
  apply (periodicL2Norm_contracted_weightedHermitianTensor_add_sub_le_of_sizes
    μ hμ S D hS hD C hc hC (mul_nonneg hu (Real.rpow_nonneg hK.le _))
    hε haε hpast hnewC hnewL2).trans_eq
  rw [show ((d : ℝ)+1)/2 = (d : ℝ)/2 + 1/2 by ring, Real.rpow_add hK]
  ring

end JanetCartan.CurrentMean
