module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Matrix
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Sobolev

/-!
# Weighted products in the current mean recurrence

The C⁰/L² part of `main:lem:mean-recurrence`, supplying the mixed product
and nonlinear increment bounds consumed by `MeanRecurrence.finite_mean_bounds`.
The fields and integrals are actual finite matrix families on the unit torus.
All weights are nonnegative; no inverse weight or sample-count constant occurs.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean

variable {d : ℕ} {ι F G : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `main:lem:mean-recurrence`: square-sum weighted Cʳ size of a finite
periodic family, in the shared fundamental-cell convention. -/
def weightedPeriodicCNorm (μ : ι → ℝ) (r : ℕ) (D : Torus d → ι → F) : ℝ :=
  Real.sqrt (∑ i, μ i * cNorm (fundamentalCell d) r (periodicLift (fun x ↦ D x i)) ^ 2)

/-- `main:lem:mean-recurrence`: square-sum weighted L² size, using normalized
Haar measure on the unit torus. -/
def weightedPeriodicL2Norm (μ : ι → ℝ) (D : Torus d → ι → F) : ℝ :=
  Real.sqrt (∑ i, μ i * periodicL2Norm (fun x ↦ D x i) ^ 2)

omit [NormedSpace ℝ F] [NormedSpace ℝ G] in
/-- `main:lem:mean-recurrence`: integrating a pointwise weighted energy
bound preserves its constant exactly. This is the integration step for the
Hermitian product, not an assumed bilinear estimate. -/
theorem periodicL2Norm_le_weighted_energy (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (E : Torus d → ι → F) (hE : ∀ i, Continuous (fun x ↦ E x i))
    (f : Torus d → G) {A : ℝ} (hA : 0 ≤ A)
    (hpoint : ∀ x, ‖f x‖ ^ 2 ≤ A ^ 2 * ∑ i, μ i * ‖E x i‖ ^ 2) :
    periodicL2Norm f ≤ A * weightedPeriodicL2Norm μ E := by
  have hi (i : ι) : Integrable (fun x ↦ ‖E x i‖ ^ 2) :=
    ((hE i).memLp_of_hasCompactSupport (p := 2)
      (HasCompactSupport.of_compactSpace _)).integrable_norm_pow (by decide)
  have hs : Integrable (fun x ↦ ∑ i, μ i * ‖E x i‖ ^ 2) :=
    integrable_finsetSum _ (fun i _ ↦ (hi i).const_mul (μ i))
  have he : (∫ x, ∑ i, μ i * ‖E x i‖ ^ 2) =
      ∑ i, μ i * periodicL2Norm (fun x ↦ E x i) ^ 2 := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ (hi i).const_mul (μ i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, periodicL2Norm, Real.sq_sqrt
      (integral_nonneg (fun x ↦ sq_nonneg ‖E x i‖))]
  calc
    periodicL2Norm f ≤ Real.sqrt (A ^ 2 * ∑ i, μ i * periodicL2Norm (fun x ↦ E x i) ^ 2) := by
      apply Real.sqrt_le_sqrt
      calc
        (∫ x, ‖f x‖ ^ 2) ≤ ∫ x, A ^ 2 * ∑ i, μ i * ‖E x i‖ ^ 2 :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
            (hs.const_mul _) (Filter.Eventually.of_forall hpoint)
        _ = _ := by rw [integral_const_mul, he]
    _ = A * weightedPeriodicL2Norm μ E := by
      rw [mul_comm (A ^ 2), Real.sqrt_mul (Finset.sum_nonneg
        (fun i _ ↦ mul_nonneg (hμ i) (sq_nonneg _))), Real.sqrt_sq hA, mul_comm]
      rfl

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `main:lem:mean-recurrence`: put the lower-band factor in weighted C⁰
and retain the pointwise weighted energy of the higher-band factor. -/
theorem norm_weightedHermitianBilinear_le_cNorm (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D E : Torus d → ι → Matrix m n ℂ)
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i)) (x : Torus d) :
    ‖weightedHermitianBilinear μ D E x‖ ≤
      weightedPeriodicCNorm μ 0 D * Real.sqrt (∑ i, μ i * ‖E x i‖ ^ 2) := by
  have hDsum : (∑ i, μ i * ‖D x i‖ ^ 2) ≤
      ∑ i, μ i * cNorm (fundamentalCell d) 0 (periodicLift (fun x ↦ D x i)) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) ((hD i).norm_le_cNorm_zero x) 2) (hμ i)
  have h := (norm_weightedHermitianBilinear_sq_le μ hμ D E x).trans
    (mul_le_mul_of_nonneg_right hDsum
      (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hμ i) (sq_nonneg _))))
  simpa only [Real.sqrt_mul (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hμ i)
    (sq_nonneg (cNorm (fundamentalCell d) 0 (periodicLift (fun x ↦ D x i)))))),
    weightedPeriodicCNorm] using Real.le_sqrt_of_sq_le h

/-- `main:lem:mean-recurrence`: the weighted C⁰-times-L² Hermitian bound
with constant one, for the actual polarization in the recurrence. -/
theorem periodicL2Norm_weightedHermitianBilinear_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D E : Torus d → ι → Matrix m n ℂ)
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (hE : ∀ i, Continuous (fun x ↦ E x i)) :
    periodicL2Norm (weightedHermitianBilinear μ D E) ≤
      weightedPeriodicCNorm μ 0 D * weightedPeriodicL2Norm μ E := by
  apply periodicL2Norm_le_weighted_energy μ hμ E hE _
    (A := weightedPeriodicCNorm μ 0 D) (Real.sqrt_nonneg _)
  intro x
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_weightedHermitianBilinear_le_cNorm μ hμ D E hD x) 2
  simpa only [mul_pow, Real.sq_sqrt
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hμ i) (sq_nonneg _)))] using h

/-- `main:lem:mean-recurrence`: the exact nonlinear increment is controlled
by the weighted sizes of the accumulated field and current change. Symmetry
allows the change to occupy the L² slot in every term. -/
theorem periodicL2Norm_weightedHermitianTensor_add_sub_le
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (S D : Torus d → ι → Matrix m n ℂ)
    (hS : ∀ i, IsSmoothPeriodic (fun x ↦ S x i))
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i)) :
    periodicL2Norm (weightedHermitianTensor μ (S + D) - weightedHermitianTensor μ S) ≤
      (2 * weightedPeriodicCNorm μ 0 S + weightedPeriodicCNorm μ 0 D) *
        weightedPeriodicL2Norm μ D := by
  apply periodicL2Norm_le_weighted_energy μ hμ D (fun i ↦ (hD i).1) _ (by
    unfold weightedPeriodicCNorm; positivity)
  intro x
  have hpoint : ‖(weightedHermitianTensor μ (S + D) - weightedHermitianTensor μ S) x‖ ≤
      (2 * weightedPeriodicCNorm μ 0 S + weightedPeriodicCNorm μ 0 D) *
        Real.sqrt (∑ i, μ i * ‖D x i‖ ^ 2) := by
    rw [weightedHermitianTensor_add_sub, ← weightedHermitianBilinear_self]
    calc
      _ ≤ ‖(2 : ℝ) • weightedHermitianBilinear μ S D x‖ +
          ‖weightedHermitianBilinear μ D D x‖ := norm_add_le _ _
      _ = 2 * ‖weightedHermitianBilinear μ S D x‖ +
          ‖weightedHermitianBilinear μ D D x‖ := by rw [norm_smul]; norm_num
      _ ≤ 2 * (weightedPeriodicCNorm μ 0 S * Real.sqrt (∑ i, μ i * ‖D x i‖ ^ 2)) +
          weightedPeriodicCNorm μ 0 D * Real.sqrt (∑ i, μ i * ‖D x i‖ ^ 2) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (norm_weightedHermitianBilinear_le_cNorm μ hμ S D hS x) (by norm_num))
          (norm_weightedHermitianBilinear_le_cNorm μ hμ D D hD x)
      _ = _ := by ring
  simpa only [mul_pow, Real.sq_sqrt
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hμ i) (sq_nonneg _)))] using
    pow_le_pow_left₀ (norm_nonneg _) hpoint 2

set_option backward.isDefEq.respectTransparency false in
/-- `main:lem:mean-recurrence`: composing the actual weighted tensor with a
bounded measurement field costs only its uniform operator norm. The lower
factor stays in weighted C⁰ and the higher one stays in weighted L². -/
theorem periodicL2Norm_contracted_weightedHermitianBilinear_le
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D E : Torus d → ι → Matrix m n ℂ)
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (hE : ∀ i, Continuous (fun x ↦ E x i))
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) {c : ℝ}
    (hc : 0 ≤ c) (hC : ∀ x, ‖C x‖ ≤ c) :
    periodicL2Norm (fun x ↦ C x (weightedHermitianBilinear μ D E x)) ≤
      c * weightedPeriodicCNorm μ 0 D * weightedPeriodicL2Norm μ E := by
  apply periodicL2Norm_le_weighted_energy μ hμ E hE _
    (A := c * weightedPeriodicCNorm μ 0 D) (mul_nonneg hc (Real.sqrt_nonneg _))
  intro x
  have h : ‖C x (weightedHermitianBilinear μ D E x)‖ ≤
      (c * weightedPeriodicCNorm μ 0 D) * Real.sqrt (∑ i, μ i * ‖E x i‖ ^ 2) := by
    calc
      _ ≤ ‖C x‖ * ‖weightedHermitianBilinear μ D E x‖ := (C x).le_opNorm _
      _ ≤ c * (weightedPeriodicCNorm μ 0 D * Real.sqrt (∑ i, μ i * ‖E x i‖ ^ 2)) :=
        mul_le_mul (hC x) (norm_weightedHermitianBilinear_le_cNorm μ hμ D E hD x)
          (norm_nonneg _) hc
      _ = _ := by ring
  simpa only [mul_pow, Real.sq_sqrt
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hμ i) (sq_nonneg _)))] using
    pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `main:lem:mean-recurrence`: substituting the accumulated C⁰ bound
`2 U ε` and current update bounds `U a`, `V a` yields the nonlinear
increment constant `5 U V ε a`. These are canonical size inputs, not a
nonlinear contraction hypothesis. -/
theorem periodicL2Norm_weightedHermitianTensor_add_sub_le_of_sizes
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (S D : Torus d → ι → Matrix m n ℂ)
    (hS : ∀ i, IsSmoothPeriodic (fun x ↦ S x i))
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    {U V ε a : ℝ} (hU : 0 ≤ U) (_hV : 0 ≤ V) (hε : 0 ≤ ε)
    (_ha : 0 ≤ a) (haε : a ≤ ε)
    (hpast : weightedPeriodicCNorm μ 0 S ≤ 2 * U * ε)
    (hnewC : weightedPeriodicCNorm μ 0 D ≤ U * a)
    (hnewL2 : weightedPeriodicL2Norm μ D ≤ V * a) :
    periodicL2Norm (weightedHermitianTensor μ (S + D) - weightedHermitianTensor μ S) ≤
      5 * U * V * ε * a := by
  have hcoef : 2 * weightedPeriodicCNorm μ 0 S + weightedPeriodicCNorm μ 0 D ≤
      5 * U * ε := by
    have hUa := mul_le_mul_of_nonneg_left haε hU
    linarith
  calc
    _ ≤ (2 * weightedPeriodicCNorm μ 0 S + weightedPeriodicCNorm μ 0 D) *
        weightedPeriodicL2Norm μ D :=
      periodicL2Norm_weightedHermitianTensor_add_sub_le μ hμ S D hS hD
    _ ≤ (5 * U * ε) * (V * a) := mul_le_mul hcoef hnewL2
      (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

end JanetCartan.CurrentMean
