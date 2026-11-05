module

public import JanetCartan.Analysis.Operator.WeightedFamily.Scalar
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Norm bounds for weighted synthesis

Finite-family assembly for `main:eq:primary-strain` and
`app:ch_pairs:eq:pairs-weighted-U`. The ambient real normed space can in particular
be a space of fields, or a matrix space carrying the chosen Frobenius norm.
These lemmas take individual analytic bounds as inputs.
-/

@[expose] public section

namespace JanetCartan.WeightedFamily

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (μ : ι → ℝ)

/-- Weighted triangle inequality used for the primary and pair sums in
`main:eq:primary-strain` and `app:ch_pairs:eq:pairs-weighted-U`. -/
theorem norm_sum_weight_smul_le (hμ : ∀ i ∈ s, 0 ≤ μ i) (v : ι → E) :
    ‖∑ i ∈ s, μ i • v i‖ ≤ ∑ i ∈ s, μ i * ‖v i‖ := by
  calc
    _ ≤ ∑ i ∈ s, ‖μ i • v i‖ := norm_sum_le _ _
    _ = _ := Finset.sum_congr rfl (fun i hi ↦ by
      rw [norm_smul, Real.norm_of_nonneg (hμ i hi)])

/-- Uniform individual bounds assemble with the total coefficient mass,
as in `main:eq:primary-strain` and `app:ch_pairs:prop:pairs-lag-sum`. -/
theorem norm_sum_weight_smul_le_of_norm_le (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (v : ι → E) {C : ℝ} (hv : ∀ i ∈ s, ‖v i‖ ≤ C) :
    ‖∑ i ∈ s, μ i • v i‖ ≤ (∑ i ∈ s, μ i) * C := by
  calc
    _ ≤ ∑ i ∈ s, μ i * ‖v i‖ := norm_sum_weight_smul_le s μ hμ v
    _ ≤ ∑ i ∈ s, μ i * C := Finset.sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_left (hv i hi) (hμ i hi)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Square-root weighted synthesis controlled by mass and unweighted energy;
the Cauchy–Schwarz step used in `main:eq:primary-strain`. -/
theorem norm_sum_sqrt_smul_le (hμ : ∀ i ∈ s, 0 ≤ μ i) (v : ι → E) :
    ‖∑ i ∈ s, Real.sqrt (μ i) • v i‖ ≤
      Real.sqrt (∑ i ∈ s, μ i) * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) :=
  (norm_sum_weight_smul_le s (fun i ↦ Real.sqrt (μ i))
    (fun _ _ ↦ Real.sqrt_nonneg _) v).trans (sum_sqrt_mul_le s μ hμ (fun i ↦ ‖v i‖))

/-- Weighted synthesis controlled by mass and weighted energy, without a
sample-count factor (`app:ch_mean_pairs:eq:mean-canonical-weighted-low`). -/
theorem norm_sum_weight_smul_le_sqrt (hμ : ∀ i ∈ s, 0 ≤ μ i) (v : ι → E) :
    ‖∑ i ∈ s, μ i • v i‖ ≤
      Real.sqrt (∑ i ∈ s, μ i) * Real.sqrt (∑ i ∈ s, μ i * ‖v i‖ ^ 2) :=
  (norm_sum_weight_smul_le s μ hμ v).trans (sum_weight_mul_le s μ hμ (fun i ↦ ‖v i‖))

/-- Uniform primary estimates give exactly the square root of sample count
times mass in `main:eq:primary-strain`. -/
theorem norm_sum_sqrt_smul_le_of_norm_le (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (v : ι → E) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ i ∈ s, ‖v i‖ ≤ C) :
    ‖∑ i ∈ s, Real.sqrt (μ i) • v i‖ ≤
      Real.sqrt (s.card * ∑ i ∈ s, μ i) * C :=
  (norm_sum_weight_smul_le_of_norm_le s (fun i ↦ Real.sqrt (μ i))
    (fun _ _ ↦ Real.sqrt_nonneg _) v hv).trans
      (mul_le_mul_of_nonneg_right (sum_sqrt_le_sqrt_card_mul_sum s μ hμ) hC)

/-- Assembly of both signed families, with the difference diagonal omitted,
from uniform individual bounds (`app:ch_pairs:prop:pairs-lag-sum`). The only
weight loss is `2𝒲μ`; the physical factor `b²` can be applied afterwards. -/
theorem norm_signed_pair_sum_le [DecidableEq ι] (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (vplus vminus : ι → ι → E) {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ i ∈ s, ∀ j ∈ s, ‖vplus i j‖ ≤ C)
    (hm : ∀ i ∈ s, ∀ j ∈ s.erase i, ‖vminus i j‖ ≤ C) :
    ‖(∑ i ∈ s, ∑ j ∈ s, Real.sqrt (μ i * μ j) • vplus i j) +
        (∑ i ∈ s, ∑ j ∈ s.erase i, Real.sqrt (μ i * μ j) • vminus i j)‖ ≤
      (2 * (∑ i ∈ s, Real.sqrt (μ i)) ^ 2) * C := by
  have hbound (t : ι → Finset ι) (v : ι → ι → E)
      (hv : ∀ i ∈ s, ∀ j ∈ t i, ‖v i j‖ ≤ C) :
      ‖∑ i ∈ s, ∑ j ∈ t i, Real.sqrt (μ i * μ j) • v i j‖ ≤
        (∑ i ∈ s, ∑ j ∈ t i, Real.sqrt (μ i * μ j)) * C := by
    calc
      _ ≤ ∑ i ∈ s, ‖∑ j ∈ t i, Real.sqrt (μ i * μ j) • v i j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, (∑ j ∈ t i, Real.sqrt (μ i * μ j)) * C :=
        Finset.sum_le_sum fun i hi ↦ norm_sum_weight_smul_le_of_norm_le
          (t i) (fun j ↦ Real.sqrt (μ i * μ j)) (fun j _ ↦ Real.sqrt_nonneg _)
          (v i) (hv i hi)
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ ‖∑ i ∈ s, ∑ j ∈ s, Real.sqrt (μ i * μ j) • vplus i j‖ +
        ‖∑ i ∈ s, ∑ j ∈ s.erase i, Real.sqrt (μ i * μ j) • vminus i j‖ := norm_add_le _ _
    _ ≤ (∑ i ∈ s, ∑ j ∈ s, Real.sqrt (μ i * μ j)) * C +
        (∑ i ∈ s, ∑ j ∈ s.erase i, Real.sqrt (μ i * μ j)) * C :=
      add_le_add (hbound (fun _ ↦ s) vplus hp) (hbound (fun i ↦ s.erase i) vminus hm)
    _ = ((∑ i ∈ s, ∑ j ∈ s, Real.sqrt (μ i * μ j)) +
        (∑ i ∈ s, ∑ j ∈ s.erase i, Real.sqrt (μ i * μ j))) * C := (add_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (signed_pair_coefficient_sum_le s μ hμ) hC

end JanetCartan.WeightedFamily
