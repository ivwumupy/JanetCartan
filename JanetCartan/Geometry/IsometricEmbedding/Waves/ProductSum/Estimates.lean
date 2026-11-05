module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.ProductSum.Algebra

import Mathlib.Tactic.Ring

/-!
# Conditional estimates for the complete signed sum

Finite assembly in `app:ch_pairs:prop:pairs-lag-sum`. The normed range of an
observation map can represent an `H^s` space, including restriction to `D` or
physical cutoff and passage to the torus. No choice of matrix norm is made here.
Each hypothesis bounds an individual **complete** source through the same map.
-/

@[expose] public noncomputable section

namespace JanetCartan.ProductSum

variable {ι V E : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weighted assembly of full-source bounds through one fixed linear map,
the finite triangle inequality in `app:ch_pairs:prop:pairs-lag-sum`. -/
theorem norm_map_weightedSignedSum_le (L : V →ₗ[ℝ] E) (b : ℝ) (μ : ι → ℝ)
    (hμ : ∀ j, 0 ≤ μ j) (plus minus : ι → ι → V)
    {C : ℝ} (hC : 0 ≤ C) (hp : ∀ j k, ‖L (plus j k)‖ ≤ C)
    (hm : ∀ j k, k ≠ j → ‖L (minus j k)‖ ≤ C) :
    ‖L (weightedSignedSum b μ plus minus)‖ ≤
      2 * C * b ^ 2 * coefficientMass μ := by
  rw [map_weightedSignedSum, weightedSignedSum, norm_smul,
    Real.norm_of_nonneg (sq_nonneg b)]
  calc
    _ ≤ b ^ 2 * ((2 * (∑ j, Real.sqrt (μ j)) ^ 2) * C) :=
      mul_le_mul_of_nonneg_left
        (WeightedFamily.norm_signed_pair_sum_le Finset.univ μ (fun j _ ↦ hμ j)
          (fun j k ↦ L (plus j k)) (fun j k ↦ L (minus j k)) hC
          (fun j _ k _ ↦ hp j k)
          (fun j _ k hk ↦ hm j k (Finset.mem_erase.mp hk).1)) (sq_nonneg b)
    _ = _ := by unfold coefficientMass; ring

/-- True-scale decay implies beat-scale decay, used in
`app:ch_pairs:eq:pairs-lag-sum-error`. Natural accuracy orders include zero. -/
theorem inverse_pow_le_of_scale_le {a ρ : ℝ} (ha : 0 < a) (hρ : a ≤ ρ) (Q : ℕ) :
    (ρ ^ Q)⁻¹ ≤ (a ^ Q)⁻¹ := by
  simpa only [one_div] using
    one_div_le_one_div_of_le (pow_pos ha Q) (pow_le_pow_left₀ ha.le hρ Q)

/-- Summing the individual error estimates
`app:ch_pairs:eq:pairs-lag-one-error` at their true frequencies gives the
beat lower bound `c lambda h`, with the explicit constant `2 C c⁻Q`.
Both signed families use the same `L` (in applications, `Dγ ∘ S + restriction`). -/
theorem error_bound_of_individual (L : V →ₗ[ℝ] E) (b : ℝ) (μ : ι → ℝ)
    (hμ : ∀ j, 0 ≤ μ j) (plus minus : ι → ι → V)
    (ρplus ρminus : ι → ι → ℝ) {lambda h c C : ℝ}
    (hlambda : 0 < lambda) (hh : 0 < h) (hc : 0 < c) (hC : 0 ≤ C) (Q : ℕ)
    (hρp : ∀ j k, c * (lambda * h) ≤ ρplus j k)
    (hρm : ∀ j k, k ≠ j → c * (lambda * h) ≤ ρminus j k)
    (hp : ∀ j k, ‖L (plus j k)‖ ≤ C * ((ρplus j k) ^ Q)⁻¹)
    (hm : ∀ j k, k ≠ j → ‖L (minus j k)‖ ≤ C * ((ρminus j k) ^ Q)⁻¹) :
    ‖L (weightedSignedSum b μ plus minus)‖ ≤
      (2 * C * (c ^ Q)⁻¹) * b ^ 2 * coefficientMass μ * ((lambda * h) ^ Q)⁻¹ := by
  have ha : 0 < c * (lambda * h) := mul_pos hc (mul_pos hlambda hh)
  have hp' (j k : ι) : ‖L (plus j k)‖ ≤ C * ((c * (lambda * h)) ^ Q)⁻¹ :=
    (hp j k).trans (mul_le_mul_of_nonneg_left
      (inverse_pow_le_of_scale_le ha (hρp j k) Q) hC)
  have hm' (j k : ι) (hjk : k ≠ j) :
      ‖L (minus j k)‖ ≤ C * ((c * (lambda * h)) ^ Q)⁻¹ :=
    (hm j k hjk).trans (mul_le_mul_of_nonneg_left
      (inverse_pow_le_of_scale_le ha (hρm j k hjk) Q) hC)
  calc
    _ ≤ 2 * (C * ((c * (lambda * h)) ^ Q)⁻¹) * b ^ 2 * coefficientMass μ :=
      norm_map_weightedSignedSum_le L b μ hμ plus minus
        (mul_nonneg hC (inv_nonneg.mpr (pow_nonneg ha.le Q))) hp' hm'
    _ = _ := by rw [mul_pow, mul_inv_rev]; ring

/-- The ambient size estimate has carrier power `lambda^(s+1)`, independently of
the beat `h`, in `app:ch_pairs:eq:pairs-lag-sum-size`. The observation map may
include the fixed physical output cutoff. -/
theorem size_bound_of_individual (L : V →ₗ[ℝ] E) (b : ℝ) (μ : ι → ℝ)
    (hμ : ∀ j, 0 ≤ μ j) (plus minus : ι → ι → V)
    {lambda C : ℝ} (hlambda : 0 ≤ lambda) (hC : 0 ≤ C) (s : ℕ)
    (hp : ∀ j k, ‖L (plus j k)‖ ≤ C * lambda ^ (s + 1))
    (hm : ∀ j k, k ≠ j → ‖L (minus j k)‖ ≤ C * lambda ^ (s + 1)) :
    ‖L (weightedSignedSum b μ plus minus)‖ ≤
      (2 * C) * b ^ 2 * coefficientMass μ * lambda ^ (s + 1) := by
  calc
    _ ≤ 2 * (C * lambda ^ (s + 1)) * b ^ 2 * coefficientMass μ :=
      norm_map_weightedSignedSum_le L b μ hμ plus minus
        (mul_nonneg hC (pow_nonneg hlambda _)) hp hm
    _ = _ := by ring

omit [DecidableEq ι] in
/-- Replacing the exact coefficient mass by `M Cμ` loses just one sample-count
power (`app:ch_pairs:prop:pairs-lag-sum`), with physical amplitude exactly `b²`. -/
theorem bound_by_sample_count (μ : ι → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    {Cμ C B b N : ℝ} (hmass : ∑ j, μ j ≤ Cμ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hN : N ≤ C * b ^ 2 * coefficientMass μ * B) :
    N ≤ C * b ^ 2 * (Fintype.card ι * Cμ) * B :=
  hN.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (coefficientMass_le_card_mul μ hμ hmass)
      (mul_nonneg hC (sq_nonneg b))) hB)

end JanetCartan.ProductSum
