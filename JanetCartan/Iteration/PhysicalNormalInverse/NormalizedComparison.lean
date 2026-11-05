module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.OriginalCarrierPrefix
public import JanetCartan.Iteration.PhysicalNormalInverse.MeanFrontend

/-!
# Exact Fourier normalization of the corrected-normal transport term

The literal zero-endpoint identity is supplied by
`leadingCrossTransportPrefix_normal_eq_original`; the real colored transport
estimate is the second conclusion of `FullComparison`. Their combination pays
exactly `4 * cF⁻² * Ccompare`, with `cF = (2*pi)^(-n/2)`. It does not replace the
rounded squared carrier cutoff or the native current inverse.

These are algebraic consequences of those two producers. The actual full
corrected response and colored comparison must still be instantiated by the
original-data parent (`app:ch_mean_pairs:eq:mean-normal-comparison`,
`new:sec:mean-source-equation`). No sampling or leading-source-tail bound is
included in this middle term.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

namespace JanetCartan.PhysicalNormalInverse
open PeriodicLocalL2 ContinuumRow

variable {n : ℕ}
local notation "cF" => ((2 * Real.pi) ^ (-(n : ℝ) / 2))

/-- The exact original-prefix identity converts the real colored comparison
into the native raw-integral normal convention. The auxiliary/exterior normal
is identical on both sides and cancels without truncation. -/
theorem original_corrected_normal_comparison_of_real_transport
    (E E₀ : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (N₀ auxiliary : OutputL2 n →L[ℝ] OutputL2 n)
    {Ccompare lam Λ h : ℝ}
    (hOriginal : transferOperator ((4 : ℝ) • realOutputCompression E₀) = cF ^ 2 • N₀)
    (hCompare : ‖(4 : ℝ) • realOutputCompression E -
      (4 : ℝ) • realOutputCompression E₀‖ ≤ 4 * (Ccompare * lam⁻¹ * Λ / h)) :
    ‖(auxiliary + N₀) -
      (auxiliary + (cF⁻¹) ^ 2 • transferOperator ((4 : ℝ) • realOutputCompression E))‖ ≤
        (4 * (cF⁻¹) ^ 2 * Ccompare) * lam⁻¹ * Λ / h := by
  have hcF : cF ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hNormalize : (cF⁻¹) ^ 2 • transferOperator ((4 : ℝ) • realOutputCompression E₀) = N₀ := by
    rw [hOriginal, smul_smul, ← mul_pow, inv_mul_cancel₀ hcF, one_pow, one_smul]
  have hTransfer :
      transferOperator ((4 : ℝ) • realOutputCompression E₀) -
        transferOperator ((4 : ℝ) • realOutputCompression E) =
      transferOperator ((4 : ℝ) • realOutputCompression E₀ -
        (4 : ℝ) • realOutputCompression E) := by
    simp only [transferOperator, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [add_sub_add_left_eq_sub, ← hNormalize]
  have hSmul : (cF⁻¹) ^ 2 • transferOperator ((4 : ℝ) • realOutputCompression E₀) -
      (cF⁻¹) ^ 2 • transferOperator ((4 : ℝ) • realOutputCompression E) =
      (cF⁻¹) ^ 2 • (transferOperator ((4 : ℝ) • realOutputCompression E₀) -
        transferOperator ((4 : ℝ) • realOutputCompression E)) :=
    (smul_sub ((cF⁻¹) ^ 2) _ _).symm
  rw [hSmul, norm_smul, Real.norm_of_nonneg (sq_nonneg _), hTransfer]
  calc
    _ ≤ (cF⁻¹) ^ 2 * ‖(4 : ℝ) • realOutputCompression E₀ -
        (4 : ℝ) • realOutputCompression E‖ :=
      mul_le_mul_of_nonneg_left (norm_transferOperator_le _) (sq_nonneg _)
    _ ≤ (cF⁻¹) ^ 2 * (4 * (Ccompare * lam⁻¹ * Λ / h)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simpa only [norm_sub_rev] using hCompare
    _ = _ := by ring

attribute [local irreducible] ContinuousLinearMap.inverse augmentedNormal imageChannel

/-- The literal second summand of `current_mean_defect_split_three`, evaluated
on the SAME uncut current inverse and an arbitrary source. Only this normal
transport term receives an all-L² bound; the leading tail stays source-only. -/
theorem original_corrected_normal_middle_term_bound
    (E E₀ : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (N₀ auxiliary : OutputL2 n →L[ℝ] OutputL2 n)
    {Ccompare lam Λ h : ℝ}
    (hOriginal : transferOperator ((4 : ℝ) • realOutputCompression E₀) = cF ^ 2 • N₀)
    (hCompare : ‖(4 : ℝ) • realOutputCompression E -
      (4 : ℝ) • realOutputCompression E₀‖ ≤ 4 * (Ccompare * lam⁻¹ * Λ / h))
    {ν : Type*} [Fintype ν]
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (e : OutputL2 n) :
    ‖((auxiliary + N₀) -
      (auxiliary + (cF⁻¹) ^ 2 • transferOperator ((4 : ℝ) • realOutputCompression E)))
        ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse e)‖ ≤
      ((4 * (cF⁻¹) ^ 2 * Ccompare) * lam⁻¹ * Λ / h) *
        ‖(augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse e‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (original_corrected_normal_comparison_of_real_transport E E₀ N₀ auxiliary hOriginal hCompare)
      (norm_nonneg _))

end JanetCartan.PhysicalNormalInverse
