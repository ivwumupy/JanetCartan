module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.SupportedBudgets
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Inverse-frequency comparison of the actual background polynomial

The comparison adjacent to `app:ch_waves:eq:background-quadrature` uses the
smooth polynomial through inverse frequency zero. Its first joint jet is
already supplied by the retained immersion/scalar profiles. At zero,
`backgroundPolynomial_zero` identifies the original transported tensor.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.Sampling.RetainedBackground
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

variable {W V : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The first joint jet controls the inverse-frequency difference on the
whole fixed interval, including zero. This is the pointwise input of the
colored-to-transport `O(λ⁻¹)` comparison following
`app:ch_waves:eq:background-quadrature`. -/
theorem norm_inverseFrequency_sub_zero_le
    {H : ℝ × W → V} (hH : ContDiff ℝ ∞ H) {C : ℝ}
    (hj : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w,
      ‖iteratedFDeriv ℝ 1 H (τ, w)‖ ≤ C)
    {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (w : W) :
    ‖H (τ, w) - H (0, w)‖ ≤ C * |τ| := by
  have hd (t : ℝ) : DifferentiableAt ℝ (fun s ↦ H (s, w)) t :=
    (hH.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t
  have hb (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ‖fderiv ℝ (fun s ↦ H (s, w)) t‖ ≤ C := by
    let A := ContinuousLinearMap.inl ℝ ℝ W
    have hh := norm_iteratedFDeriv_preAffine_le A (0, w) isOpen_univ
      hH.contDiffOn (x := t) (mem_univ _) 1
    have hh' : ‖fderiv ℝ (fun s ↦ H (s, w)) t‖ ≤
        ‖iteratedFDeriv ℝ 1 H (t, w)‖ * ‖A‖ := by
      simpa [A, norm_iteratedFDeriv_one] using hh
    exact (hh'.trans (mul_le_of_le_one_right (norm_nonneg _)
      (ContinuousLinearMap.norm_inl_le_one ..))).trans (hj t ht w)
  simpa only [sub_zero, Real.norm_eq_abs] using
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_fderiv_le
      (x := 0) (y := τ) (fun t _ ↦ hd t) hb (by constructor <;> norm_num) hτ

/-- The low retained reserve removes every amplitude-scale factor from the
first inverse-frequency jet. This directly consumes the output of
`exists_retained_supportedBackground_budgets` in the comparison following
`app:ch_waves:eq:background-quadrature`. -/
theorem norm_inverseFrequency_sub_zero_le_of_joint_budgets
    {H : ℝ × W → V} (hH : ContDiff ℝ ∞ H) {A : ℕ → ℝ}
    {L : ℝ} {rpar : ℕ} (hrpar : 1 ≤ rpar)
    (hj : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ j,
      ‖iteratedFDeriv ℝ j H (τ, w)‖ ≤ A j * L ^ (j - rpar))
    {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (w : W) :
    ‖H (τ, w) - H (0, w)‖ ≤ A 1 * |τ| := by
  apply norm_inverseFrequency_sub_zero_le hH _ hτ w
  intro t ht y
  simpa [Nat.sub_eq_zero_of_le hrpar] using hj t ht y 1

/-- The unchanged radial inverse frequency lies in the fixed comparison
interval and costs at most `λ⁻¹`, uniformly in all radial labels. Consumer:
the colored-to-transport comparison after
`app:ch_waves:eq:background-quadrature`. -/
theorem norm_radial_inverseFrequency_sub_zero_le
    {H : ℝ × W → V} (hH : ContDiff ℝ ∞ H) {A : ℕ → ℝ}
    (hA : 0 ≤ A 1) {L : ℝ} {rpar : ℕ} (hrpar : 1 ≤ rpar)
    (hj : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ j,
      ‖iteratedFDeriv ℝ j H (τ, w)‖ ≤ A j * L ^ (j - rpar))
    {R lam : ℝ} (hR : 1 ≤ R) (hlam : 1 ≤ lam) (w : W) :
    ‖H ((R * lam)⁻¹, w) - H (0, w)‖ ≤ A 1 * lam⁻¹ := by
  have hprod : 1 ≤ R * lam := one_le_mul_of_one_le_of_one_le hR hlam
  have hτ : (R * lam)⁻¹ ∈ Icc (-1 : ℝ) 1 :=
    ⟨le_trans (by norm_num) (inv_nonneg.mpr (by linarith)),
      inv_le_one_of_one_le₀ hprod⟩
  apply (norm_inverseFrequency_sub_zero_le_of_joint_budgets hH hrpar hj hτ w).trans
  rw [abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ hA
  exact inv_anti₀ (by linarith) (le_mul_of_one_le_left (by linarith) hR)

end JanetCartan.Sampling.RetainedBackground
