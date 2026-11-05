module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalCarriers
public import JanetCartan.Iteration.PhysicalMean.CarrierOnlyTail
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalNormalSourceTailTemplate

/-!
# First normal summand on the actual uncut inverse datum

The coefficient remains the original positive-density coefficient profile, with
its native derivative shift.  No zero-density estimate is substituted.  The
Fourier cutoff acts only on the carrier inputs; neither image nor exterior
channel is truncated. This is the *source-only* first summand, not the operator
norm of the transport/sampling summands (`new:sec:mean-source-equation`).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalNormalInverse.OriginalNormalSourceTail
open ContinuumRow CoerciveInverse CurrentMean CarrierSobolev PhysicalMean

/-- Full row norm from the same native bound on its physical row. In
particular the exterior channel is paid for once, without an inverse estimate
or a finite sum of newly chosen individual carrier constants. -/
theorem augmentedRow_norm_of_physical {n : ℕ} {ι : Type*} [Fintype ι]
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    {M : ℝ} (hM : ‖physicalRow image U‖ ≤ M) :
    ‖augmentedRow image U ψ‖ ≤ M + ‖1 - ψ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg ((norm_nonneg _).trans hM) (norm_nonneg _))
  intro f
  rw [augmentedRow_apply, add_mul]
  exact (norm_add_le _ _).trans <| add_le_add
    (((physicalRow image U).le_opNorm _).trans (mul_le_mul hM (WithLp.norm_fst_le _ f)
      (norm_nonneg _) ((norm_nonneg _).trans hM)))
    (((exteriorChannel ψ).le_opNorm _).trans (mul_le_mul (exteriorChannel_norm_le ψ)
      (WithLp.norm_snd_le _ f) (norm_nonneg _) (norm_nonneg _)))

/-- Applied to the original native paired bound, this evaluates the leading
source-only normal truncation on the *same* uncut `Q₀ e`, for all smooth
residuals, carrier radii, and orders. The right side below will be the actual
positive-current `Cpair q` times its full retained-coefficient expression.
Neither a bound on all L² data nor a tail estimate is supplied as a premise
(`new:sec:mean-source-equation`). -/
theorem source_tail_from_native_pair {n : ℕ} {ι : Type*} [Fintype ι]
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    {M : ℝ} (hM : ‖physicalRow image U‖ ≤ M) {K : ℝ} (hK : 1 ≤ K)
    (e : SmoothResidual n) (q : ℕ) {B : ℝ}
    (hreg : (augmentedRow image U ψ).adjoint ((augmentedNormal image U ψ).inverse
      (smoothResidualToL2 n e)) ∈ augmentedInputLevel n ι q)
    (hp : (periodicSobolevScale n (Euclidean n)).gradeNorm q
        ((augmentedNormal image U ψ).inverse (smoothResidualToL2 n e)) +
      (augmentedInputSobolevScale n ι).gradeNorm q
        (rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e)) ≤ B) :
    ‖(augmentedNormal image U ψ - leadingCarrierCutNormal image U ψ K)
      ((augmentedNormal image U ψ).inverse (smoothResidualToL2 n e))‖ ≤
      ((M + ‖1 - ψ‖) / K^q) * B := by
  have hrow := augmentedRow_norm_of_physical image U ψ hM
  have hb : (augmentedInputSobolevScale n ι).gradeNorm q ((augmentedRow image U ψ).adjoint
      ((augmentedNormal image U ψ).inverse (smoothResidualToL2 n e))) ≤ B :=
    (le_add_of_nonneg_left ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg q _)).trans hp
  exact (leadingCarrierCutNormal_defect_le image U ψ hK q _ hreg).trans
    (mul_le_mul (div_le_div_of_nonneg_right hrow (pow_nonneg (zero_le_one.trans hK) q)) hb
      ((augmentedInputSobolevScale n ι).gradeNorm_nonneg q _)
      (div_nonneg ((norm_nonneg _).trans hrow) (pow_nonneg (zero_le_one.trans hK) q)))

end JanetCartan.PhysicalNormalInverse.OriginalNormalSourceTail

retain_actual_original_normal_source_tail

end
