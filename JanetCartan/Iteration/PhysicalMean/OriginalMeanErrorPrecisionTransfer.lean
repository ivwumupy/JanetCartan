module
public import JanetCartan.Iteration.PhysicalMean.SourcePrecision
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.ProjectedResidualBound
/-!
# Pointwise transfer of the exact residual precision

Actual115 controls the C1 norm of the SAME residual used in actual58/59 mean
error. Periodicity gives the pointwise bound everywhere without a fictitious
extra cell hypothesis. The fixed frame cost stays explicit, or is paid by a
CURRENT-stage reach and one extra accuracy order, never by an N-dependent
initial threshold (`new:eq:mean-error-formula`, `main:eq:mean-equation`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalMean.OriginalMeanErrorPrecisionTransfer
open CurrentMean UniformStep

/-- The actual residual C1 seminorm controls its exact torus value everywhere;
no replacement source or different representative is introduced. -/
theorem residual_pointwise_everywhere {n : ℕ} (u : SmoothResidual n) (A : ℝ)
    (h : cNorm (fundamentalCell n) 1 (periodicLift (fun z ↦ u.val z ())) ≤ A)
    (x : Euclidean n) : ‖u.val (torusQuotient x) ()‖ ≤ A := by
  exact ((SmoothPeriodicFamily.smooth u ()).norm_le_cNorm_zero (torusQuotient x)).trans
    ((cNorm_mono_order (s := fundamentalCell n) (f := periodicLift (fun z ↦ u.val z ()))
      (show 0 ≤ 1 by omega)).trans h)

/-- Keep the genuine fixed frame coefficient in the literal physical error
bound. Actual58/59 supplies herror, actual115 supplies hprecision. -/
theorem physical_error_of_residual_cNorm {n : ℕ} (hn : 5 ≤ n)
    (u : SmoothResidual n) (E : MetricTensor n) (x : Euclidean n) (A : ℝ)
    (herror : ‖E‖ ≤ projectedStressResidualConstant hn * ‖u.val (torusQuotient x) ()‖)
    (hprecision : cNorm (fundamentalCell n) 1 (periodicLift (fun z ↦ u.val z ())) ≤ A) :
    ‖E‖ ≤ projectedStressResidualConstant hn * A :=
  herror.trans (mul_le_mul_of_nonneg_left (residual_pointwise_everywhere u A hprecision x)
    (projectedStressResidualConstant_pos hn).le)

/-- A frame factor may be absorbed by CURRENT R≥Cframe at accuracy+1.
This introduces no new initial geometric threshold or analytic assumption. -/
theorem frame_error_le_requested_precision {e C R accuracy : ℝ}
    (hR : 1 ≤ R) (hC : C ≤ R) (he : e ≤ C*R^(-(accuracy+1))) :
    e ≤ R^(-accuracy) := by
  have hp : 0 < R := zero_lt_one.trans_le hR
  calc
    e ≤ C*R^(-(accuracy+1)) := he
    _ ≤ R*R^(-(accuracy+1)) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hp.le _)
    _ = R^(1 + (-(accuracy+1))) := by rw [Real.rpow_add hp,Real.rpow_one]
    _ = R^(-accuracy) := by congr 1; ring

end JanetCartan.PhysicalMean.OriginalMeanErrorPrecisionTransfer
end
