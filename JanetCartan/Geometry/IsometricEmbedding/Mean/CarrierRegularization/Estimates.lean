module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierRegularization.Mask
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierRegularization.HilbertSchmidt
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Compact carrier regularizations and their rough size

Consequences of the pointwise geometric inputs to `app:ch_background:eq:bg-T`.
The squared Hilbert–Schmidt bound grows as `R^n`; it is not the uniform
oscillatory bound needed for the uncut continuum row.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.ContinuumRow.CarrierRegularization.MaskHypotheses

variable {n N : ℕ} {d : CarrierData n N} {m : CarrierVariable n → ℝ}
  {Z : Set CarrierParameter} {R M C : ℝ}
  (h : MaskHypotheses d m Z R M C)

/-- Exact convergent Hilbert–Schmidt identity for the actual finite carrier
operator (`app:ch_background:eq:bg-T`). -/
theorem operator_hilbertSchmidt {ι : Type*} (c : HilbertBasis ι ℂ (CarrierL2 n)) :
    IsHilbertSchmidt c h.operator ∧ hilbertSchmidtSq c h.operator =
      ∫ u, ∫ x, ‖maskedKernel d m x u‖ ^ 2 ∂volume ∂carrierMeasure n :=
  boundedKernelOperator_hilbertSchmidt h.maskedKernel_measurable
    (h.compact_parameters.measurableSet.prod measurableSet_closedBall)
    h.mask_support_finite h.maskedKernel_support h.maskedKernel_bound c

/-- Squared-kernel identity with the real mask displayed explicitly
(`app:ch_background:eq:bg-T`). -/
theorem operator_hilbertSchmidtSq_eq {ι : Type*} (c : HilbertBasis ι ℂ (CarrierL2 n)) :
    hilbertSchmidtSq c h.operator =
      ∫ u, (m u) ^ 2 * (∫ x, ‖carrierKernel d x u‖ ^ 2) ∂carrierMeasure n := by
  rw [(h.operator_hilbertSchmidt c).2]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u ↦ by
    simp only [maskedKernel, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, integral_const_mul]

/-- The actual finite-frequency carrier operator is compact
(`app:ch_background:eq:bg-T`). -/
theorem operator_isCompact : IsCompactOperator h.operator :=
  boundedKernelOperator_isCompact h.maskedKernel_measurable
    (h.compact_parameters.measurableSet.prod measurableSet_closedBall)
    h.mask_support_finite h.maskedKernel_support h.maskedKernel_bound

include h
/-- Scaling of the literal initial product measure, including zero-dimensional
frequency space (`app:ch_background:eq:bg-T`). -/
theorem mask_support_volume :
    (carrierMeasure n).real (Z ×ˢ Metric.closedBall 0 R) =
      (volume.prod volume).real Z * R ^ (n - 1) *
        (volume : Measure (Euclidean (n - 1))).real (Metric.closedBall 0 1) := by
  simp only [Measure.real, carrierMeasure, Measure.prod_prod, ENNReal.toReal_mul]
  have hv := Measure.addHaar_real_closedBall' volume (0 : Euclidean (n - 1))
    h.radius_nonneg
  simp only [Measure.real, finrank_euclideanSpace, Fintype.card_fin] at hv
  rw [hv]
  ring

/-- Rough squared-kernel bound `C₀ R^n` from the half-derivative amplitude.
The displayed constant depends only on the fixed parameter support and the
pointwise mask/amplitude bounds (`app:ch_background:eq:bg-T`). -/
theorem squared_kernel_integral_le (hn : 1 ≤ n) :
    (∫ u, ∫ x, ‖maskedKernel d m x u‖ ^ 2 ∂volume ∂carrierMeasure n) ≤
      ((M * C) ^ 2 * (volume.prod volume).real Z *
        (volume : Measure (Euclidean (n - 1))).real (Metric.closedBall 0 1)) * R ^ n := by
  have hpow : R ^ n = R ^ (n - 1) * R := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  calc
    _ ≤ (M * C * Real.sqrt R) ^ 2 *
        (carrierMeasure n).real (Z ×ˢ Metric.closedBall 0 R) :=
      boundedKernelOperator_sq_integral_le h.maskedKernel_measurable
        (h.compact_parameters.measurableSet.prod measurableSet_closedBall)
        h.mask_support_finite h.maskedKernel_support h.maskedKernel_bound
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt h.radius_nonneg, h.mask_support_volume, hpow]
      ring

/-- The same rough bound for the convergent squared Hilbert–Schmidt norm
(`app:ch_background:eq:bg-T`). -/
theorem operator_hilbertSchmidtSq_le (hn : 1 ≤ n) {ι : Type*}
    (c : HilbertBasis ι ℂ (CarrierL2 n)) :
    hilbertSchmidtSq c h.operator ≤
      ((M * C) ^ 2 * (volume.prod volume).real Z *
        (volume : Measure (Euclidean (n - 1))).real (Metric.closedBall 0 1)) * R ^ n := by
  rw [(h.operator_hilbertSchmidt c).2]
  exact h.squared_kernel_integral_le hn

/-- A rough squared operator norm bound; its radius dependence must be
replaced by the oscillatory estimate before removing the mask
(`app:ch_background:eq:bg-T`). -/
theorem operator_norm_sq_le (hn : 1 ≤ n) :
    ‖h.operator‖ ^ 2 ≤
      ((M * C) ^ 2 * (volume.prod volume).real Z *
        (volume : Measure (Euclidean (n - 1))).real (Metric.closedBall 0 1)) * R ^ n := by
  obtain ⟨_, c, _⟩ := exists_hilbertBasis ℂ (CarrierL2 n)
  have hh := (h.operator_hilbertSchmidt c).1
  have hnonneg : 0 ≤ hilbertSchmidtSq c h.operator :=
    tsum_nonneg (fun _ ↦ sq_nonneg _)
  calc
    _ ≤ hilbertSchmidtSq c h.operator := by
      have hs := pow_le_pow_left₀ (norm_nonneg _) hh.opNorm_le 2
      rwa [Real.sq_sqrt hnonneg] at hs
    _ ≤ _ := h.operator_hilbertSchmidtSq_le hn c

end JanetCartan.ContinuumRow.CarrierRegularization.MaskHypotheses
