module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.Construction

/-!
# Fatou on the literal carrier adjoint

The finite complex normal bounds supplied by
`exists_carrierL2Extension_and_uniformNormals_of_primitiveNorms` imply square
integrability of the literal uncut adjoint on every complex output. This is the
membership input for `carrierRealization_adjoint_eq_literal`, in
`app:ch_background:prop:bg-frame`, Step 1. Parameter truncation is removed using
the angular support before taking the pointwise limit.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
variable {n N : ℕ} {d : CarrierData n N}
    {Z : Set CarrierParameter} (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    {κ : ℝ → ℝ} (hκone : ∀ t ∈ Icc (0 : ℝ) 1, κ t = 1)
    {R : ℕ → ℝ} {M Cmask : ℝ}
    (hmask : ∀ k : ℕ, CarrierRegularization.MaskHypotheses d
      (parameterTruncatedMask Z (radialCarrierMask κ (k + 1))) Z (R k) M Cmask)

include hZ hκone

/-- The finite Hilbert adjoints converge almost everywhere to the literal
uncut adjoint, on the original carrier measure (`app:ch_background:eq:bg-T`).
No uncut membership is used. Consumer: the carrier-adjoint Fatou argument. -/
theorem parameterRegularizedOperator_adjoint_tendsto_ae (w : ComplexOutputL2 n) :
    ∀ᵐ u ∂carrierMeasure n, Tendsto (fun k ↦ (hmask k).operator.adjoint w u)
      atTop (𝓝 (carrierAdjointIntegral d w u)) := by
  filter_upwards [ae_all_iff.mpr
    (fun k ↦ parameterRegularizedOperator_adjoint_ae hZ (hmask k) w)] with u hu
  apply tendsto_const_nhds.congr'
  filter_upwards [radialCarrierMask_eventually_eq_one κ hκone {u} isCompact_singleton]
    with k hk
  simp [hu k, hk u (mem_singleton u)]

/-- Uniform bounds on the actual finite complex normals give L² membership
and the square-root bound for the literal adjoint of every complex output.
The producer is `exists_carrierL2Extension_and_uniformNormals_of_primitiveNorms`;
the consumer is `carrierRealization_adjoint_eq_literal`.
Source: `app:ch_background:prop:bg-frame`, Step 1 and `app:ch_background:eq:bg-realification`. -/
theorem carrierAdjointIntegral_memLp_bound_of_uniformNormals
    {B : ℝ} (hB : 0 ≤ B)
    (hnormal : ∀ k, ‖(hmask k).operator.comp (hmask k).operator.adjoint‖ ≤ B)
    (w : ComplexOutputL2 n) :
    MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n) ∧
      (eLpNorm (carrierAdjointIntegral d w) 2 (carrierMeasure n)).toReal ≤
        Real.sqrt B * ‖w‖ := by
  have hl := parameterRegularizedOperator_adjoint_tendsto_ae hZ hκone hmask w
  have hm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun k ↦ Lp.aestronglyMeasurable ((hmask k).operator.adjoint w)) hl
  have hb (k) : ‖(hmask k).operator.adjoint w‖ ≤ Real.sqrt B * ‖w‖ := by
    have ht := norm_carrierRegularization_le (hmask k).operator
      ((hmask k).operator.comp (hmask k).operator.adjoint) hB rfl (hnormal k)
    exact ((hmask k).operator.adjoint.le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (by simpa using ht) (norm_nonneg _))
  have he : eLpNorm (carrierAdjointIntegral d w) 2 (carrierMeasure n) ≤
      ENNReal.ofReal (Real.sqrt B * ‖w‖) := by
    apply Lp.eLpNorm_le_of_ae_tendsto _
      (fun k ↦ Lp.aestronglyMeasurable ((hmask k).operator.adjoint w)) hm hl
    apply Eventually.of_forall
    intro k
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top ((hmask k).operator.adjoint w))]
    change ENNReal.ofReal ‖(hmask k).operator.adjoint w‖ ≤ _
    exact ENNReal.ofReal_le_ofReal (hb k)
  exact ⟨he.trans_lt ENNReal.ofReal_lt_top,
    ENNReal.toReal_le_of_le_ofReal (by positivity) he⟩

end JanetCartan.ContinuumRow.CarrierNormalRealization
