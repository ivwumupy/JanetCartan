module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Tests
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierRegularization

/-!
# The constructed finite carrier normal

The compact carrier producer now supplies the individual action and adjoint
identities. This leaf instantiates the kernel calculation with that actual
operator, leaving only its primitive mask hypotheses, as required by
`app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.ContinuumRow.TransportKernel

variable {n N : ℕ} {d : CarrierData n N} {m : CarrierVariable n → ℝ}
  {Z : Set CarrierParameter} {R M C : ℝ}
  (h : CarrierRegularization.MaskHypotheses d m Z R M C)

/-- The primitive finite-mask inputs imply the shared finite-band kernel bounds.
This discharges the Fubini inputs for the constructed carrier normal in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def finiteCarrierKernelBoundsOfMask : FiniteCarrierKernelBounds d m where
  carrierSupport := Z
  isCompact_carrierSupport := h.compact_parameters
  frequencyRadius := R
  frequencyRadius_nonneg := h.radius_nonneg
  bound := M * C * Real.sqrt R
  bound_nonneg := mul_nonneg (mul_nonneg h.mask_bound_nonneg h.amplitude_bound_nonneg)
    (Real.sqrt_nonneg R)
  stronglyMeasurable := h.maskedKernel_measurable
  norm_le := h.maskedKernel_bound
  eq_zero := by
    intro x z η hz
    apply h.maskedKernel_support
    simpa only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right,
      not_and_or, not_le] using hz

/-- Matrix kernel of the actual compact operator and its literal Hilbert adjoint,
on all output L² data (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedOperator_normal_eq_matrix (w : ComplexOutputL2 n) :
    ∀ᵐ x ∂volume, ∀ i, h.operator (h.operator.adjoint w) x i =
      ∑ j, ∫ y, regularizedNormalEntry d m x y i j * w y j :=
  carrierHilbertNormal_eq_matrix (finiteCarrierKernelBoundsOfMask h)
    h.operator h.operator_ae w (h.operator_adjoint_ae w)

/-- The literal normal test pairing of the constructed compact operator.
No action or adjoint realization remains to be assumed
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedOperator_normalTestPairing (v w : ComplexOutputL2 n) :
    normalTestPairing d m v w = inner ℂ (h.operator.adjoint v) (h.operator.adjoint w) :=
  normalTestPairing_eq_adjoint_inner (finiteCarrierKernelBoundsOfMask h)
    h.operator h.operator_ae v w (h.operator_adjoint_ae w)

/-- The factor four for both real quadratures of the constructed carrier,
with the literal matrix kernel (`app:ch_background:eq:bg-real-symbol`). -/
theorem regularizedOperator_realNormal_pairing (r s : OutputL2 n) :
    inner ℝ r (realQuadratureChannel h.operator
      ((realQuadratureChannel h.operator).adjoint s)) =
      4 * (normalTestPairing d m (l2ComplexInclusion volume r)
        (l2ComplexInclusion volume s)).re :=
  realCarrierNormal_pairing (finiteCarrierKernelBoundsOfMask h)
    h.operator h.operator_ae r s (h.operator_adjoint_ae _)

end JanetCartan.ContinuumRow.TransportKernel
