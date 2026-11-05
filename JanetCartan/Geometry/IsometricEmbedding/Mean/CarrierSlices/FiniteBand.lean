module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Kernel

/-!
# Analytic inputs for finite-band carrier disintegration

This leaf specifies the common-kernel hypotheses for the operator version of
`app:ch_waves:eq:sampling-prefix-normal`. It contains only geometric support,
measurability, and pointwise size inputs. It assumes no adjoint identity,
operator normal identity, or existence of a geometric carrier family.

The actual inputs must be supplied by the carrier-regularization, sampling-kernel,
raw-input Hilbert, and leading-wave producers. The finite radius is essential:
the uncut half-derivative carrier kernel is outside this interface.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow

/-- Uniform bounded compact support for the literal masked kernel of
`app:ch_background:eq:bg-T`, used to justify the finite-band disintegration in
`app:ch_waves:eq:sampling-prefix-normal`. Compact measurement is already retained
in `carrierKernel`. These are analytic inputs, not operator conclusions. -/
structure FiniteCarrierKernelBounds {n N : ℕ} (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) where
  carrierSupport : Set CarrierParameter
  isCompact_carrierSupport : IsCompact carrierSupport
  frequencyRadius : ℝ
  frequencyRadius_nonneg : 0 ≤ frequencyRadius
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  stronglyMeasurable : StronglyMeasurable
    (fun p : Torus n × CarrierVariable n ↦ maskedCarrierKernel d m p.1 p.2)
  norm_le : ∀ x u, ‖maskedCarrierKernel d m x u‖ ≤ bound
  eq_zero : ∀ x z η, z ∉ carrierSupport ∨ frequencyRadius < ‖η‖ →
    maskedCarrierKernel d m x (z, η) = 0

end JanetCartan.ContinuumRow
