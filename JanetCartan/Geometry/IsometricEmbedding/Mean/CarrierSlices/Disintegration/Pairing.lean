module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Disintegration.Adjoint

/-!
# Scalar disintegration of the actual carrier normal

The adjoint fibers imply the scalar integral identity in
`app:ch_waves:eq:sampling-prefix-normal`. This is a step toward the operator-valued
Bochner identity; operator-norm integrability remains a separate obligation.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow

variable {n N : ℕ} (d : CarrierData n N) (m : CarrierVariable n → ℝ)
  (h : FiniteCarrierKernelBounds d m)
  (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
  (S : CarrierParameter → CarrierSliceL2 n →L[ℂ] ComplexOutputL2 n)
  (hT : ∀ f, (T f : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume]
    regularizedCarrierIntegral d m f)
  (hS : ∀ z f, (S z f : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume]
    regularizedCarrierSliceIntegral d m z f)

include h hT hS

/-- Scalar matrix coefficients of the actual slice normals are integrable, as a
consequence of the full L² adjoint and its fiber formula
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_inner_carrierSlice_normal (v w : ComplexOutputL2 n) :
    Integrable (fun z ↦ inner ℂ v ((S z ∘L (S z).adjoint) w))
      (volume.prod volume) := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) (T.adjoint v) (T.adjoint w)).integral_prod_left
  apply hi.congr
  filter_upwards [carrier_adjoint_fiber_ae_eq d m h T S hT hS v,
    carrier_adjoint_fiber_ae_eq d m h T S hT hS w] with z hv hw
  change (∫ η, inner ℂ (T.adjoint v (z, η)) (T.adjoint w (z, η))) = _
  rw [ContinuousLinearMap.comp_apply, ← (S z).adjoint_inner_left ((S z).adjoint w) v, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv, hw] with η hvη hwη
  simp only [hvη, hwη]

/-- The actual normal has the integral of the slice-normal matrix coefficients
(`app:ch_waves:eq:sampling-prefix-normal`). No normal identity is assumed. -/
theorem inner_carrier_normal_eq_integral (v w : ComplexOutputL2 n) :
    inner ℂ v ((T ∘L T.adjoint) w) =
      ∫ z, inner ℂ v ((S z ∘L (S z).adjoint) w) ∂volume.prod volume := by
  calc
    _ = inner ℂ (T.adjoint v) (T.adjoint w) :=
      (T.adjoint_inner_left (T.adjoint w) v).symm
    _ = ∫ u, inner ℂ (T.adjoint v u) (T.adjoint w u) ∂carrierMeasure n :=
      L2.inner_def _ _
    _ = ∫ z, ∫ η, inner ℂ (T.adjoint v (z, η)) (T.adjoint w (z, η))
        ∂volume ∂volume.prod volume :=
      integral_prod _ (L2.integrable_inner (𝕜 := ℂ) (T.adjoint v) (T.adjoint w))
    _ = _ := ?_
  apply integral_congr_ae
  filter_upwards [carrier_adjoint_fiber_ae_eq d m h T S hT hS v,
    carrier_adjoint_fiber_ae_eq d m h T S hT hS w] with z hv hw
  rw [ContinuousLinearMap.comp_apply, ← (S z).adjoint_inner_left ((S z).adjoint w) v, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv, hw] with η hvη hwη
  simp only [hvη, hwη]

end JanetCartan.ContinuumRow
