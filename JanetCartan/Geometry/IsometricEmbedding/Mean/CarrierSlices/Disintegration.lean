module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Disintegration.Pairing
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Disintegration.OperatorIntegrability
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Disintegration.NormalKernel

/-!
# Finite-band normal disintegration

For `app:ch_background:eq:bg-T` and `app:ch_waves:eq:sampling-prefix-normal`,
the forward AE formulas and finite-band compact kernel bounds determine the actual
adjoints, their fibers, and the normal's matrix kernel. They also imply Bochner
integrability in operator norm and identify the full normal with the integral of
the slice normals, both in carrier and standard sampling coordinates.

These deductions assume only the given operators' forward formulas and
`FiniteCarrierKernelBounds`; the analytic producers must supply those inputs.
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

include h hS in
/-- The actual slice normals are Bochner integrable in standard sampling
Lebesgue coordinates (`app:ch_waves:eq:sampling-prefix-normal`). This supplies
integrability for the downstream finite-prefix normal assembly. -/
theorem integrable_carrierSlice_sampling_normal :
    Integrable (fun z : SeparatedSampling.Point ↦
      S (carrierSamplingEquiv.symm z) ∘L (S (carrierSamplingEquiv.symm z)).adjoint) volume :=
  carrierSamplingEquiv_measurePreserving.symm.integrable_comp_of_integrable
    (integrable_carrierSlice_normal h S hS)

include h hT hS

/-- Operator assembly from scalar disintegration and operator-norm integrability
(`app:ch_waves:eq:sampling-prefix-normal`). The theorem `carrier_normal_eq_integral`
below discharges `hA` using `integrable_carrierSlice_normal`. -/
theorem carrier_normal_eq_integral_of_integrable
    (hA : Integrable (fun z ↦ S z ∘L (S z).adjoint) (volume.prod volume)) :
    T ∘L T.adjoint = ∫ z, S z ∘L (S z).adjoint ∂volume.prod volume := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro v
  calc
    _ = ∫ z, inner ℂ v ((S z ∘L (S z).adjoint) w) ∂volume.prod volume :=
      inner_carrier_normal_eq_integral d m h T S hT hS v w
    _ = _ := by
      rw [ContinuousLinearMap.integral_apply hA w]
      exact integral_inner (hA.apply_continuousLinearMap w) v

/-- The same operator assembly in standard sampling coordinates
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem carrier_normal_eq_sampling_integral_of_integrable
    (hA : Integrable (fun z ↦ S z ∘L (S z).adjoint) (volume.prod volume)) :
    T ∘L T.adjoint = ∫ z : SeparatedSampling.Point,
      S (carrierSamplingEquiv.symm z) ∘L (S (carrierSamplingEquiv.symm z)).adjoint := by
  rw [carrier_normal_eq_integral_of_integrable d m h T S hT hS hA]
  simpa only [MeasurableEquiv.symm_apply_apply] using
    integral_carrierSamplingEquiv (fun z ↦
      S (carrierSamplingEquiv.symm z) ∘L (S (carrierSamplingEquiv.symm z)).adjoint)

/-- The actual finite-band normal is the Bochner integral of its actual slice
normals (`app:ch_background:eq:bg-T`, `app:ch_waves:eq:sampling-prefix-normal`).
The forward AE formulas and compact kernel bounds supply all adjoint,
measurability, and integrability facts used in this identity. -/
theorem carrier_normal_eq_integral :
    T ∘L T.adjoint = ∫ z, S z ∘L (S z).adjoint ∂volume.prod volume :=
  carrier_normal_eq_integral_of_integrable d m h T S hT hS
    (integrable_carrierSlice_normal h S hS)

/-- The actual finite-band normal in standard sampling Lebesgue coordinates
(`app:ch_waves:eq:sampling-prefix-normal`). The equivalence changes only the
carrier parameter; torus output and Euclidean transverse measures are preserved. -/
theorem carrier_normal_eq_sampling_integral :
    T ∘L T.adjoint = ∫ z : SeparatedSampling.Point,
      S (carrierSamplingEquiv.symm z) ∘L (S (carrierSamplingEquiv.symm z)).adjoint :=
  carrier_normal_eq_sampling_integral_of_integrable d m h T S hT hS
    (integrable_carrierSlice_normal h S hS)

end JanetCartan.ContinuumRow
