module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.FiniteBand
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Compact bounds for carrier disintegration

These consequences of the finite-band bounds supply the integrability used by the
adjoint and normal identities in `app:ch_background:eq:bg-T` and
`app:ch_waves:eq:sampling-prefix-normal`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow.FiniteCarrierKernelBounds

variable {n N : ℕ} {d : CarrierData n N} {m : CarrierVariable n → ℝ}
variable (h : FiniteCarrierKernelBounds d m)

include h

/-- Compact initial support for the finite-band kernel of `app:ch_background:eq:bg-T`. -/
def initialSupport : Set (CarrierVariable n) :=
  h.carrierSupport ×ˢ Metric.closedBall 0 h.frequencyRadius

/-- Compactness supplies finite initial measure in `app:ch_background:eq:bg-T`. -/
theorem isCompact_initialSupport : IsCompact h.initialSupport :=
  h.isCompact_carrierSupport.prod (isCompact_closedBall _ _)

/-- Literal kernel support, used by both adjoint and normal Fubini arguments
(`app:ch_background:eq:bg-T`). -/
theorem kernel_eq_zero_off_initialSupport (x : Torus n) (u : CarrierVariable n)
    (hu : u ∉ h.initialSupport) : maskedCarrierKernel d m x u = 0 := by
  apply h.eq_zero
  simpa only [initialSupport, Set.mem_prod, Metric.mem_closedBall, dist_zero_right,
    not_and_or, not_le] using hu

/-- Compact support of every input section (`app:ch_background:eq:bg-T`). -/
theorem hasCompactSupport_kernel_input (x : Torus n) :
    HasCompactSupport (maskedCarrierKernel d m x) :=
  HasCompactSupport.intro h.isCompact_initialSupport (h.kernel_eq_zero_off_initialSupport x)

/-- Compact transverse support of every fixed-carrier section
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem hasCompactSupport_kernel_slice (x : Torus n) (z : CarrierParameter) :
    HasCompactSupport (fun η ↦ maskedCarrierKernel d m x (z, η)) := by
  apply HasCompactSupport.intro (isCompact_closedBall 0 h.frequencyRadius)
  intro η hη
  exact h.eq_zero x z η (Or.inr (by simpa using hη))

/-- Measurability of an input section, needed for the adjoint pairing
(`app:ch_background:eq:bg-T`). -/
theorem stronglyMeasurable_kernel_input (x : Torus n) :
    StronglyMeasurable (maskedCarrierKernel d m x) :=
  h.stronglyMeasurable.comp_measurable (measurable_const.prodMk measurable_id)

/-- Measurability of an output column (`app:ch_background:eq:bg-T`). -/
theorem stronglyMeasurable_kernel_output (u : CarrierVariable n) :
    StronglyMeasurable (fun x ↦ maskedCarrierKernel d m x u) :=
  h.stronglyMeasurable.comp_measurable (measurable_id.prodMk measurable_const)

/-- Measurability of a transverse section (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem stronglyMeasurable_kernel_slice (x : Torus n) (z : CarrierParameter) :
    StronglyMeasurable (fun η ↦ maskedCarrierKernel d m x (z, η)) :=
  (h.stronglyMeasurable_kernel_input x).comp_measurable
    (measurable_const.prodMk measurable_id)

/-- Every bounded input kernel section is square integrable; this is a consequence,
not an extra hypothesis, of the finite-band cutoff (`app:ch_background:eq:bg-T`). -/
theorem memLp_kernel_input (x : Torus n) :
    MemLp (maskedCarrierKernel d m x) 2 (carrierMeasure n) := by
  have : IsFiniteMeasureOnCompacts (carrierMeasure n) := by
    unfold carrierMeasure
    infer_instance
  exact (h.hasCompactSupport_kernel_input x).memLp_of_bound
    (h.stronglyMeasurable_kernel_input x).aestronglyMeasurable h.bound
    (Filter.Eventually.of_forall (h.norm_le x))

/-- Square integrability of each torus column (`app:ch_background:eq:bg-T`). -/
theorem memLp_kernel_output (u : CarrierVariable n) :
    MemLp (fun x ↦ maskedCarrierKernel d m x u) 2 (volume : Measure (Torus n)) :=
  MemLp.of_bound (h.stronglyMeasurable_kernel_output u).aestronglyMeasurable h.bound
    (Filter.Eventually.of_forall (fun x ↦ h.norm_le x u))

/-- Square integrability of each transverse slice
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem memLp_kernel_slice (x : Torus n) (z : CarrierParameter) :
    MemLp (fun η ↦ maskedCarrierKernel d m x (z, η)) 2 volume :=
  (h.hasCompactSupport_kernel_slice x z).memLp_of_bound
    (h.stronglyMeasurable_kernel_slice x z).aestronglyMeasurable h.bound
    (Filter.Eventually.of_forall (fun η ↦ h.norm_le x (z, η)))

/-- The actual full-input integrand is integrable for every L² datum
(`app:ch_background:eq:bg-T`). -/
theorem integrable_smul_kernel_input (f : CarrierL2 n) (x : Torus n) :
    Integrable (fun u ↦ f u • maskedCarrierKernel d m x u) (carrierMeasure n) :=
  memLp_one_iff_integrable.mp ((Lp.memLp f).smul (h.memLp_kernel_input x))

/-- The actual slice integrand is integrable for every L² datum
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_smul_kernel_slice (f : CarrierSliceL2 n) (x : Torus n)
    (z : CarrierParameter) :
    Integrable (fun η ↦ f η • maskedCarrierKernel d m x (z, η)) volume :=
  memLp_one_iff_integrable.mp ((Lp.memLp f).smul (h.memLp_kernel_slice x z))

/-- Scalar compact majorant for the full initial kernel, used in the adjoint
pairing of `app:ch_background:eq:bg-T`. -/
def inputEnvelope : CarrierVariable n → ℝ :=
  h.initialSupport.indicator (fun _ ↦ h.bound)

/-- Scalar transverse majorant, uniform in the carrier parameter, used for
`app:ch_waves:eq:sampling-prefix-normal`. -/
def sliceEnvelope : Euclidean (n - 1) → ℝ :=
  (Metric.closedBall 0 h.frequencyRadius).indicator (fun _ ↦ h.bound)

/-- Square integrability of the full compact majorant (`app:ch_background:eq:bg-T`). -/
theorem memLp_inputEnvelope : MemLp h.inputEnvelope 2 (carrierMeasure n) := by
  have : IsFiniteMeasureOnCompacts (carrierMeasure n) := by
    unfold carrierMeasure
    infer_instance
  exact memLp_indicator_const 2 h.isCompact_initialSupport.measurableSet.nullMeasurableSet
    h.bound (Or.inr h.isCompact_initialSupport.measure_lt_top.ne)

/-- Square integrability of the uniform transverse majorant
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem memLp_sliceEnvelope : MemLp h.sliceEnvelope 2 volume :=
  memLp_indicator_const 2 measurableSet_closedBall.nullMeasurableSet h.bound
    (Or.inr (isCompact_closedBall (0 : Euclidean (n - 1)) h.frequencyRadius).measure_lt_top.ne)

/-- The full kernel is dominated by the same initial majorant at every output point
(`app:ch_background:eq:bg-T`). -/
theorem norm_kernel_le_inputEnvelope (x : Torus n) (u : CarrierVariable n) :
    ‖maskedCarrierKernel d m x u‖ ≤ h.inputEnvelope u := by
  classical
  by_cases hu : u ∈ h.initialSupport
  · simpa [inputEnvelope, hu] using h.norm_le x u
  · simp [inputEnvelope, hu, h.kernel_eq_zero_off_initialSupport x u hu]

/-- The slice kernel is dominated by the same transverse majorant at every output
point and carrier parameter (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_kernel_le_sliceEnvelope (x : Torus n) (z : CarrierParameter)
    (η : Euclidean (n - 1)) :
    ‖maskedCarrierKernel d m x (z, η)‖ ≤ h.sliceEnvelope η := by
  classical
  by_cases hη : η ∈ Metric.closedBall 0 h.frequencyRadius
  · simpa [sliceEnvelope, hη] using h.norm_le x (z, η)
  · have hzero := h.eq_zero x z η (Or.inr (by simpa using hη))
    simp [sliceEnvelope, hη, hzero]

end JanetCartan.ContinuumRow.FiniteCarrierKernelBounds
