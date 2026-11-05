module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.ElapsedKernels
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Time/space splitting with the original Lebesgue normalization

The time-first Euclidean coordinates in
`app:ch_regular_base:eq:fixed-time-representation` preserve Lebesgue measure.
This supplies the actual Fubini change of variables for compact frequency
regularizations; no Jacobian or Fourier normalization is suppressed.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- The literal first-coordinate/time and remaining-coordinate/space
identification in `app:ch_regular_base:eq:fixed-time-representation`. -/
def timeSpaceMeasurableEquiv : Euclidean (d + 1) ≃ᵐ ℝ × Euclidean d :=
  (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin d → ℝ))))

/-- The preceding equivalence uses exactly `Basic.spatialPart`.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem timeSpaceMeasurableEquiv_apply (x : Euclidean (d + 1)) :
    timeSpaceMeasurableEquiv x = (x 0, spatialPart x) := by
  rfl

/-- Rejoining a time and a spatial vector in the original time-first
coordinates of `app:ch_regular_base:eq:fixed-time-representation`. -/
def timeSpacePoint (t : ℝ) (y : Euclidean d) : Euclidean (d + 1) :=
  timeSpaceMeasurableEquiv.symm (t, y)

/-- Recovering time after rejoining coordinates (fixed-time representation). -/
@[simp] theorem timeSpacePoint_time (t : ℝ) (y : Euclidean d) :
    timeSpacePoint t y 0 = t :=
  congrArg Prod.fst (timeSpaceMeasurableEquiv.apply_symm_apply (t, y))

/-- Recovering space after rejoining coordinates (fixed-time representation). -/
@[simp] theorem spatialPart_timeSpacePoint (t : ℝ) (y : Euclidean d) :
    spatialPart (timeSpacePoint t y) = y :=
  congrArg Prod.snd (timeSpaceMeasurableEquiv.apply_symm_apply (t, y))

/-- Rejoining the physical coordinates is continuous. Consumer: integrability
of the temporal Fourier slices in the fixed-time representation. -/
theorem continuous_timeSpacePoint :
    Continuous (fun p : ℝ × Euclidean d ↦ timeSpacePoint p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact continuous_fst
  · exact (PiLp.continuous_apply 2 _ j).comp continuous_snd

/-- The coordinate split has unit Jacobian for the existing Euclidean volume.
Consumer: compact frequency Fubini in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem measurePreserving_timeSpaceMeasurableEquiv :
    MeasurePreserving (timeSpaceMeasurableEquiv (d := d)) volume (volume.prod volume) := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin d))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin (d + 1))))

/-- Splitting a genuinely integrable spacetime-frequency integral into spatial
frequency followed by temporal frequency, without changing the measure.
Consumer: the compact-cutoff fixed-time identity in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_eq_space_time {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Euclidean (d + 1) → F) (hf : Integrable f) :
    (∫ ξ, f ξ) = ∫ η : Euclidean d, ∫ τ : ℝ, f (timeSpacePoint τ η) := by
  have hp := measurePreserving_timeSpaceMeasurableEquiv (d := d)
  have hi := hp.symm.integrable_comp_of_integrable hf
  rw [← hp.symm.integral_comp' f]
  exact integral_prod_symm _ hi

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
