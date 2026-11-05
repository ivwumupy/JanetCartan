module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.ChartMeasure
public import JanetCartan.Analysis.Fourier.Periodic.Sobolev

/-!
# Physical chart integrals of periodic lifts

The local field and full-strain estimates in `app:ch_background:prop:bg-mixed-physical`
use Euclidean Lebesgue measure on the chart. The raw inputs retain their auxiliary
Haar measure. The unit-cell transfer below relates only the output functions.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace JanetCartan.AuxiliaryRawBand

open PeriodicLocalL2

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

/-- A continuous periodic lift is square integrable on every measurable or
nonmeasurable subset of the unit cell (`app:ch_background:prop:bg-mixed-physical`). -/
theorem memLp_periodicLift_on_subset_cell {f : Torus n → F} (hf : Continuous f)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hcell : W ⊆ halfOpenCell n) :
    MemLp (periodicLift f) 2 (volume.restrict W) := by
  exact ((hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f) (p := 2)).comp_measurePreserving
    measurePreserving_quotient).mono_measure (Measure.restrict_mono_set _ hcell)

/-- Exact transfer of squared output norms on a measurable physical chart
(`app:ch_background:prop:bg-mixed-physical`, `app:not:fourier`). -/
theorem integral_norm_sq_periodicLift_chart
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : MeasurableSet W)
    (hcell : W ⊆ halfOpenCell n) (f : Torus n → F) :
    (∫ x in W, ‖periodicLift f x‖ ^ 2) =
      ∫ z in torusChart W, ‖f z‖ ^ 2 := by
  rw [← integral_chart_representative hW hcell (fun x ↦ ‖periodicLift f x‖ ^ 2)]
  simp only [periodicLift, Function.comp_apply,
    AmplitudeBound.torusQuotient_centeredTorusRepresentative]

/-- Restriction of a smooth auxiliary output to the physical cell decreases
its squared L² norm, with constant one (`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem integral_norm_sq_periodicLift_le {f : Torus n → F} (hf : Continuous f)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hcell : W ⊆ halfOpenCell n) :
    (∫ x in W, ‖periodicLift f x‖ ^ 2) ≤ periodicL2Norm f ^ 2 := by
  have hi : IntegrableOn (fun x ↦ ‖periodicLift f x‖ ^ (2 : ℕ)) (halfOpenCell n) :=
    (memLp_periodicLift_on_subset_cell hf (Subset.refl (halfOpenCell n))).integrable_norm_pow
      (by decide)
  calc
    _ ≤ ∫ x in halfOpenCell n, ‖periodicLift f x‖ ^ 2 :=
      setIntegral_mono_set hi (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
        (Filter.Eventually.of_forall hcell)
    _ = ∫ z, ‖f z‖ ^ 2 := integral_periodicLift (fun z ↦ ‖f z‖ ^ 2)
    _ = periodicL2Norm f ^ 2 := (Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)).symm

end JanetCartan.AuxiliaryRawBand
