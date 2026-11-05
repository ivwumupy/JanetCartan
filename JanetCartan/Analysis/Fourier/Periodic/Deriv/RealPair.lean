module
public import JanetCartan.Analysis.Fourier.Periodic.Coefficient
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
/-!
# Complex and real-pair Fourier coefficients

Compatibility and coefficient bounds for paper.tex, `app:not:fourier`.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan
variable {n : ℕ}
/-- At unit period, the shared volume equals normalized product Haar measure. -/
lemma torus_volume_eq_pi_haar : (volume : Measure (Torus n)) =
    Measure.pi (fun _ : Fin n ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  rw [volume_pi]
  congr 1
  funext i
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1))

/-- The shared real pair consists of the parts of the complex coefficient (`app:not:fourier`). -/
theorem periodicFourierCoeff_eq_complex_parts {f : Torus n → ℝ} (hf : Continuous f) (k : Fin n → ℤ) :
    periodicFourierCoeff f k =
      ((UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k).re,
       (UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k).im) := by
  have hi : Integrable (fun x : Torus n ↦ UnitAddTorus.mFourier (-k) x * (f x : ℂ)) :=
    ((UnitAddTorus.mFourier (-k)).continuous.mul (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k =
      ∫ x : Torus n, UnitAddTorus.mFourier (-k) x * (f x : ℂ) := by
    rw [torus_volume_eq_pi_haar]
    rfl
  rw [hc]
  ext
  · simpa [periodicFourierCoeff] using integral_re hi
  · simpa [periodicFourierCoeff] using integral_im hi

local instance realPairCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance realPairCircleProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
/-- A uniform field bound bounds every normalized coefficient (`app:not:fourier`). -/
theorem norm_mFourierCoeff_le (f : Torus n → ℂ) (k : Fin n → ℤ) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : ‖UnitAddTorus.mFourierCoeff f k‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus n)))
    (f := fun x ↦ UnitAddTorus.mFourier (-k) x * f x)
    (Filter.Eventually.of_forall fun x ↦ by
      simpa [norm_mul, UnitAddTorus.mFourier, fourier_apply, norm_prod] using hC x)
  simpa [UnitAddTorus.mFourierCoeff, smul_eq_mul] using h
end JanetCartan
