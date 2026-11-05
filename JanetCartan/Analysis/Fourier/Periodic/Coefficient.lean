module

public import JanetCartan.Analysis.Fourier.Periodic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Linear maps and periodic Fourier coefficients

The common coefficient identity used by differentiation and smoothing in the
Fourier conventions of Appendix A of `paper.tex`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {n : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Real continuous linear maps commute with the shared Fourier coefficients
(Appendix B). -/
theorem periodicFourierCoeff_comp_clm (A : F →L[ℝ] G) {f : Torus n → F}
    (hf : Continuous f) (k : Fin n → ℤ) :
    periodicFourierCoeff (A ∘ f) k =
      (A (periodicFourierCoeff f k).1, A (periodicFourierCoeff f k).2) := by
  apply Prod.ext
  · change (∫ x : Torus n, _ • A (f x)) = A (∫ x : Torus n, _ • f x)
    simp_rw [← A.map_smul]
    exact A.integral_comp_comm <| Continuous.integrable_of_hasCompactSupport
      ((Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous).smul hf)
      (HasCompactSupport.of_compactSpace _)
  · change (∫ x : Torus n, _ • A (f x)) = A (∫ x : Torus n, _ • f x)
    simp_rw [← A.map_smul]
    exact A.integral_comp_comm <| Continuous.integrable_of_hasCompactSupport
      ((Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous).smul hf)
      (HasCompactSupport.of_compactSpace _)

/-- The pointwise form of the coefficient identity for a real continuous linear map. -/
theorem periodicFourierCoeff_map (A : F →L[ℝ] G) {f : Torus n → F}
    (hf : Continuous f) (k : Fin n → ℤ) :
    periodicFourierCoeff (fun x ↦ A (f x)) k =
      (A (periodicFourierCoeff f k).1, A (periodicFourierCoeff f k).2) :=
  periodicFourierCoeff_comp_clm A hf k

end JanetCartan
