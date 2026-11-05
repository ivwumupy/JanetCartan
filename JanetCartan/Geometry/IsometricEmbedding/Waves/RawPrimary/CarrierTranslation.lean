module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WkbGrades

/-!
# Exact carrier translation for uniform raw slice constants

Translate only the free covector of the original phase and amplitude. Applying
the slice estimate at covector zero then gives constants independent of the
carrier label. The Fourier datum, measure, physical cutoff and literal weak
jets are unchanged. The consumer is `UniformCanonicalSlice`, for
`app:ch_waves:eq:individual-raw-slice`.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary
open SliceBounds

variable {X P F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [MeasurableSpace P] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace P] in
/-- Carrier translation preserves the quotient including its smooth value at
epsilon zero (`app:ch_waves:eq:phase-quotient`). -/
theorem rawSlicePhaseExtension_translate (S : X → P → ℝ) (ζ : P) :
    rawSlicePhaseExtension (fun x η ↦ S x (ζ + η)) 0 = rawSlicePhaseExtension S ζ := by
  funext q
  simp only [rawSlicePhaseExtension, phaseShiftQuotient, inner_gradient_left,
    fderiv_comp_add_left, zero_add]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace P] in
/-- The original Lebesgue integral is unchanged by translating its phase and
amplitude together; no input translation or measure change occurs
(`app:ch_waves:eq:individual-representation`). -/
theorem rawPrimaryDemodulatedIntegral_translate (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (μ : Measure P) (f : P → ℂ) :
    rawPrimaryDemodulatedIntegral (fun x η ↦ S x (ζ + η))
      (fun x η ↦ A x (ζ + η)) 0 τ μ f = rawPrimaryDemodulatedIntegral S A ζ τ μ f := by
  funext x
  simp only [rawPrimaryDemodulatedIntegral, rawPrimaryPhaseDifference, zero_add, add_zero]

omit [CompleteSpace P] [NormedSpace ℝ F] in
/-- All literal integral jets agree after carrier translation, with the SAME
physical cutoff and datum (`app:ch_waves:eq:individual-raw-slice`). -/
theorem rawSliceIntegralJet_translate (χ : X → ℝ) (S : X → P → ℝ) (A : X → P → F)
    (ζ : P) (τ : ℝ) (μ : Measure P) (f : P → ℂ) :
    rawSliceIntegralJet χ (fun x η ↦ S x (ζ + η)) (fun x η ↦ A x (ζ + η))
      0 τ μ f = rawSliceIntegralJet χ S A ζ τ μ f := by
  funext j x
  simp only [rawSliceIntegralJet, rawPrimaryDemodulatedAtom,
    rawPrimaryPhaseDifference, zero_add, add_zero]

omit [CompleteSpace P] [MeasurableSpace P] in
/-- Free-covector translation preserves every original joint derivative,
without spending reserve (`app:ch_waves:eq:individual-grading`). -/
theorem iteratedFDeriv_covector_translate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : X × P → E)
    (ζ : P) (k : ℕ) (q : X × P) :
    iteratedFDeriv ℝ k (fun w : X × P ↦ f (w.1, ζ + w.2)) q =
      iteratedFDeriv ℝ k f (q.1, ζ + q.2) := by
  have he (w : X × P) : (0, ζ) + w = (w.1, ζ + w.2) := by
    ext <;> simp
  simpa only [he] using
    iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) k (0, ζ) q

end JanetCartan.RawPrimary
