module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LebesgueData
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# The finite Fourier measure of the actual raw datum

The measure is formed before spatial initial multiplication. Its variation is
exactly the absolute value of the original smooth-band density, so the original
Lebesgue Fourier estimate controls its total mass with no band-count loss.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
namespace JanetCartan.RawPrimary
open RawInputPartition

variable {n J : ℕ} {d : Euclidean (n - 1) → ℂ} {M : ℝ}

/-- The literal complex Fourier measure of the raw initial input, before the
physical cutoff (`app:ch_waves:thm:individual`, `app:ch_waves:eq:B-bounds`). -/
def wideFourierMeasure (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) :
    VectorMeasure (Euclidean (n - 1)) ℂ :=
  volume.withDensityᵥ (weightedWideDensity d v)

/-- Exact variation of the original Fourier measure
(`app:ch_waves:eq:B-bounds`). -/
theorem variation_wideFourierMeasure (hd : Measurable d) (hM : 0 ≤ M)
    (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    (wideFourierMeasure d v).variation =
      volume.withDensity (fun η ↦ ‖weightedWideDensity d v η‖ₑ) :=
  Measure.variation_withDensityᵥ (integrable_wideDensity hd hM hb v)

/-- The raw Fourier measure has finite total variation for every original
Hilbert datum (`app:ch_waves:thm:individual`). -/
theorem isFiniteMeasure_variation_wideFourierMeasure (hd : Measurable d) (hM : 0 ≤ M)
    (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    IsFiniteMeasure (wideFourierMeasure d v).variation := by
  rw [variation_wideFourierMeasure hd hM hb v]
  exact ⟨by simpa [HasFiniteIntegral] using (integrable_wideDensity hd hM hb v).2⟩

/-- The real total-variation mass is precisely the original Fourier `L¹`
norm (`app:ch_waves:eq:B-bounds`). -/
theorem variation_wideFourierMeasure_real_univ (hd : Measurable d) (hM : 0 ≤ M)
    (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    (wideFourierMeasure d v).variation.real univ = ∫ η, ‖weightedWideDensity d v η‖ := by
  rw [measureReal_def, variation_wideFourierMeasure hd hM hb v,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    integral_norm_eq_lintegral_enorm (integrable_wideDensity hd hM hb v).aestronglyMeasurable]

/-- The exact `K^(n/2)` bound for the same finite Fourier measure, with the
original wide-input norm (`app:ch_waves:eq:B-bounds`). -/
theorem variation_wideFourierMeasure_rounded_le (hn : 1 ≤ n) {K : ℝ} (hK : 1 ≤ K)
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n (cutoffCount K)) :
    (wideFourierMeasure d v).variation.real univ ≤
      (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2)) * K ^ ((n : ℝ) / 2) * ‖v‖ := by
  rw [variation_wideFourierMeasure_real_univ hd hM hb v]
  exact integral_norm_weightedWideDensity_rounded_le hn hK hd hM hb v

end JanetCartan.RawPrimary
