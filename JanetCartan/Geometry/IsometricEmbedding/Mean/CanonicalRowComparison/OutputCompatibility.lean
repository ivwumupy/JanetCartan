module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.OutputTransfer
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Prefixes.RealCompression
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Synthesis

/-!
# Output transfer preserves the real canonical normal

Only the output passes from physical Lebesgue measure to the auxiliary torus.
The raw input and both complex quadratures are unchanged. These identities
connect the constructed transport continuum normal to the exact endpoint of
`refined_complete_normal_sub_transport_le`; source:
`app:ch_waves:eq:real-normal`, `app:ch_mean_pairs:defn:mean-canonical`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory

namespace JanetCartan.CanonicalRowComparison
open PeriodicLocalL2 ContinuumRow SamplingKernelBounds

variable {n : ℕ}

/-- Real part commutes with the original output transfer; no input-space
identification is involved (`app:ch_waves:eq:real-normal`). -/
theorem l2RealPart_toTorus (f : Output n) :
    l2RealPart volume (toTorus (𝕜 := ℂ) f) = toTorus (𝕜 := ℝ) (l2RealPart volume f) := by
  apply Lp.ext
  filter_upwards [(euclideanRealPart (ι := Fin n)).coeFn_compLpL (toTorus (𝕜 := ℂ) f),
    toTorus_coe (𝕜 := ℂ) f, toTorus_coe (𝕜 := ℝ) (l2RealPart volume f),
    measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
      ((euclideanRealPart (ι := Fin n)).coeFn_compLpL f).restrict] with x hl hf hr he
  change l2RealPart volume (toTorus (𝕜 := ℂ) f) x = _ at hl ⊢
  change (l2RealPart volume f ∘ AmplitudeBound.centeredTorusRepresentative) x = _ at he
  rw [hl, hf, hr, he]
  rfl

/-- Real inclusion commutes with the original zero extension of the output
chart. The chart indicator is retained on both sides
(`app:ch_background:eq:bg-realification`). -/
theorem l2ComplexInclusion_toEuclidean (f : OutputL2 n) :
    toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume f) =
      l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) f) := by
  apply Lp.ext
  have hf := measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp
    ((euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL f)
  have hfi := (ae_restrict_iff' measurableSet_halfOpenCell).mp hf
  filter_upwards [toEuclidean_coe (𝕜 := ℂ) (l2ComplexInclusion volume f),
    toEuclidean_coe (𝕜 := ℝ) f,
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL (toEuclidean (𝕜 := ℝ) f), hfi]
    with x hc hr hi hx
  change toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume f) x =
    l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) f) x
  change l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) f) x = _ at hi
  rw [hc, hi, hr]
  by_cases h : x ∈ halfOpenCell n
  · simp only [Set.indicator_of_mem h]
    exact hx h
  · simp only [Set.indicator_of_notMem h, map_zero]

/-- Compression and output transfer commute exactly. Thus the factor four
of the sampled cross normal is the SAME factor four on the continuum output
(`app:ch_waves:eq:real-normal`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem realOutputCompression_transferOperator (A : Output n →L[ℂ] Output n) :
    realOutputCompression (transferOperator A) = transferOperator (realOutputCompression A) := by
  ext1 f
  change l2RealPart volume (toTorus (𝕜 := ℂ)
    (A (toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume f)))) =
      toTorus (𝕜 := ℝ) (l2RealPart volume (A (l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) f))))
  rw [l2ComplexInclusion_toEuclidean, l2RealPart_toTorus]

private def complexNormalOutputTransfer (n : ℕ) :
    (Output n →L[ℂ] Output n) →L[ℂ] (ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n) :=
  ((ContinuousLinearMap.compL ℂ (ComplexOutputL2 n) (Output n) (ComplexOutputL2 n)).flip
    (toEuclidean (𝕜 := ℂ)).toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℂ (Output n) (Output n) (ComplexOutputL2 n)) (toTorus (𝕜 := ℂ)))

/-- Bochner integration of the original sampling-coordinate normal commutes
with output transfer (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem transferOperator_sampling_integral
    (F : SeparatedSampling.Point → Output n →L[ℂ] Output n) (hF : Integrable F) :
    transferOperator (∫ z, F z) = ∫ z, transferOperator (F z) :=
  ((complexNormalOutputTransfer n).integral_comp_comm hF).symm

end JanetCartan.CanonicalRowComparison
