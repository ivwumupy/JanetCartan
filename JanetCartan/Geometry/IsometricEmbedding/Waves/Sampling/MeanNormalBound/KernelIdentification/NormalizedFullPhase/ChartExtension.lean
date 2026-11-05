module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.Dilation

/-!
# Zero extension of normalized full inputs

For `app:ch_osc:eq:osc-exact-normal-kernel`, the open phase chart need not
contain the whole closed wide annulus. Both inputs are therefore extended
isometrically to the same full Euclidean L² space. Only the actual amplitudes
must have matching support; no whole-domain containment is required.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
open RawInputHilbert

/-- The complete normalized input embedding: dilate `η = 2^j θ`, insert `s`
into Euclidean coordinates, then extend by zero to full Euclidean space
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def normalizedFullInputEmbedding (m j : ℕ) (B : ℝ) :
    FullBandInput (m + 1) j B →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Euclidean (m + 1))) :=
  (zeroExtension (measurableSet_fullInputDomain m 0 B)).comp
    (((fullBandDilation (m + 1) j B).trans
      (fullInputL2Coordinates m 0 B)).toLinearIsometry)

/-- Literal zero extension of the normalized input representative
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem normalizedFullInputEmbedding_apply_ae (m j : ℕ) (B : ℝ)
    (f : FullBandInput (m + 1) j B) :
    normalizedFullInputEmbedding m j B f =ᵐ[volume]
      (fullInputDomain m 0 B).indicator
        (fullInputL2Coordinates m 0 B (fullBandDilation (m + 1) j B f)) :=
  zeroExtension_coeFn (measurableSet_fullInputDomain m 0 B) _

/-- The complete input normalization is isometric, including zero extension
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_normalizedFullInputEmbedding (m j : ℕ) (B : ℝ)
    (f : FullBandInput (m + 1) j B) :
    ‖normalizedFullInputEmbedding m j B f‖ = ‖f‖ :=
  (normalizedFullInputEmbedding m j B).norm_map f

/-- The actual adjoint is a left inverse of the normalized input embedding,
which is the cancellation used in the forward identity
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem normalizedFullInputEmbedding_adjoint_comp (m j : ℕ) (B : ℝ) :
    (normalizedFullInputEmbedding m j B).toContinuousLinearMap.adjoint.comp
      (normalizedFullInputEmbedding m j B).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ _ := by
  ext1 f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  exact (normalizedFullInputEmbedding m j B).inner_map_map g f

end JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
