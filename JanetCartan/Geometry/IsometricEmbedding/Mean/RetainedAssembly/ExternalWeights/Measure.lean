module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.ExternalWeights.Cutoffs

/-!
# The literal squared external measure

The measure in `app:ch_background:eq:bg-affine-mean` is exactly `χ² dz`.
Here `dz = ds dv`; the existing measure-preserving `parameter` identifies
this with the original three-dimensional Euclidean Lebesgue measure.
The consumer is the supplied-weight mean/source construction, followed by
`PositiveBackground.uncorrectedDensity_core_cancellation`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RetainedAssembly.ExternalWeights
open ContinuumRow CanonicalCarrier

/-- The fixed external weight, literally the cutoff square
(`app:ch_background:eq:bg-affine-mean`). -/
def squaredCarrierWeight (χ : CarrierParameter → ℝ) (z : CarrierParameter) : ℝ := χ z ^ 2

/-- The original Lebesgue carrier measure with density `χ²`
(`app:ch_background:eq:bg-affine-mean`). -/
def squaredCarrierMeasure (χ : CarrierParameter → ℝ) : Measure CarrierParameter :=
  (volume.prod volume).withDensity (fun z ↦ ENNReal.ofReal (squaredCarrierWeight χ z))

/-- Nonnegativity is a consequence of the literal square
(`app:ch_background:prop:bg-positive`). -/
theorem squaredCarrierWeight_nonneg (χ : CarrierParameter → ℝ) (z : CarrierParameter) :
    0 ≤ squaredCarrierWeight χ z := sq_nonneg _

/-- Smoothness of the same fixed external weight
(`app:ch_background:prop:bg-positive`). -/
theorem squaredCarrierWeight_contDiff {χ : CarrierParameter → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (squaredCarrierWeight χ) := hχ.pow 2

/-- Squaring changes neither the closed support nor its fixed domain
(`app:ch_background:prop:bg-positive`). -/
theorem squaredCarrierWeight_tsupport (χ : CarrierParameter → ℝ) :
    tsupport (squaredCarrierWeight χ) = tsupport χ := by
  unfold squaredCarrierWeight tsupport
  rw [Function.support_pow _ (by norm_num : 2 ≠ 0)]

/-- The literal external measure is finite for a smooth compactly supported
cutoff (`app:ch_background:eq:bg-affine-mean`). -/
theorem squaredCarrierMeasure_finite {χ : CarrierParameter → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport χ) :
    IsFiniteMeasure (squaredCarrierMeasure χ) := by
  have hw := (squaredCarrierWeight_contDiff hχ).continuous
  have hs : HasCompactSupport (squaredCarrierWeight χ) := by
    change IsCompact (tsupport (squaredCarrierWeight χ))
    rw [squaredCarrierWeight_tsupport]
    exact hcompact
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hw.aestronglyMeasurable
    (Filter.Eventually.of_forall (squaredCarrierWeight_nonneg χ))).mpr
      (hw.integrable_of_hasCompactSupport hs)

/-- Integrating with the external measure is exactly the supplied squared
weight convention used by the mean, for arbitrary real vector-valued
integrands (`app:ch_background:eq:bg-affine-mean`). -/
theorem integral_squaredCarrierMeasure {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : CarrierParameter → ℝ} (hχ : ContDiff ℝ ∞ χ) (g : CarrierParameter → F) :
    ∫ z, g z ∂squaredCarrierMeasure χ =
      ∫ z, squaredCarrierWeight χ z • g z ∂(volume.prod volume) := by
  rw [squaredCarrierMeasure, integral_withDensity_eq_integral_toReal_smul
    (squaredCarrierWeight_contDiff hχ).continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (squaredCarrierWeight_nonneg χ _)]

/-- Reassembling `(s,v)` gives precisely Euclidean Lebesgue integration of
the SAME weight; no transport Jacobian or normalization factor is introduced
(`app:ch_background:eq:bg-affine-mean`). -/
theorem integral_squaredCarrierMeasure_parameter
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : CarrierParameter → ℝ} (hχ : ContDiff ℝ ∞ χ) (g : Euclidean 3 → F) :
    ∫ z, g (parameter z) ∂squaredCarrierMeasure χ =
      ∫ z, χ (TransportKernel.sliceCoordinates 2 z) ^ 2 • g z ∂volume := by
  rw [integral_squaredCarrierMeasure hχ]
  have hm : MeasurableEmbedding (parameter : CarrierParameter → Euclidean 3) := by
    rw [parameter_eq_sliceCoordinates_symm]
    exact (TransportKernel.sliceCoordinates 2).symm.measurableEmbedding
  simpa only [squaredCarrierWeight, parameter_eq_sliceCoordinates_symm,
    MeasurableEquiv.apply_symm_apply] using parameter_measurePreserving.integral_comp hm
      (fun z ↦ χ (TransportKernel.sliceCoordinates 2 z) ^ 2 • g z)

end JanetCartan.RetainedAssembly.ExternalWeights
