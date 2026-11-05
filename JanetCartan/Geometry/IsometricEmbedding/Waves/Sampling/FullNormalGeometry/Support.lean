module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalInputGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.CanonicalGap.RadialSupport

/-!
# The entire supported input for the full sampling normal

The compact input below is the literal coordinate pullback of the prescribed
positive radial interval times the retained normalized core. It covers every
direction in the original compact angular support and every radius in the
original normalized wide band. It is not a smaller local inverse box.

The consumer is `LiteralMeanBound.exists_source_mean_bound`, specifically its
`canonicalInputCoordinates '' G.D₀` containment. Constructing a buffered inverse
on a neighborhood of this entire set remains a separate geometric obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff

namespace JanetCartan.Sampling.FullNormalGeometry
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ContinuumRow.CanonicalConic
open MeanNormalBound.CanonicalGap MeanNormalBound.NormalizedFullPhase RawKernel
open ContinuumNormalReduction.ConicChart

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Full compact radial/input support in the original sampling coordinates.
The radial interval is prescribed before the current immersion and all labels
(`app:ch_waves:setup:oscillatory`, `app:ch_waves:eq:sampling-operator-bounds`). -/
def radialSamplingSupport (z₀ : Euclidean 3) (ηb : Euclidean m)
    (r amin amax : ℝ) : Set (Euclidean (m + 1)) :=
  canonicalInputCoordinates T ⁻¹'
    ((fun q : ℝ × Euclidean (m + 1) ↦ radialInput T q.1 q.2) ''
      (Icc amin amax ×ˢ normalizedInputCore T z₀ ηb r))

/-- The compact support is chosen using only the retained reference charts.
Consumer: `UniformNormalGeometry.compact_D₀`
(`app:ch_osc:setup:osc-normal`). -/
theorem radialSamplingSupport_compact (z₀ : Euclidean 3) (ηb : Euclidean m)
    (r amin amax : ℝ) : IsCompact (radialSamplingSupport T z₀ ηb r amin amax) :=
  (canonicalInputIsometry T).toHomeomorph.isCompact_preimage.mpr
    (radialInput_image_compact T z₀ ηb r amin amax)

/-- The exact support containment required by the literal mean bound is an
equality for this input core. No angular or radial support is discarded
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem canonicalInputCoordinates_image_radialSamplingSupport
    (z₀ : Euclidean 3) (ηb : Euclidean m) (r amin amax : ℝ) :
    canonicalInputCoordinates T '' radialSamplingSupport T z₀ ηb r amin amax =
      (fun q : ℝ × Euclidean (m + 1) ↦ radialInput T q.1 q.2) ''
        (Icc amin amax ×ˢ normalizedInputCore T z₀ ηb r) :=
  (canonicalInputCoordinates T).surjective.image_preimage _

/-- Literal incidence and covector coordinates of a radially dilated core
point (`app:ch_seed:eq:seed-exact-phase-quotient`). -/
theorem canonicalInputCoordinates_fullInputCoordinates_radial
    (a t : ℝ) (η : Euclidean m) :
    canonicalInputCoordinates T (fullInputCoordinates m (t, a • η)) =
      radialInput T a ((adaptedSliceCoordinates T).equiv.symm (t, η)) := by
  apply (adaptedSliceCoordinates T).equiv.injective
  simp only [adapted_canonicalInputCoordinates, radialInput,
    ContinuousLinearEquiv.apply_symm_apply, radialScale]

/-- Every original compact angular direction and every prescribed radial
label is retained, with the incidence coordinate unchanged. Consumer: support
of the subsequent measured amplitude (`app:ch_waves:setup:oscillatory`). -/
theorem fullInputCoordinates_mem_radialSamplingSupport
    {z₀ : Euclidean 3} {ηb θ : Euclidean m} (hηb : ηb ≠ 0)
    {r amin amax a t : ℝ} (hr : 0 < r)
    (ht : t ∈ closedBall (z₀ 0) r) (ha : a ∈ Icc amin amax)
    (hθ : θ ∈ closedDirections (n := m + 1) ηb r) :
    fullInputCoordinates m (t, a • (‖ηb‖ • θ)) ∈
      radialSamplingSupport T z₀ ηb r amin amax := by
  unfold radialSamplingSupport
  rw [mem_preimage]
  rw [canonicalInputCoordinates_fullInputCoordinates_radial]
  exact ⟨(a, (adaptedSliceCoordinates T).equiv.symm (t, ‖ηb‖ • θ)),
    ⟨ha, closedDirections_mem_normalizedInputCore T hηb hr ht hθ⟩, rfl⟩

/-- The entire original normalized wide band has radii between `1/2` and
`2`. This theorem retains those endpoints; no sharp refinement mask is added
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideBand_mem_radialSamplingSupport
    {z₀ : Euclidean 3} {ηb η : Euclidean m} (hηb : ηb ≠ 0)
    {r amin amax t : ℝ} (hr : 0 < r)
    (ht : t ∈ closedBall (z₀ 0) r)
    (hlo : amin ≤ (1 / 2) / ‖ηb‖) (hhi : 2 / ‖ηb‖ ≤ amax)
    (hη : η ∈ RawInputPartition.wideBand (m + 1) 0)
    (hθ : NormedSpace.normalize η ∈ closedDirections (n := m + 1) ηb r) :
    fullInputCoordinates m (t, η) ∈ radialSamplingSupport T z₀ ηb r amin amax := by
  have hn : 0 < ‖ηb‖ := norm_pos_iff.mpr hηb
  have hloη : (1 / 2 : ℝ) ≤ ‖η‖ := by
    have hh := hη.2
    simpa only [RawInputPartition.dyadicScale, pow_zero, one_div,
      mem_ball, dist_zero_right, not_lt] using hh
  have hhiη : ‖η‖ ≤ 2 := by
    have hh := hη.1
    norm_num [RawInputPartition.dyadicScale, mem_closedBall, dist_zero_right] at hh
    exact hh
  have ha : ‖η‖ / ‖ηb‖ ∈ Icc amin amax :=
    ⟨hlo.trans (div_le_div_of_nonneg_right hloη hn.le),
      (div_le_div_of_nonneg_right hhiη hn.le).trans hhi⟩
  have he : (‖η‖ / ‖ηb‖) • (‖ηb‖ • NormedSpace.normalize η) = η := by
    rw [smul_smul, div_mul_cancel₀ _ (ne_of_gt hn), NormedSpace.norm_smul_normalize]
  simpa only [he] using
    fullInputCoordinates_mem_radialSamplingSupport T hηb hr ht ha hθ

end JanetCartan.Sampling.FullNormalGeometry
