module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.FullBand
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WideDilation

/-!
# Literal full input coordinates

The full input in `app:ch_waves:eq:sampling-prefix-normal` is `(s, θ)` with
Lebesgue measure in all coordinates. These changes of variables are consumed
by the normalized full-phase kernel identification. The transverse dimension
is written `m`, so the physical and full input dimensions are `m + 1`.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
open RawInputPartition RawPrimary.SliceBounds

/-- Insert the slice coordinate before the transverse coordinates, as required
by `app:ch_waves:eq:sampling-prefix-normal`. -/
def fullInputCoordinates (m : ℕ) : ℝ × Euclidean m ≃ᵐ Euclidean (m + 1) :=
  (((MeasurableEquiv.refl ℝ).prodCongr
    (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm).trans
        (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ))

/-- The coordinate formula keeps the original slice and transverse variables
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullInputCoordinates_apply (m : ℕ) (u : ℝ × Euclidean m) :
    fullInputCoordinates m u = WithLp.toLp 2 (Fin.cons u.1 (fun i ↦ u.2 i)) := by
  simp only [fullInputCoordinates, MeasurableEquiv.trans_apply,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  change WithLp.toLp 2 (Fin.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) 0 u.1 (fun i ↦ u.2 i)) = _
  simp only [Fin.insertNth_zero]
  rfl

/-- The literal coordinate insertion preserves Lebesgue measure; no input
density is hidden in the coordinates (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullInputCoordinates_measurePreserving (m : ℕ) :
    MeasurePreserving (fullInputCoordinates m) (volume.prod volume) volume :=
  (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
    (((volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm).comp
      ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin m))))

/-- The precise restricted full input domain in Euclidean coordinates, before
zero extension into the open phase chart (`app:ch_waves:eq:sampling-prefix-normal`). -/
def fullInputDomain (m j : ℕ) (B : ℝ) : Set (Euclidean (m + 1)) :=
  fullInputCoordinates m '' (Set.Icc (-B) B ×ˢ wideBand (m + 1) j)

/-- Measurability of the actual full input restriction
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem measurableSet_fullInputDomain (m j : ℕ) (B : ℝ) :
    MeasurableSet (fullInputDomain m j B) :=
  (fullInputCoordinates m).measurableSet_image.mpr
    (measurableSet_Icc.prod (measurableSet_wideBand (m + 1) j))

/-- Exact domain membership in literal coordinates
(`app:ch_waves:eq:sampling-prefix-normal`). -/
@[simp] theorem fullInputCoordinates_mem_domain (m j : ℕ) (B : ℝ)
    (u : ℝ × Euclidean m) :
    fullInputCoordinates m u ∈ fullInputDomain m j B ↔
      u ∈ Set.Icc (-B) B ×ˢ wideBand (m + 1) j :=
  (fullInputCoordinates m).injective.mem_set_image

/-- Restricted product Lebesgue measure becomes restricted Euclidean Lebesgue
measure, including the boundary (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullInputCoordinates_restrict_measurePreserving (m j : ℕ) (B : ℝ) :
    MeasurePreserving (fullInputCoordinates m) (fullBandMeasure (m + 1) j B)
      (volume.restrict (fullInputDomain m j B)) := by
  have h := (fullInputCoordinates_measurePreserving m).restrict_preimage
    (measurableSet_fullInputDomain m j B)
  simpa only [fullInputDomain, Set.preimage_image_eq _ (fullInputCoordinates m).injective,
    fullBandMeasure, Measure.prod_restrict] using h

/-- Full-input Bochner substitution, used by the forward and normal identities
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_fullInputCoordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (m j : ℕ) (B : ℝ) (f : Euclidean (m + 1) → E) :
    (∫ u, f (fullInputCoordinates m u) ∂fullBandMeasure (m + 1) j B) =
      ∫ w in fullInputDomain m j B, f w :=
  (fullInputCoordinates_restrict_measurePreserving m j B).integral_comp' f

/-- The complete input dilation fixes `s` and sends `θ` to `2^j θ`.
The scale is `2^j`, not `dyadicScale j = 2^j/2`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def fullInputDilation (n j : ℕ) :
    (ℝ × Euclidean (n - 1)) ≃ᵐ (ℝ × Euclidean (n - 1)) :=
  (MeasurableEquiv.refl ℝ).prodCongr
    (Homeomorph.smul (Units.mk0 ((2 : ℝ) ^ j) (by positivity))).toMeasurableEquiv

/-- The product measure has exactly the transverse Jacobian. This reuses the
wide-band change of variables built from `RawInputDilation`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem map_fullBandMeasure_dilation (n j : ℕ) (B : ℝ) :
    (fullBandMeasure n 0 B).map (fullInputDilation n j) =
      ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (n - 1))⁻¹) • fullBandMeasure n j B := by
  change Measure.map (Prod.map id (fun θ ↦ (2 : ℝ) ^ j • θ))
    ((volume.restrict (Set.Icc (-B) B)).prod (volume.restrict (wideBand n 0))) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
    map_wideBandMeasure_smul, Measure.prod_smul_right]
  rfl

/-- The exact full-input substitution, with its transverse Jacobian, used to
normalize the full forward kernel (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem integral_fullBand_dilation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n j : ℕ) (B : ℝ) (f : ℝ × Euclidean (n - 1) → E) :
    (∫ u, f (fullInputDilation n j u) ∂fullBandMeasure n 0 B) =
      (((2 : ℝ) ^ j) ^ (n - 1))⁻¹ • ∫ u, f u ∂fullBandMeasure n j B := by
  rw [← integral_map_equiv, map_fullBandMeasure_dilation,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

end JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
