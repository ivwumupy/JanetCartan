module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalDataBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LebesgueData
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition

/-!
# The same canonical datum on the grouped wide-band input

The two-shell isometry identifies the original wide-band adjoint input with
`CanonicalDataBounds.fourierDensity` and `initialDatum`. It is a change of
Hilbert coordinates, not a replacement row or inverse. Every smaller prefix
acts on the full fixed input and retains both pieces of each original band.
These identities supply the data part of `main:eq:old-canonical` and
`main:eq:variation` to the canonical smooth-realization consumer.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalTailRealization
open RawInputPartition RawInputRealization CanonicalDataBounds

variable {n J : ℕ} {Y : Type*} [NormedAddCommGroup Y]
  [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The SAME real wide-band row in the existing two-shell coordinates
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
def refinedRow (A : WideInput n J →L[ℝ] Y) : RefinedInput n J →L[ℝ] Y :=
  A.comp (realWideRefinement n J).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The real adjoint commutes with the actual isometric reassembly; no
independent canonical input is selected (`main:eq:old-canonical`). -/
theorem adjoint_refinedRow (A : WideInput n J →L[ℝ] Y) (q : Y) :
    (refinedRow A).adjoint q = realWideRefinement n J (A.adjoint q) := by
  rw [refinedRow, ContinuousLinearMap.adjoint_comp]
  change ((realWideRefinement n J).symm : RefinedInput n J →L[ℝ] WideInput n J).adjoint
    (A.adjoint q) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  rfl

/-- The literal canonical density represents the unchanged smooth wide-band
sum, including its original detector and high-pass
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem fourierDensity_refinedRow_eq_wideDensity
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (A : WideInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y) (r : Y) :
    fourierDensity (fun i : RefinedIndex J ↦ weightedRadialBand d i.1.val)
      (refinedRow A) Q0 r =ᵐ[volume] weightedWideDensity d (A.adjoint (Q0 r)) := by
  simp only [fourierDensity, adjointInput, adjoint_refinedRow]
  exact (weightedWideDensity_eq_refined hd hM hb _).symm

/-- Equality of the actual uncut initial fields holds everywhere, after
integrating the almost-everywhere density identity
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem initialDatum_refinedRow_eq_wideField
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (A : WideInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y) (r : Y) :
    initialDatum (fun i : RefinedIndex J ↦ weightedRadialBand d i.1.val)
      (refinedRow A) Q0 r = weightedWideField d (A.adjoint (Q0 r)) := by
  simp only [initialDatum, adjointInput, adjoint_refinedRow]
  exact (weightedWideField_eq_refined hd hM hb _).symm

/-- The existing real grouped prefix is self-adjoint; the grouping is by
original band, not by an independently truncated sharp piece
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_realRefinedPrefix (L : ℕ) :
    ((refinedPrefix n J L).restrictScalars ℝ).adjoint =
      (refinedPrefix n J L).restrictScalars ℝ :=
  RawInputHilbert.adjoint_realCoordinateProjection _

/-- Every prefix row is a restriction of the same full row
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def groupedPrefixRow (A : RefinedInput n J →L[ℝ] Y) (K : ℝ) :
    RefinedInput n J →L[ℝ] Y :=
  A.comp ((refinedPrefix n J (cutoffCount K)).restrictScalars ℝ)

/-- All cutoff-dependent canonical inputs use the same adjoint and `Q0`,
followed by the literal grouped prefix (`main:eq:old-canonical`). -/
theorem adjointInput_groupedPrefixRow (A : RefinedInput n J →L[ℝ] Y)
    (Q0 : Y →L[ℝ] Y) (K : ℝ) (r : Y) :
    adjointInput (groupedPrefixRow A K) Q0 r =
      refinedPrefix n J (cutoffCount K) (A.adjoint (Q0 r)) := by
  rw [adjointInput, groupedPrefixRow, ContinuousLinearMap.adjoint_comp,
    adjoint_realRefinedPrefix]
  rfl

/-- The same finite prefix in wide-band coordinates and sharp coordinates
produces exactly the same canonical initial field
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem initialDatum_groupedPrefixRow_eq_wideField
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (A : WideInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y) (K : ℝ) (r : Y) :
    initialDatum (fun i : RefinedIndex J ↦ weightedRadialBand d i.1.val)
      (groupedPrefixRow (refinedRow A) K) Q0 r =
      weightedWideField d (widePrefix n J (cutoffCount K) (A.adjoint (Q0 r))) := by
  rw [initialDatum, adjointInput_groupedPrefixRow, adjoint_refinedRow]
  change field _ (refinedPrefix n J (cutoffCount K)
    (wideRefinement n J (A.adjoint (Q0 r)))) = _
  rw [← wideRefinement_prefix]
  exact (weightedWideField_eq_refined hd hM hb _).symm

/-- The existing smooth canonical derivative is unchanged by the SAME real
Hilbert coordinate change used for its initial Fourier datum. This supplies
the coordinate identification for the actual raw derivative map once produced;
it does not posit a second physical wave map
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem smoothCanonicalDerivative_refinedRow
    {ι m : Type*} [Fintype ι] [Fintype m]
    (A : ι → WideInput n J →L[ℝ] ContinuumRow.OutputL2 n)
    (G : ι → WideInput n J →ₗ[ℝ]
      CurrentMean.SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (Q0 : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (r : ContinuumRow.OutputL2 n) :
    CanonicalChange.smoothCanonicalDerivative (fun i ↦ refinedRow (A i))
      (fun i ↦ (G i).comp (realWideRefinement n J).symm.toLinearEquiv.toLinearMap) Q0 r =
      CanonicalChange.smoothCanonicalDerivative A G Q0 r := by
  apply Subtype.ext
  funext x i
  change ((G i) ((realWideRefinement n J).symm ((refinedRow (A i)).adjoint (Q0 r)))).val x () =
    ((G i) ((A i).adjoint (Q0 r))).val x ()
  rw [adjoint_refinedRow, LinearIsometryEquiv.symm_apply_apply]

end JanetCartan.CanonicalTailRealization
