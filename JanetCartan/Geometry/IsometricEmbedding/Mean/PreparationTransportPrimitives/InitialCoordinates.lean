module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparationTransportPrimitives.Characteristic
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Reparametrization

/-!
# Original scalar coordinates for preparation

The scalar in `app:ch_mean_pairs:eq:mean-density-lipschitz` is expressed in
`(z,y)` coordinates. The characteristic formula uses `(y,z)` with the three
carrier coordinates reassembled. This fixed linear relabeling preserves the
exact initial compact as its image; it introduces no cutoff or enlargement.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff

namespace JanetCartan.CurrentMean.PreparationTransportPrimitives
open ContinuumRow NullTransport.AmplitudeTame

/-- The fixed initial-coordinate relabeling of
`app:ch_mean_pairs:eq:mean-density-recursion`, without any flow or cutoff. -/
def preparationInitialRelabel {n : ℕ} :
    (Euclidean (n - 1) × Euclidean 3) →L[ℝ] CarrierVariable n :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p ↦ (TransportKernel.sliceCoordinates 2 p.2, p.1)
    map_add' := by intro p q; rfl
    map_smul' := by intro a p; rfl }

/-- The original open scalar domain remains open after the fixed relabeling.
This supplies the local norm input of the reserve-fourteen transport bound,
without imposing global scalar smoothness
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationInitialRelabel_isOpenMap {n : ℕ} :
    IsOpenMap (preparationInitialRelabel (n := n)) := by
  apply ContinuousLinearMap.isOpenMap
  intro p
  refine ⟨(p.2, (TransportKernel.sliceCoordinates 2).symm p.1), ?_⟩
  change ((TransportKernel.sliceCoordinates 2)
    ((TransportKernel.sliceCoordinates 2).symm p.1), p.2) = p
  simp

/-- Returning an actual retained initial scalar to characteristic coordinates
recovers that exact function. Thus the history construction's `CarrierData`
uses the original scalar, not another existential choice
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
@[simp] theorem preparationCharacteristicInitial_initialScalar {n : ℕ}
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    preparationCharacteristicInitial (ContinuumAdjoint.Canonical.initialScalar initial) =
      initial := by
  funext p
  simp only [preparationCharacteristicInitial, ContinuumAdjoint.Canonical.initialScalar,
    CanonicalCarrier.parameter_eq_sliceCoordinates_symm, MeasurableEquiv.symm_apply_apply]

/-- Every smooth scalar on the original preparation space gives smooth
characteristic initial data (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem preparationCharacteristicInitial_contDiff {n : ℕ}
    {u : CarrierVariable n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (preparationCharacteristicInitial u) :=
  hu.comp preparationInitialRelabel.contDiff

/-- Relabeling bounds the scalar on exactly the original initial compact,
with no derivative loss (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem cNorm_preparationCharacteristicInitial_le {n : ℕ}
    {I : Set (Euclidean (n - 1) × Euclidean 3)} (hI : IsCompact I)
    {u : CarrierVariable n → ℝ} (hu : ContDiff ℝ ∞ u) (s : ℕ) :
    cNorm I s (preparationCharacteristicInitial u) ≤
      linearNormCost (preparationInitialRelabel (n := n)) s *
        cNorm (preparationInitialRelabel '' I) s u :=
  cNorm_comp_linear_le preparationInitialRelabel
    (hI.image preparationInitialRelabel.continuous) isOpen_univ (subset_univ _)
    hu.contDiffOn (mapsTo_image _ _) s

/-- Scalar relabeling needs smoothness only on the prescribed open initial
domain containing the retained compact. Its norm still uses exactly the
image of that compact and loses no derivatives
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem cNorm_preparationCharacteristicInitial_le_on {n : ℕ}
    {I : Set (Euclidean (n - 1) × Euclidean 3)} (hI : IsCompact I)
    {D : Set (CarrierVariable n)} (hD : IsOpen D)
    (hID : preparationInitialRelabel '' I ⊆ D)
    {u : CarrierVariable n → ℝ} (hu : ContDiffOn ℝ ∞ u D) (s : ℕ) :
    cNorm I s (preparationCharacteristicInitial u) ≤
      linearNormCost (preparationInitialRelabel (n := n)) s *
        cNorm (preparationInitialRelabel '' I) s u :=
  cNorm_comp_linear_le preparationInitialRelabel
    (hI.image preparationInitialRelabel.continuous) hD hID hu (mapsTo_image _ _) s

end JanetCartan.CurrentMean.PreparationTransportPrimitives
