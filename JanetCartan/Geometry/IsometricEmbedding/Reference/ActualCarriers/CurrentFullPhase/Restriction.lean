module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.MomentumComparison

/-!
# Restricting the actual full charts to a common target

These elementary restrictions preserve the chosen coordinates and every jet.
The consumer is the common reference/current target in `CarrierFullPhaseInput`
(`app:ch_seed:prop:seed-actual-menu`, Step 1).
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology
namespace JanetCartan.ActualCarriers.CurrentFullPhase
open HamiltonPhase

/-- Restrict a full chart to an open subtarget, retaining its actual inverse
coordinates (`app:lem:common-hamilton-phase`). -/
def restrictChart {n : ℕ} {H : HomogeneousSymbol (Euclidean n)}
    {Φ : HamiltonFlow H (Euclidean (n - 1))} (C : ProjectionChart Φ)
    {V : Set (Euclidean n × (ℝ × Euclidean (n - 1)))} (hV : IsOpen V)
    (hVC : V ⊆ C.target) : ProjectionChart Φ where
  source := C.source ∩ Φ.augmentedProjection ⁻¹' V
  target := V
  isOpen_source := (show ContinuousOn Φ.augmentedProjection C.source from
    fun q hq ↦ (Φ.hasFDerivAt_augmentedProjection
      (C.source_admissible q hq)).continuousAt.continuousWithinAt).isOpen_inter_preimage
        C.isOpen_source hV
  isOpen_target := hV
  coordinates := C.coordinates
  derivative := C.derivative
  hasFDerivAt_coordinates := fun z hz ↦ C.hasFDerivAt_coordinates z (hVC hz)
  source_admissible := fun q hq ↦ C.source_admissible q hq.1
  maps_to_source := fun z hz ↦ ⟨C.maps_to_source z (hVC hz), by
    change (Φ.position (chartLift C.coordinates z), z.2) ∈ V
    rw [C.right_inverse z (hVC hz)]
    exact hz⟩
  maps_to_target := fun _ hq ↦ hq.2
  right_inverse := fun z hz ↦ C.right_inverse z (hVC hz)
  left_inverse := fun q hq ↦ C.left_inverse q hq.1

/-- Restriction preserves the source-ball description, used to prove the
current zero-section containment (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem restrictChart_source_eq {n : ℕ} {H : HomogeneousSymbol (Euclidean n)}
    {Φ : HamiltonFlow H (Euclidean (n - 1))} (C : ProjectionChart Φ)
    {V : Set (Euclidean n × (ℝ × Euclidean (n - 1)))} (hV : IsOpen V)
    (hVC : V ⊆ C.target) {B : Set (ℝ × InitialData (Euclidean (n - 1)))}
    (hsource : C.source = B ∩ Φ.augmentedProjection ⁻¹' C.target) :
    (restrictChart C hV hVC).source = B ∩ Φ.augmentedProjection ⁻¹' V := by
  change (C.source ∩ Φ.augmentedProjection ⁻¹' V) = _
  rw [hsource]
  ext q
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hVC h.2⟩, h.2⟩⟩

/-- Equality of phases on an open neighborhood transports the comparison
seminorm without losing derivatives (`app:lem:common-hamilton-phase`). -/
theorem cNorm_sub_eq_of_phase_eqOn {n : ℕ}
    {V K : Set (Euclidean n × (ℝ × Euclidean (n - 1)))} (hV : IsOpen V)
    (hKV : K ⊆ V) {f g : Euclidean n × (ℝ × Euclidean (n - 1)) → ℝ}
    (he : EqOn f g V) (s : Euclidean n × (ℝ × Euclidean (n - 1)) → ℝ) (m : ℕ) :
    cNorm K m (s - f) = cNorm K m (s - g) := by
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Set.image_congr
  intro z hz
  have hh : s - f =ᶠ[𝓝 z] s - g :=
    eventuallyEq_of_mem (hV.mem_nhds (hKV hz)) (fun w hw ↦ by simp only [Pi.sub_apply, he hw])
  exact congrArg norm ((hh.iteratedFDeriv ℝ k).eq_of_nhds)

end JanetCartan.ActualCarriers.CurrentFullPhase
