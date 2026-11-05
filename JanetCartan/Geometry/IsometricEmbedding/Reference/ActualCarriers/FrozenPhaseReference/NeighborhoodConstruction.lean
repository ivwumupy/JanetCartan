module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.NeighborhoodConstruction.CanonicalMomentum
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.NeighborhoodConstruction.NeighborhoodBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.NeighborhoodConstruction.RootBuffer

/-!
# Construction of the local frozen reference

For `app:lem:common-hamilton-phase` and
`app:ch_seed:prop:seed-actual-menu`, Step 1, the adapted section determines the
literal Hamilton family. Its affine phase and characteristic inverse are
proved in `NeighborhoodConstruction.CanonicalMomentum` from injectivity of the
energy/tangential-momentum map on the retained state ball.

The scalar-root buffer and the open covector/physical neighborhood selection
instantiate these results to construct every field of `LocalFrozenReference`.
The retained family supplies both the reference chart and its low-order
perturbations for the subsequent frozen-patch and finite-menu constructions.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace

namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open HamiltonPhase

/-- Construct the literal frozen Hamilton family for an adapted section in
any supplied open state buffer. The characteristic and determinant hypotheses
discharge the energy and transversality inputs of the chart producer
(`app:lem:common-hamilton-phase`, `app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_frozenHamiltonFamily_of_adapted {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0) (a : AdaptedSection ξ)
    {D : Set (Euclidean n × Euclidean n)} (hD : IsOpen D)
    (hDH : D ⊆ (frozenSymbol n).domain) {R : ℝ} (hR : 0 < R)
    (hRD : closedBall (0, ξ) R ⊆ D) :
    Nonempty (FrozenHamiltonFamily a.embedding a.normal a.baseData ⟪a.normal, ξ⟫_ℝ D R) := by
  apply exists_frozenHamiltonFamily hD hDH a.embedding a.normal a.orthogonal a.spanning hR
  · simpa only [a.baseState_eq] using hRD
  · rw [a.baseState_eq, frozenSymbol_h]
    simp [hchar, AdaptedSection.baseData]
  · rw [a.baseState_eq]
    exact (frozenSymbol_transverse_pos hξ hchar a.determinant_positive).ne'

/-- Construct the local affine frozen reference from a nonzero characteristic
covector and its adapted section (`app:lem:common-hamilton-phase`,
`app:ch_seed:prop:seed-actual-menu`, Step 1). Scalar-root uniqueness and the
actual frozen Hamilton ODE prove the affine phase and characteristic inverse
for the same retained family. This supplies the local reference consumed by
`exists_frozenPatchData_of_localReference` in the finite-menu construction. -/
theorem exists_localFrozenReference {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0) (a : AdaptedSection ξ) :
    Nonempty (LocalFrozenReference a) := by
  obtain ⟨D, R, hD, hDH, hR, hRD, hinj⟩ := exists_frozenRootBuffer hξ hchar a
  obtain ⟨F⟩ := exists_frozenHamiltonFamily_of_adapted hξ hchar a hD hDH hR hRD
  obtain ⟨V, c, ρ, hV, hξV, hVR, hVzero, hc, hgap, hρ, htarget, hsource⟩ :=
    exists_frozenReferenceNeighborhoods hξ a hR F
  refine ⟨{
    stateDomain := D
    stateRadius := R
    state_open := hD
    state_subset := hDH
    stateRadius_pos := hR
    stateBall_subset := by simpa only [a.baseState_eq] using hRD
    family := F
    covectorSet := V
    covectorSet_open := hV
    covectorSet_base := hξV
    covectorSet_nonzero := hVzero
    determinantGap := c
    determinantGap_pos := hc
    determinant_gap := hgap
    radius := ρ
    radius_pos := hρ
    covector := F.canonicalMomentum
    phase_linear := fun _ hq ↦ F.phase_eq_canonicalMomentum hinj hq
    covector_inverse := ?_
    target_contains := htarget
    section_source := hsource }⟩
  intro p hp hpchar
  exact F.canonicalMomentum_eq_of_characteristic hinj (hVR hp) hpchar
    (F.canonicalDatum_mem (htarget 0 (mem_ball_self hρ) p hp))

end JanetCartan.ActualCarriers.FrozenPhaseReference
