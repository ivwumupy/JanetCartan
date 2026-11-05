module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.BufferedFamily
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Inputs

/-!
# Interfaces for the local frozen reference construction

These output types separate the local construction from its consumers.
`NeighborhoodConstruction.exists_localFrozenReference` constructs every field
from a nonzero characteristic covector and an adapted orthogonal section,
including the affine identity and inverse-covector identity. The restriction
below supplies exactly the reference argument consumed by
`exists_finite_carrierPhase_assembly`; the main `FrozenPhaseReference` module
constructs the finite decorated cover from `5 ≤ n` alone.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace

namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open HamiltonPhase FrozenMenu

/-- Output of orienting the determinant differential and choosing an orthogonal
section (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
structure AdaptedSection {n : ℕ} (ξ : Euclidean n) where
  normal : Euclidean n
  embedding : Euclidean (n - 1) →ₗᵢ[ℝ] Euclidean n
  normal_unit : ‖normal‖ = 1
  orthogonal : ∀ u, ⟪normal, embedding u⟫_ℝ = 0
  spanning : ∀ x, ⟪normal, x⟫_ℝ = 0 → ∃ u, embedding u = x
  determinant_positive : 0 < fderiv ℝ cubeDeterminant ξ normal

/-- Canonical base datum at the physical origin
(`app:lem:common-hamilton-phase`). -/
def AdaptedSection.baseData {n : ℕ} {ξ : Euclidean n} (a : AdaptedSection ξ) :
    InitialData (Euclidean (n - 1)) :=
  (0, (0, a.embedding.toContinuousLinearMap.adjoint ξ))

/-- Output of the actual local Hamilton construction at a frozen covector.
Every phase and root identity below is proved by the local existence theorem.
The same family contains the reference
chart and all low-order perturbation witnesses (`app:lem:common-hamilton-phase`,
`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
structure LocalFrozenReference {n : ℕ} {ξ : Euclidean n} (a : AdaptedSection ξ) where
  stateDomain : Set (Euclidean n × Euclidean n)
  stateRadius : ℝ
  state_open : IsOpen stateDomain
  state_subset : stateDomain ⊆ (frozenSymbol n).domain
  stateRadius_pos : 0 < stateRadius
  stateBall_subset : closedBall
    (transverseSectionState a.embedding a.normal (a.baseData, ⟪a.normal, ξ⟫_ℝ))
    stateRadius ⊆ stateDomain
  family : FrozenHamiltonFamily a.embedding a.normal a.baseData ⟪a.normal, ξ⟫_ℝ
    stateDomain stateRadius
  covectorSet : Set (Euclidean n)
  covectorSet_open : IsOpen covectorSet
  covectorSet_base : ξ ∈ covectorSet
  covectorSet_nonzero : ∀ p ∈ covectorSet, p ≠ 0
  determinantGap : ℝ
  determinantGap_pos : 0 < determinantGap
  determinant_gap : ∀ p ∈ covectorSet,
    determinantGap ≤ fderiv ℝ cubeDeterminant p a.normal
  radius : ℝ
  radius_pos : 0 < radius
  covector : (ℝ × Euclidean (n - 1)) → Euclidean n
  phase_linear : ∀ q ∈ family.chart.target,
    phase family.chart.coordinates q = ⟪covector q.2, q.1⟫_ℝ
  covector_inverse : ∀ p ∈ covectorSet, cubeDeterminant p = 0 →
    covector (0, a.embedding.toContinuousLinearMap.adjoint p) = p
  target_contains : ∀ x ∈ ball (0 : Euclidean n) radius, ∀ p ∈ covectorSet,
    (x, (0, a.embedding.toContinuousLinearMap.adjoint p)) ∈ family.chart.target
  section_source : ∀ u, a.embedding u ∈ ball (0 : Euclidean n) radius →
    ∀ p ∈ covectorSet,
      (0, (u, (0, a.embedding.toContinuousLinearMap.adjoint p))) ∈ family.chart.source

/-- Decorated frozen patch retained through the incidence cover construction.
This is an output specification, not an assumed finite menu
(`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4). -/
structure FrozenPatchData {n : ℕ} (P : Patch n) where
  center : Euclidean n
  adapted : AdaptedSection center
  localReference : LocalFrozenReference adapted
  center_eq : P.toFun 0 = center
  buffered_mem : ∀ z ∈ parameterCube (2 * P.radius),
    P.toFun z ∈ localReference.covectorSet
  buffered_characteristic : ∀ z ∈ parameterCube (2 * P.radius),
    cubeDeterminant (P.toFun z) = 0
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  buffered_annulus : ∀ z ∈ parameterCube (2 * P.radius),
    lower ≤ ‖P.toFun z‖ ∧ ‖P.toFun z‖ ≤ upper

/-- Restriction of the already constructed local reference, preserving its
literal symbol, flow and chart. This discharges the type of the `R` argument of
`exists_finite_carrierPhase_assembly`; existence of `FrozenPatchData` is still
required (`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
def FrozenPatchData.reference {n : ℕ} {P : Patch n} (d : FrozenPatchData P) :
    CarrierPhaseReference P where
  sectionEmbedding := d.adapted.embedding
  symbol := frozenSymbol n
  flow := d.localReference.family.flow
  chart := d.localReference.family.chart
  radius := d.localReference.radius
  radius_pos := d.localReference.radius_pos
  momentum_smooth := d.localReference.family.reference_control.momentum_smooth
  coordinates_smooth := by
    rw [d.localReference.family.reference_control.target_eq]
    exact d.localReference.family.reference_control.coordinates_smooth
  covector := d.localReference.covector
  phase_linear := d.localReference.phase_linear
  patch_covector := fun z hz ↦ d.localReference.covector_inverse _
    (d.buffered_mem z (fun i ↦ (hz i).le))
    (d.buffered_characteristic z (fun i ↦ (hz i).le))
  target_contains := fun x hx z hz ↦ d.localReference.target_contains x hx _
    (d.buffered_mem z (fun i ↦ (hz i).le))

/-- The same section map survives restriction to the literal patch indices
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem FrozenPatchData.reference_section_eq {n : ℕ} {P : Patch n} (d : FrozenPatchData P) :
    d.reference.flow.sectionMap = d.reference.sectionEmbedding.toContinuousLinearMap :=
  d.localReference.family.reference_control.section_eq

/-- Buffered zero-section source containment for the same chosen reference
chart (`app:lem:common-hamilton-phase`). -/
theorem FrozenPatchData.reference_section_source {n : ℕ} {P : Patch n} (d : FrozenPatchData P)
    {u : Euclidean (n - 1)} (hu : d.reference.sectionEmbedding u ∈ ball 0 d.reference.radius)
    {z : Euclidean 3} (hz : z ∈ parameterCube (2 * P.radius)) :
    (0, (u, (0, d.reference.spatialPatch z))) ∈ d.reference.chart.source :=
  d.localReference.section_source u hu _ (d.buffered_mem z hz)

/-- The doubled closed patch has a strictly positive adapted determinant
partial derivative, with no appeal to inner-cube validity
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem FrozenPatchData.buffered_transverse_pos {n : ℕ} {P : Patch n} (d : FrozenPatchData P)
    {z : Euclidean 3} (hz : z ∈ parameterCube (2 * P.radius)) :
    0 < fderiv ℝ cubeDeterminant (P.toFun z) d.adapted.normal :=
  d.localReference.determinantGap_pos.trans_le
    (d.localReference.determinant_gap _ (d.buffered_mem z hz))

end JanetCartan.ActualCarriers.FrozenPhaseReference
