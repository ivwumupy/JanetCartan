module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Hamilton.Flow

/-!
# The named source-dilated inverse projection chart

Both inverse identities and domain containments for the explicit inverse in
`app:ch_background:eq:bg-Nsigma`. Its coordinates are literally
`sourceCoordinates`; the label and Cauchy section are those of the seed chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology InnerProductSpace

namespace JanetCartan.NormalizedBackground.SourceGeometry
open HamiltonPhase

variable {E U : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U}

/-- The explicit inverse of the source-dilated Hamilton projection
(`app:ch_background:eq:bg-Nsigma`). All domains are preimages of the seed domains. -/
def sourceProjectionChart (C : ProjectionChart Φ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ProjectionChart (sourceHamiltonFlow Φ hρ) where
  source := sourceFlowMap ρ ⁻¹' C.source
  target := sourceDilationMap ρ ⁻¹' C.target
  isOpen_source := C.isOpen_source.preimage (sourceFlowMap ρ).continuous
  isOpen_target := C.isOpen_target.preimage (sourceDilationMap ρ).continuous
  coordinates := sourceCoordinates C.coordinates ρ
  derivative z := ρ⁻¹ • (C.derivative (sourceDilationMap ρ z)).comp (sourceDilationMap ρ)
  hasFDerivAt_coordinates := by
    intro z hz
    exact ((C.hasFDerivAt_coordinates _ hz).comp z
      (sourceDilationMap (E := E) (V := ℝ × U) ρ).hasFDerivAt).const_smul ρ⁻¹
  source_admissible := by
    intro q hq
    exact C.source_admissible _ hq
  maps_to_source := by
    intro z hz
    simpa [chartLift, sourceCoordinates, smul_smul, hρ] using C.maps_to_source _ hz
  maps_to_target := by
    intro q hq
    simpa [sourceHamiltonFlow, smul_smul, hρ] using C.maps_to_target _ hq
  right_inverse := by
    intro z hz
    have hi := congrArg (fun x ↦ ρ⁻¹ • x) (C.right_inverse _ hz)
    simpa [sourceHamiltonFlow, chartLift, sourceCoordinates, smul_smul, hρ] using hi
  left_inverse := by
    intro q hq
    have hi := congrArg (fun x : ℝ × U ↦ ρ⁻¹ • x) (C.left_inverse _ hq)
    simpa [sourceHamiltonFlow, sourceCoordinates, smul_smul, hρ] using hi

/-- The constructed chart uses exactly the inverse coordinates specified by
`app:ch_background:eq:bg-Nsigma`. -/
@[simp] theorem sourceProjectionChart_coordinates (C : ProjectionChart Φ)
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    (sourceProjectionChart C hρ).coordinates = sourceCoordinates C.coordinates ρ := rfl

/-- Identification of the constructed phase, with no choice of a second inverse
(`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceProjectionChart_phase (C : ProjectionChart Φ)
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    phase (sourceProjectionChart C hρ).coordinates = sourcePhase (phase C.coordinates) ρ := by
  funext z
  exact phase_sourceCoordinates C.coordinates ρ z

/-- The full phase differential has transported momentum and the actual divided
canonical footpoint (`app:lem:common-hamilton-phase`, `app:ch_background:eq:bg-Nsigma`). -/
theorem hasFDerivAt_sourceHamiltonPhase (C : ProjectionChart Φ)
    {ρ : ℝ} (hρ : ρ ≠ 0) {z : E × (ℝ × U)}
    (hz : (ρ • z.1, z.2) ∈ C.target) :
    HasFDerivAt (sourcePhase (phase C.coordinates) ρ)
      (phaseDifferential (Φ.momentum (chartLift C.coordinates (ρ • z.1, z.2)))
        (sourceCoordinates C.coordinates ρ z)) z := by
  have hd := (sourceProjectionChart C hρ).hasFDerivAt_phase hz
  rw [sourceProjectionChart_phase C hρ] at hd
  simpa [sourceProjectionChart, sourceHamiltonFlow, chartLift, sourceCoordinates,
    smul_smul, hρ] using hd

/-- The unchanged section has the unchanged Cauchy value
(`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceHamiltonPhase_initial_value (C : ProjectionChart Φ)
    {ρ : ℝ} (hρ : ρ ≠ 0) {u : U} {η : ℝ × U}
    (hs : (0, (ρ • u, η)) ∈ C.source) :
    sourcePhase (phase C.coordinates) ρ (Φ.sectionMap u, η) = inner ℝ u η.2 := by
  have hi := (sourceProjectionChart C hρ).initial_value (u := u) (η := η)
    (by simpa [sourceProjectionChart] using hs)
  rw [sourceProjectionChart_phase C hρ] at hi
  exact hi

/-- The centered seed Cauchy value needed for the integral zero-scale phase
extension in `app:ch_background:prop:bg-normalized`. -/
theorem seedHamiltonPhase_zero (C : ProjectionChart Φ) {η : ℝ × U}
    (hs : (0, (0, η)) ∈ C.source) : phase C.coordinates (0, η) = 0 := by
  simpa using C.initial_value hs

end JanetCartan.NormalizedBackground.SourceGeometry
