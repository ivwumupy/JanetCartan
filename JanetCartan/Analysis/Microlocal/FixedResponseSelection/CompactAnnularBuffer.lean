module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.AnnularDomain

/-!
# One annular buffer for compact source incidences

The source compact can contain several labels and radial values on the same
angular sector. Compactness bounds its radial section below and its norm above,
so one open integration annulus contains all its covectors together with the
original complete annular multiplier support. The solver chart is unchanged.
Consumer: same-chart stationary selection for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Enlarge the same integration annulus to contain EVERY frozen covector
in a compact incidence set. Its original full annular carrier is retained,
as are a positive radial gap, convexity and compact closure in the doubled
cone. No radial normalization of the source is imposed
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_retained_open_annular_frequency_buffer_of_compact
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    {ε aperture gap radius : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < gap)
    {F : Set E} (hF : IsCompact F) (hFcone : F ⊆ fullAngularCone ℓ η₀ ε aperture) :
    ∃ g > (0 : ℝ), ∃ R > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier ℓ η₀ ε aperture g R
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier ℓ η₀ ε aperture gap radius ⊆ O ∧
      F ⊆ O ∧
      closure O ⊆ retainedAnnularFrequencyCarrier ℓ η₀ (2 * ε) (2 * aperture) g R := by
  obtain ⟨m, hm, hbound⟩ := hF.exists_forall_le'
    (ℓ.continuous.comp spatialPartCLM.continuous).continuousOn
    (fun θ hθ ↦ (hFcone hθ).1.1)
  change ∀ θ ∈ F, m ≤ ℓ (spatialPart θ) at hbound
  obtain ⟨B, hB, hnorm⟩ := hF.isBounded.exists_pos_norm_le
  let g := min gap m / 2
  let R := 1 + max radius B
  have hg' : 0 < g := half_pos (lt_min hg hm)
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right radius B]
  obtain ⟨hO, hOc⟩ := retainedOpenAnnularFrequencyCarrier_open_convex ℓ η₀ ε aperture g R
  have hclosure := closure_retainedOpenAnnularFrequencyCarrier_subset ℓ η₀ ε aperture g R
  refine ⟨g, hg', R, hR, hO, hOc,
    ((retainedAnnularFrequencyCarrier_compact_convex ℓ η₀ (2 * ε) (2 * aperture) g R).1).of_isClosed_subset
      isClosed_closure hclosure, ?_, ?_, hclosure⟩
  · intro θ hθ
    have hgeometry := retainedAnnularFrequencyCarrier_geometry ℓ η₀ hε hAp hg hθ
    have hrad : gap ≤ ℓ (spatialPart θ) :=
      closure_minimal (t := {θ : E | gap ≤ ℓ (spatialPart θ)})
        (fun θ (hv : θ ∈ fullAngularCone ℓ η₀ (ε / 2) (aperture / 2) ∩
          {θ | gap < ℓ (spatialPart θ)}) ↦
            show gap ≤ ℓ (spatialPart θ) from (show gap < ℓ (spatialPart θ) from hv.2).le)
        (isClosed_le continuous_const (ℓ.continuous.comp spatialPartCLM.continuous)) hθ.2
    refine ⟨?_, hgeometry.1, ?_⟩
    · rw [mem_ball, dist_zero_right]
      dsimp [R]
      linarith [hgeometry.2.2, le_max_left radius B]
    · change g < ℓ (spatialPart θ)
      dsimp [g]
      linarith [min_le_left gap m]
  · intro θ hθ
    refine ⟨?_, hFcone hθ, ?_⟩
    · rw [mem_ball, dist_zero_right]
      dsimp [R]
      linarith [hnorm θ hθ, le_max_right radius B]
    · change g < ℓ (spatialPart θ)
      dsimp [g]
      linarith [hbound θ hθ, min_le_right gap m]

end JanetCartan.ResponseTransfer.RetainedFactors
