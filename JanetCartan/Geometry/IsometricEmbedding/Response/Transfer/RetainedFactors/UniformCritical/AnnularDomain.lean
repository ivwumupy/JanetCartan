module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AnnularCarriers

/-!
# Open convex buffers around the full retained annulus

The integration domain contains both the entire closed annular frequency
carrier and a neighborhood of the frozen primary covector. Its compact
closure remains in a larger normalized cone with a positive radial gap.
Enlarging this domain changes no mask or multiplier.

Consumer: the integration domain and critical-point containment in both
orientations of `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- The open convex frequency domain used to buffer both the full annular
support and the primary critical covectors
(`app:ch_response:eq:direct-envelope-profile`). -/
def retainedOpenAnnularFrequencyCarrier (ℓ : Euclidean d →L[ℝ] ℝ)
    (η₀ : Euclidean d) (ε aperture gap radius : ℝ) : Set E :=
  ball 0 radius ∩ (fullAngularCone ℓ η₀ ε aperture ∩
    {θ | gap < ℓ (spatialPart θ)})

/-- The common open annular domain is convex, so its integration-variable
segments stay inside the same conic chart
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedOpenAnnularFrequencyCarrier_open_convex
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    (ε aperture gap radius : ℝ) :
    IsOpen (retainedOpenAnnularFrequencyCarrier ℓ η₀ ε aperture gap radius) ∧
      Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ η₀ ε aperture gap radius) := by
  refine ⟨isOpen_ball.inter ((isOpen_fullAngularCone ℓ η₀ ε aperture).inter
    (isOpen_lt continuous_const (ℓ.continuous.comp spatialPartCLM.continuous))), ?_⟩
  exact (convex_ball (0 : E) radius).inter
    ((convex_fullAngularCone ℓ η₀ ε aperture).inter
      ((convex_Ioi gap).linear_preimage (ℓ.comp spatialPartCLM).toLinearMap))

/-- The compact closure of the open annular domain lies in the existing
closed carrier with twice the angular margins. Thus the already proved
normalization and Hessian estimates apply to every closed segment, including
boundary points (`app:ch_response:eq:direct-envelope-profile`). -/
theorem closure_retainedOpenAnnularFrequencyCarrier_subset
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    (ε aperture gap radius : ℝ) :
    closure (retainedOpenAnnularFrequencyCarrier ℓ η₀ ε aperture gap radius) ⊆
      retainedAnnularFrequencyCarrier ℓ η₀ (2 * ε) (2 * aperture) gap radius := by
  intro θ hθ
  refine ⟨closure_minimal (fun _ hv ↦ ball_subset_closedBall hv.1)
    isClosed_closedBall hθ, ?_⟩
  have hs := closure_mono (show retainedOpenAnnularFrequencyCarrier ℓ η₀ ε aperture gap radius ⊆
    fullAngularCone ℓ η₀ ε aperture ∩ {θ | gap < ℓ (spatialPart θ)} from
      fun _ hv ↦ hv.2) hθ
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hs

/-- Enlarge the integration carrier to contain the FULL retained annulus
and a fourfold ball around the frozen primary covector. The latter is
independent of the annular selector's radial endpoints. The open convex
domain has compact closure in the same larger conic chart and a positive
radial gap. Its constants precede every current field and frequency.

The frozen covector's cone membership is a fixed geometric condition, while
`RootDomain.exists_uniform_primary_pair_neighborhood` places the actual
primary gradients in the returned ball. This does not assume containment of
moving critical points (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_retained_open_annular_frequency_buffer
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    {ε aperture gap radius : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < gap)
    (θ₀ : E) (hθ : θ₀ ∈ fullAngularCone ℓ η₀ ε aperture)
    (hℓ : ℓ (spatialPart θ₀) = 1) :
    ∃ g > (0 : ℝ), ∃ R > (0 : ℝ), ∃ s > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier ℓ η₀ ε aperture g R
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier ℓ η₀ ε aperture gap radius ⊆ O ∧
      closedBall θ₀ (4 * s) ⊆ O ∧
      closure O ⊆ retainedAnnularFrequencyCarrier ℓ η₀ (2 * ε) (2 * aperture) g R := by
  let g := min gap 1 / 2
  let R := 1 + max radius ‖θ₀‖
  let O := retainedOpenAnnularFrequencyCarrier ℓ η₀ ε aperture g R
  have hg' : 0 < g := half_pos (lt_min hg zero_lt_one)
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right radius ‖θ₀‖, norm_nonneg θ₀]
  obtain ⟨hO, hOc⟩ := retainedOpenAnnularFrequencyCarrier_open_convex ℓ η₀ ε aperture g R
  have hsub := closure_retainedOpenAnnularFrequencyCarrier_subset ℓ η₀ ε aperture g R
  have hcompact : IsCompact (closure O) :=
    ((retainedAnnularFrequencyCarrier_compact_convex ℓ η₀ (2 * ε) (2 * aperture) g R).1).of_isClosed_subset
      isClosed_closure hsub
  have hθO : θ₀ ∈ O := by
    refine ⟨?_, hθ, ?_⟩
    · rw [mem_ball, dist_zero_right]
      dsimp [R]; linarith [le_max_right radius ‖θ₀‖]
    · change g < ℓ (spatialPart θ₀)
      rw [hℓ]
      dsimp [g]; linarith [min_le_right gap (1 : ℝ)]
  obtain ⟨s, hs, hsO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hθO)
  refine ⟨g, hg', R, hR, s / 8, by positivity, hO, hOc, hcompact, ?_,
    (closedBall_subset_ball (by linarith : 4 * (s / 8) < s)).trans hsO, hsub⟩
  intro θ hθD
  obtain ⟨hcone, _, hnorm⟩ := retainedAnnularFrequencyCarrier_geometry ℓ η₀ hε hAp hg hθD
  have hrad : gap ≤ ℓ (spatialPart θ) :=
    closure_minimal (fun _ hv ↦ hv.2.le)
      (isClosed_le continuous_const (ℓ.continuous.comp spatialPartCLM.continuous)) hθD.2
  refine ⟨?_, hcone, ?_⟩
  · rw [mem_ball, dist_zero_right]
    dsimp [R]; linarith [le_max_left radius ‖θ₀‖]
  · dsimp [g]; linarith [min_le_left gap (1 : ℝ)]

end JanetCartan.ResponseTransfer.RetainedFactors
