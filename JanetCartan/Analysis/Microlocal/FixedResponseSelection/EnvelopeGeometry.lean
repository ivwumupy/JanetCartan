module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.IncidenceParameters
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SelectorGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Phase.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.PrimaryGradientBand
public import Mathlib.Algebra.Order.Field.Pi

/-!
# Radial margins of the original full-source envelope

The actual frozen source covectors on their original compact give positive
lower and upper radial bounds. These determine the annulus needed by the
source-gradient selector before the stationary domain is constructed. A finite
family of retained stationary annuli also determines one amplitude budget band.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu LeadingWave.FullModulation
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Compactness and the original Hamilton energy identity bound the full
frozen covectors away from zero, before reference and history. These bounds
control every center's literal `norm / 2` and `2 * norm` gradient band in
`FullSourceEnvelopes.exists_fullSource_gradient_band`
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_full_source_frozen_gradient_bounds_on_compact
    {Csrc : Set (Euclidean 3 × Euclidean d)} (hCsrc : IsCompact Csrc)
    (hcsrc : ∀ c ∈ Csrc,
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius) :
    ∃ normLo > (0 : ℝ), ∃ normHi > (0 : ℝ),
      ∀ c ∈ Csrc, normLo ≤ ‖T.reference.covector (0, c.2)‖ ∧
        ‖T.reference.covector (0, c.2)‖ ≤ normHi := by
  let F := fun c : Euclidean 3 × Euclidean d ↦ T.reference.covector (0, c.2)
  have hF : ContinuousOn F Csrc := T.continuousOn_frozen_full_source_pair.snd.comp
    (f := fun c ↦ ((0 : Euclidean (d+1)), c))
    (continuousOn_const.prodMk continuousOn_id) (fun c hc ↦
      T.full_source_mem_phaseDomain_of_physical_buffer
        (mem_closedBall_self T.physicalRadius_pos.le) (hcsrc c hc))
  obtain ⟨lo, hlo, hlower⟩ := hCsrc.exists_forall_le' hF.norm
    (fun c hc ↦ norm_pos_iff.mpr (T.full_source_frozen_covector_regular (hcsrc c hc)).1)
  obtain ⟨hi, hhi, hupper⟩ := (hCsrc.image_of_continuousOn hF).isBounded.exists_pos_norm_le
  exact ⟨lo, hlo, hi, hhi, fun c hc ↦ ⟨hlower c hc, hupper _ (mem_image_of_mem F hc)⟩⟩


/-- The original full-phase differential producer supplies a single gradient
band on the entire retained physical and parameter incidence. This precedes
the stationary annulus and requires no new parameter ball. Consumer:
`RetainedCharacteristicEnvelopes.fullSource_physical_incidence_solver_residual_envelopes`
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_full_source_gradient_band_on_physical_incidence
    (i : Fin (d + 1)) (z : RootState (Euclidean d)) (ε : ℝ)
    {A : Set (Euclidean 3 × Euclidean d)} (hA : IsCompact A)
    (hprimary : ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
      ((CompatibleResponse.primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T) :
    ∃ sourceLower sourceUpper δ : ℝ,
      0 < sourceLower ∧ sourceLower < sourceUpper ∧ 0 < δ ∧ δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean (d+1)) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d+1)) < δ →
      ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
        sourceLower ≤ ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1‖ ∧
        ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1‖ ≤ sourceUpper := by
  let pull : Euclidean (d+1) × (Euclidean 3 × Euclidean d) →
      Euclidean (d+1) × (Euclidean 3 × Euclidean d) :=
    fun q ↦ ((CompatibleResponse.primaryCoordinateChange i).symm q.1, q.2)
  have hpull : Continuous pull :=
    ((CompatibleResponse.primaryCoordinateChange i).symm.continuous.comp continuous_fst).prodMk continuous_snd
  have hphysical := ResponseTransfer.RetainedFactors.isCompact_closure_retained_physicalBox z (2*ε)
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hphysical
  have hJ := (hphysical.prod hA).image hpull
  obtain ⟨sourceLower, sourceUpper, δ, hLo, hHi, hδ, hδT, hband⟩ :=
    ResponsePrimarySources.exists_fullPhase_differential_bounds T hJ (by
      rintro _ ⟨q, hq, rfl⟩
      exact hprimary q hq)
  refine ⟨sourceLower, sourceUpper, δ, hLo, hHi, hδ, hδT, ?_⟩
  intro Q hQ q hq
  have he : ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1‖ =
      ‖fderiv ℝ (fun y ↦ phase T Q y q.2.2) ((CompatibleResponse.primaryCoordinateChange i).symm q.1)‖ := by
    rw [← (InnerProductSpace.toDual ℝ (Euclidean (d+1))).symm.norm_map]
    change ‖gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1‖ = _
    rw [T.fullSourcePhaseInCoordinates_gradient i Q (hprimary q hq),
      ResponseTransfer.RetainedFactors.norm_primaryCoordinateChange]
    exact (InnerProductSpace.toDual ℝ (Euclidean (d+1))).symm.norm_map _
  rw [he]
  exact hband Q hQ (pull q) (mem_image_of_mem pull hq)

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily

namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open CompatibleResponse ActualCarriers KernelIdentification
variable {d : ℕ}

/-- The actual sector direction has a positive closed angular neighborhood
in the smaller envelope cone. This radius is imposed before finite masks are
chosen, preserving the literal physical-coordinate pullback
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_pulledback_inner_cone_radius
    (i : Fin (d + 1)) (ξ : Euclidean (d + 1)) (hξ : ξ ≠ 0)
    (ℓ : Euclidean d →L[ℝ] ℝ) (hℓ : ℓ (coordinateSplit i ξ).2 = 1)
    {ε aperture : ℝ} (hε : 0 < ε) (hApξ : |ξ i| < aperture / 2) :
    ∃ α > (0 : ℝ), closedBall (NormedSpace.normalize ξ) α ⊆
      primaryCoordinateChange i ⁻¹'
        fullAngularCone ℓ (coordinateSplit i ξ).2 (ε / 4) (aperture / 2) := by
  let V := primaryCoordinateChange i ⁻¹'
    fullAngularCone ℓ (coordinateSplit i ξ).2 (ε / 4) (aperture / 2)
  have hV : IsOpen V := (isOpen_fullAngularCone ..).preimage
    (primaryCoordinateChange i).continuous
  have hcenter : primaryCoordinateChange i ξ ∈
      fullAngularCone ℓ (coordinateSplit i ξ).2 (ε / 4) (aperture / 2) := by
    refine ⟨?_, ?_⟩
    · change 0 < ℓ (coordinateSplit i ξ).2 ∧
        (ℓ (coordinateSplit i ξ).2)⁻¹ • (coordinateSplit i ξ).2 ∈
          ball (coordinateSplit i ξ).2 (ε / 4)
      rw [hℓ]
      simpa only [inv_one, one_smul] using
        And.intro zero_lt_one (mem_ball_self (by positivity : 0 < ε / 4))
    · simpa only [primaryCoordinateChange_apply, timeSpacePoint_time,
        spatialPart_timeSpacePoint, hℓ, mul_one] using hApξ
  have hn : NormedSpace.normalize ξ ∈ V := by
    have hs := smul_mem_fullAngularCone (inv_pos.mpr (norm_pos_iff.mpr hξ)) hcenter
    simpa only [V, mem_preimage, NormedSpace.normalize, map_smul] using hs
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV _ hn
  exact ⟨r/2, half_pos hr,
    (closedBall_subset_ball (half_lt_self hr)).trans hball⟩

/-- The selector's explicit gap is monotone in its lower source radius;
all geometric denominators are the SAME retained ones
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retainedSelectorGap_mono_source_radius (η₀ : Euclidean d)
    {ε aperture a₁ a₂ : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (ha : a₁ ≤ a₂) :
    retainedSelectorGap η₀ ε aperture a₁ ≤ retainedSelectorGap η₀ ε aperture a₂ := by
  unfold retainedSelectorGap
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right ha (by norm_num))
      (by positivity)) (by norm_num)

/-- Construct the prescribed annulus from the actual frozen source bounds
and the original elapsed-gradient comparison constants. Both the original
annulus and every center's full selector shoulders are retained; the constants
precede the stationary domain, reference and histories
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_full_source_envelope_annulus (η₀ : Euclidean d)
    {ε aperture gap radius normLo normHi gradientLower gradientUpper : ℝ}
    (hε : 0 < ε) (hAp : 0 < aperture) (hgap : 0 < gap)
    (hlo : 0 < normLo) (hhi : 0 < normHi)
    (hgradLo : 0 < gradientLower) (hgradHi : 0 < gradientUpper) :
    ∃ envelopeGap > (0 : ℝ), ∃ envelopeRadius > (0 : ℝ),
      envelopeGap ≤ gap ∧ radius ≤ envelopeRadius ∧
      ∀ normSource : ℝ, normLo ≤ normSource → normSource ≤ normHi →
        envelopeGap ≤ retainedSelectorGap η₀ (ε / 2) aperture
          ((normSource / 2) / (2 * gradientUpper)) ∧
        4 * (2 * normSource) / gradientLower ≤ envelopeRadius := by
  let selGap := retainedSelectorGap η₀ (ε / 2) aperture
    ((normLo / 2) / (2 * gradientUpper))
  have hselGap : 0 < selGap := retainedSelectorGap_pos η₀ (half_pos hε) hAp
    (div_pos (half_pos hlo) (mul_pos (by norm_num) hgradHi))
  let rad := max radius (4 * (2 * normHi) / gradientLower)
  have hrad : 0 < rad := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨min gap selGap, lt_min hgap hselGap, rad, hrad,
    min_le_left _ _, le_max_left _ _, ?_⟩
  intro normSource hlow hupp
  refine ⟨(min_le_right _ _).trans ?_, ?_⟩
  · exact retainedSelectorGap_mono_source_radius η₀ (half_pos hε) hAp
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hlow (by norm_num))
        (by positivity))
  · exact (div_le_div_of_nonneg_right (by linarith) hgradLo.le).trans
      (le_max_right _ _)

/-- Choose an actual common radial band for every stationary source annulus
of one selected chart. The original amplitude constructor must use this band
when invoking its raw symbol-budget producer; no budget on a different band is
transferred. Consumer: `exists_selected_fullSource_annular_history_profiles`,
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_retained_envelope_amplitude_band {ι : Type*} [Finite ι]
    (ℓ : Euclidean d →L[ℝ] ℝ) (g Rad : ι → ℝ)
    (hg : ∀ j, 0 < g j) :
    ∃ ra > (0 : ℝ), ∃ rb > ra, ∀ j,
      ra ≤ g j / 2 ∧ g j + 1 + (1 + ‖ℓ‖) * Rad j ≤ rb := by
  obtain ⟨ra, hra, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : ι ↦ (0 : ℝ)) (y := fun j ↦ g j / 2) (fun j ↦ half_pos (hg j))
  obtain ⟨upper, hupper⟩ := Finite.exists_le (fun j ↦ g j + 1 + (1 + ‖ℓ‖) * Rad j)
  refine ⟨ra, hra, max (ra + 1) upper, ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · intro j
    exact ⟨by simpa using (hsmall j).le, (hupper j).trans (le_max_right _ _)⟩

end JanetCartan.ResponseTransfer.RetainedFactors
