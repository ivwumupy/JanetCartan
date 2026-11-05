module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.ClosedCarriers
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.Selector
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.DilatedShellCover

/-!
# Convex carriers for the entire retained annular support

The direct envelope selector keeps a full radial interval. A ball around one
central covector does not contain that interval. Here a closed convex cone
section contains the actual dilated multiplier and both selector shoulders,
has a positive spatial-frequency gap, and normalizes into the original chart.
Consumer: the supported segments in `HistoryElapsedHessian` and the primitive
domains of `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open DirectEvolution AnnularComplement RegularSector.FiniteMasks
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- A bounded convex section of the retained cone, with a linear radial
collar. Unlike a spherical annulus its segments stay away from zero
(`app:ch_response:eq:direct-envelope-profile`). -/
def retainedAnnularFrequencyCarrier (ℓ : Euclidean d →L[ℝ] ℝ)
    (η₀ : Euclidean d) (ε aperture gap radius : ℝ) : Set E :=
  closedBall 0 radius ∩ closure (fullAngularCone ℓ η₀ (ε / 2) (aperture / 2) ∩
    {θ | gap < ℓ (spatialPart θ)})

/-- The full radial carrier is compact and convex, including its shoulders
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedAnnularFrequencyCarrier_compact_convex
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    (ε aperture gap radius : ℝ) :
    IsCompact (retainedAnnularFrequencyCarrier ℓ η₀ ε aperture gap radius) ∧
      Convex ℝ (retainedAnnularFrequencyCarrier ℓ η₀ ε aperture gap radius) := by
  refine ⟨(isCompact_closedBall (0 : E) radius).inter_right isClosed_closure, ?_⟩
  exact (convex_closedBall (0 : E) radius).inter
    (((convex_fullAngularCone ℓ η₀ (ε / 2) (aperture / 2)).inter
      ((convex_Ioi gap).linear_preimage (ℓ.comp spatialPartCLM).toLinearMap)).closure)

/-- Every point of the closed carrier remains in the original outer cone
and has a quantitative spatial radial gap. Thus every convex segment has the
same conic normalization, not merely its two endpoints
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedAnnularFrequencyCarrier_geometry
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    {ε aperture gap radius : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < gap)
    {θ : E} (hθ : θ ∈ retainedAnnularFrequencyCarrier ℓ η₀ ε aperture gap radius) :
    θ ∈ fullAngularCone ℓ η₀ ε aperture ∧
      gap / (1 + ‖ℓ‖) ≤ ‖spatialPart θ‖ ∧ ‖θ‖ ≤ radius := by
  have hden : 0 < 1 + ‖ℓ‖ := by positivity
  have hsub : fullAngularCone ℓ η₀ (ε / 2) (aperture / 2) ∩
      {θ : E | gap < ℓ (spatialPart θ)} ⊆
      fullAngularCone ℓ η₀ (ε / 2) (aperture / 2) ∩
        {θ : E | gap / (1 + ‖ℓ‖) < ‖spatialPart θ‖} := by
    intro v hv
    refine ⟨hv.1, (div_lt_iff₀ hden).mpr ?_⟩
    have hn := (le_abs_self (ℓ (spatialPart v))).trans (ℓ.le_opNorm (spatialPart v))
    have hv' : gap < ℓ (spatialPart v) := hv.2
    nlinarith only [hv', hn, norm_nonneg (spatialPart v)]
  have hcone := closure_fullAngularCone_collar_subset ℓ hε hAp (div_pos hg hden)
    (closure_mono hsub hθ.2)
  have hrad : gap ≤ ℓ (spatialPart θ) :=
    closure_minimal (fun _ hv ↦ hv.2.le)
      (isClosed_le continuous_const (ℓ.continuous.comp spatialPartCLM.continuous)) hθ.2
  have hn := (le_abs_self (ℓ (spatialPart θ))).trans (ℓ.le_opNorm (spatialPart θ))
  refine ⟨hcone, (div_le_iff₀ hden).mpr ?_, ?_⟩
  · nlinarith only [hrad, hn, norm_nonneg (spatialPart θ)]
  · simpa only [mem_closedBall, dist_zero_right] using hθ.1

/-- The actual right multiplier retains the full conic support under its
fixed radial dilation. This identifies the producer's sphere-support premise
with the cone used below (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem dilatedConicMask_tsupport_subset_fullAngularCone
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (ε aperture : ℝ)
    (mask : E → ℝ)
    (hm : tsupport mask ∩ sphere (0 : E) 1 ⊆ fullAngularCone ℓ η₀ ε aperture)
    {threshold : ℝ} (ht : 0 < threshold) :
    tsupport (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)) ⊆
      fullAngularCone ℓ η₀ ε aperture := by
  intro ξ hξ
  have hs := dilatedConicMask_tsupport_subset mask ht
    (tsupport_comp_subset Complex.ofReal_zero _ hξ)
  have hn : ξ ≠ 0 := norm_pos_iff.mp (ht.trans_le hs.1)
  have hc := hm ⟨hs.2, by simpa only [mem_sphere, dist_zero_right] using
    NormedSpace.norm_normalize hn⟩
  simpa only [NormedSpace.norm_smul_normalize] using
    smul_mem_fullAngularCone (norm_pos_iff.mpr hn) hc

/-- One compact convex frequency carrier contains the literal annular
amplitude for every positive frequency, elapsed time, matrix order and pair
of physical masks. Its constants precede those varying labels. Both radial
shoulders and the original dilated multiplier are retained; no datum or
operator is projected (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_retained_annular_frequency_carrier
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    {ε aperture a b : ℝ} (hε : 0 < ε) (hAp : 0 < aperture)
    (ha : 0 < a) (hb : 0 < b)
    (mask : E → ℝ)
    (hm : tsupport mask ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ η₀ (ε / 2) (aperture / 2)) :
    ∃ D : Set E, IsCompact D ∧ Convex ℝ D ∧ ∃ gap > (0 : ℝ),
      (∀ θ ∈ D, θ ∈ fullAngularCone ℓ η₀ ε aperture ∧
        gap ≤ ‖spatialPart θ‖ ∧ ‖θ‖ ≤ 2 * b) ∧
      ∀ threshold > (0 : ℝ), ∀ (r : ℕ) (A : TwoTimeAmplitude d r)
        (χout χsource : E → ℂ) (t lam : ℝ), 0 < lam → ∀ order : ℤ,
        ∀ v ∈ tsupport (Function.uncurry (AnnularSobolev.normalizedAnnularElapsedAmplitude
          (P := Euclidean 3) A χout χsource
          (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ))
          (fun θ ↦ (annularSelector a b ha hb θ : ℂ)) t lam order)), v.2.snd ∈ D := by
  let den := 1 + aperture / 2 + ‖η₀‖ + ε / 2
  have hd : 0 < den := by dsimp [den]; positivity
  let g := (a / 4 / den) / 2
  have hg : 0 < g := by dsimp [g]; positivity
  let D := retainedAnnularFrequencyCarrier ℓ η₀ ε aperture g (2 * b)
  obtain ⟨hc, hconv⟩ := retainedAnnularFrequencyCarrier_compact_convex ℓ η₀ ε aperture g (2 * b)
  refine ⟨D, hc, hconv, g / (1 + ‖ℓ‖), by positivity,
    fun _ hθ ↦ retainedAnnularFrequencyCarrier_geometry ℓ η₀ hε hAp hg hθ, ?_⟩
  intro threshold ht r A χout χsource t lam hlam order v hv
  have hs := tsupport_normalizedAnnularElapsedAmplitude_subset A χout χsource
    (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ))
    (fun θ ↦ (annularSelector a b ha hb θ : ℂ)) t hlam.ne' order hv
  have hcone := dilatedConicMask_tsupport_subset_fullAngularCone ℓ η₀
    (ε / 2) (aperture / 2) mask hm ht hs.2.2.1
  have hr := tsupport_annularSelector_subset a b ha hb
    (tsupport_comp_subset Complex.ofReal_zero _ hs.2.2.2)
  have hband := normalizedSourceBand_mem_radialSectionBand ℓ (half_pos hε).le
    (half_pos hAp).le (show 0 < a / 4 by positivity) hlam
    (ξ := v.2.snd) (b := 3 * b) ⟨hcone, by linarith [hr.1], by linarith [hr.2]⟩
  have hrad : a / 4 / den ≤ ℓ (spatialPart v.2.snd) := by
    obtain ⟨⟨s, η⟩, ⟨hlo, _, he⟩, hη⟩ := hband
    rw [← hη, map_smul, smul_eq_mul, he, mul_one]
    exact hlo.1
  refine ⟨by simpa only [mem_closedBall, dist_zero_right] using hr.2,
    subset_closure ⟨?_, ?_⟩⟩
  · simpa only [inv_smul_smul₀ hlam.ne'] using
      smul_mem_fullAngularCone (inv_pos.mpr hlam) hcone
  · change g < _
    dsimp [g]
    linarith [show 0 < a / 4 / den by positivity]

end JanetCartan.ResponseTransfer.RetainedFactors
