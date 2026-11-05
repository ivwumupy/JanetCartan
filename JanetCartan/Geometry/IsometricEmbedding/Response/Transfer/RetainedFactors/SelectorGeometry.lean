module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AnnularCarriers
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AdjointAmplitudeJets

/-!
# The exact integrated-envelope selector on the retained carrier

Choose the closed annulus before the critical radius and source masks. The
selector has the radii prescribed by `IntegratedEnvelope.Assembly`, rather
than independently selected radii. Both shoulders and the literal adjoint's
exchanged physical positions remain in the same carrier. Consumer:
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral DirectEvolution
open AnnularComplement AnnularSobolev RegularSector.FiniteMasks
variable {d p q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean p
local notation "Joint" => (E × Par) × CarrierVariables (d + 1)

/-- Enlarge only the proof carrier, retaining its cone and every original
frequency (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedAnnularFrequencyCarrier_mono
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (ε aperture : ℝ)
    {g₁ g₂ R₁ R₂ : ℝ} (hg : g₂ ≤ g₁) (hR : R₁ ≤ R₂) :
    retainedAnnularFrequencyCarrier ℓ η₀ ε aperture g₁ R₁ ⊆
      retainedAnnularFrequencyCarrier ℓ η₀ ε aperture g₂ R₂ := by
  intro θ hθ
  refine ⟨closedBall_subset_closedBall hR hθ.1, ?_⟩
  apply closure_mono _ hθ.2
  intro v hv
  exact ⟨hv.1, hg.trans_lt hv.2⟩

/-- Explicit linear radial gap of the full selector, before the source cap
is selected (`app:ch_response:eq:direct-envelope-profile`). -/
def retainedSelectorGap (η₀ : Euclidean d) (ε aperture a : ℝ) : ℝ :=
  (a / 4 / (1 + aperture / 2 + ‖η₀‖ + ε / 2)) / 2

/-- Positivity of the actual fixed selector gap. -/
theorem retainedSelectorGap_pos (η₀ : Euclidean d) {ε aperture a : ℝ}
    (hε : 0 < ε) (hAp : 0 < aperture) (ha : 0 < a) :
    0 < retainedSelectorGap η₀ ε aperture a := by
  unfold retainedSelectorGap
  positivity

/-- Both full radial shoulders of the selected multiplier lie in this
explicit closed carrier. This fixes the annulus before any chart, amplitude,
history or frequency is varied (`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_selector_frequency_mem
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d)
    {ε aperture a b : ℝ} (hε : 0 < ε) (hAp : 0 < aperture)
    (ha : 0 < a) (hb : 0 < b) (mask : E → ℝ)
    (hm : tsupport mask ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ η₀ (ε / 2) (aperture / 2))
    {threshold lam : ℝ} (ht : 0 < threshold) (hlam : 0 < lam)
    {θ : E}
    (hβ : lam • θ ∈ tsupport (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)))
    (hπ : θ ∈ tsupport (fun ξ ↦ (annularSelector a b ha hb ξ : ℂ))) :
    θ ∈ retainedAnnularFrequencyCarrier ℓ η₀ ε aperture
      (retainedSelectorGap η₀ ε aperture a) (2 * b) := by
  let den := 1 + aperture / 2 + ‖η₀‖ + ε / 2
  have hd : 0 < den := by dsimp [den]; positivity
  have hcone := dilatedConicMask_tsupport_subset_fullAngularCone ℓ η₀
    (ε / 2) (aperture / 2) mask hm ht hβ
  have hr := tsupport_annularSelector_subset a b ha hb
    (tsupport_comp_subset Complex.ofReal_zero _ hπ)
  have hband := normalizedSourceBand_mem_radialSectionBand ℓ (half_pos hε).le
    (half_pos hAp).le (show 0 < a / 4 by positivity) hlam
    (ξ := θ) (b := 3 * b) ⟨hcone, by linarith [hr.1], by linarith [hr.2]⟩
  have hrad : a / 4 / den ≤ ℓ (spatialPart θ) := by
    obtain ⟨⟨s, η⟩, ⟨hlo, _, he⟩, hη⟩ := hband
    rw [← hη, map_smul, smul_eq_mul, he, mul_one]
    exact hlo.1
  refine ⟨by simpa only [mem_closedBall, dist_zero_right] using hr.2,
    subset_closure ⟨?_, ?_⟩⟩
  · simpa only [inv_smul_smul₀ hlam.ne'] using
      smul_mem_fullAngularCone (inv_pos.mpr hlam) hcone
  · change (a / 4 / den) / 2 < _
    linarith [show 0 < a / 4 / den by positivity]

/-- The literal adjoint's support is the forward support with its two
physical positions exchanged. All complex masks retain conjugate order
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem tsupport_normalizedAdjointAnnularElapsedAmplitude_subset
    (A : TwoTimeAmplitude d q) (χout χsource β π : E → ℂ)
    (t : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (order : ℤ)
    {v : Joint} (hv : v ∈ tsupport (Function.uncurry
      (normalizedAdjointAnnularElapsedAmplitude (P := Par) A χout χsource β π t lam order))) :
    v.1.1 ∈ tsupport χsource ∧ v.2.fst ∈ tsupport χout ∧
      lam • v.2.snd ∈ tsupport β ∧ v.2.snd ∈ tsupport π := by
  let f := Function.uncurry
    (normalizedAnnularElapsedAmplitude (P := Par) A χout χsource β π t lam order)
  have he : Function.uncurry
      (normalizedAdjointAnnularElapsedAmplitude (P := Par) A χout χsource β π t lam order) =
      (fun M => M.conjTranspose) ∘ (f ∘ annularCarrierSwap) := by
    funext w
    change (lam ^ order)⁻¹ •
      (annularElapsedAmplitude A χout χsource β π t lam w.2.fst w.1.1
        (lam • w.2.snd)).conjTranspose =
      ((lam ^ order)⁻¹ • annularElapsedAmplitude A χout χsource β π t lam
        w.2.fst w.1.1 (lam • w.2.snd)).conjTranspose
    simp only [Matrix.conjTranspose_smul, star_trivial]
  rw [he] at hv
  have hv' := tsupport_comp_subset (g := fun M : Matrix (Fin q) (Fin q) ℂ => M.conjTranspose)
    Matrix.conjTranspose_zero (f ∘ annularCarrierSwap) hv
  have hv'' := tsupport_comp_subset_preimage f annularCarrierSwap.continuous hv'
  have hs := tsupport_normalizedAnnularElapsedAmplitude_subset A χout χsource β π t hlam order hv''
  exact ⟨hs.2.1, hs.1, hs.2.2⟩

/-- The exact selector in both orientations fits the SAME critical domain.
The complete topological support retains both physical masks, the high-pass
multiplier and its full radial shoulders. This discharges the support and
frequency-radius inputs of both integrated-envelope endpoints
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_selector_support_in_critical_domain
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε aperture a b : ℝ} (hε : 0 < ε) (hAp : 0 < aperture)
    (ha : 0 < a) (hb : 0 < b) (mask : E → ℝ)
    (hm : tsupport mask ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ z.2.2 (ε / 4) (aperture / 2))
    {O : Set E}
    (hcarrier : retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture
      (retainedSelectorGap z.2.2 (ε / 2) aperture a) (2 * b) ⊆ O)
    (A : TwoTimeAmplitude d q) (χout χsource : E → ℂ)
    (ho : tsupport χout ⊆ elapsedPhysicalBox z (ε / 2))
    (hs : tsupport χsource ⊆ elapsedPhysicalBox z (ε / 2))
    {threshold lam : ℝ} (ht : 0 < threshold) (hlam : 0 < lam)
    (t : ℝ) (order : ℤ) (adj : Bool) :
    let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)
    let π : E → ℂ := fun ξ ↦ (annularSelector a b ha hb ξ : ℂ)
    let α := if adj then normalizedAdjointAnnularElapsedAmplitude (P := Par)
      A χout χsource β π t lam order else normalizedAnnularElapsedAmplitude (P := Par)
      A χout χsource β π t lam order
    ∀ v ∈ tsupport (Function.uncurry α),
      v.1.1 ∈ tsupport χout ∪ tsupport χsource ∧
      v.2.fst ∈ tsupport χout ∪ tsupport χsource ∧
      v.2 ∈ retainedOpenIntegrationDomain z ε O ∧
      ‖v.2.snd‖ ≤ 2 * b ∧ lam • v.2.snd ∈ tsupport β := by
  intro β π α v hv
  have hboth : v.1.1 ∈ tsupport χout ∪ tsupport χsource ∧
      v.2.fst ∈ tsupport χout ∪ tsupport χsource ∧
      lam • v.2.snd ∈ tsupport β ∧ v.2.snd ∈ tsupport π := by
    cases adj
    · have hh := tsupport_normalizedAnnularElapsedAmplitude_subset A χout χsource β π
        t hlam.ne' order hv
      exact ⟨Or.inl hh.1, Or.inr hh.2.1, hh.2.2⟩
    · have hh := tsupport_normalizedAdjointAnnularElapsedAmplitude_subset A χout χsource β π
        t hlam.ne' order hv
      exact ⟨Or.inr hh.1, Or.inl hh.2.1, hh.2.2⟩
  have hfreq := retained_selector_frequency_mem ℓ z.2.2 (half_pos hε) hAp ha hb mask
    (by simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hm) ht hlam hboth.2.2.1 hboth.2.2.2
  have hphys : v.2.fst ∈ elapsedPhysicalBox z (ε / 2) := hboth.2.1.elim (fun h ↦ ho h) (fun h ↦ hs h)
  refine ⟨hboth.1, hboth.2.1, ?_, ?_, hboth.2.2.1⟩
  · exact ⟨⟨ball_subset_ball (by linarith : ε / 2 ≤ ε) hphys.1,
      ball_subset_ball (by linarith : ε / 2 ≤ ε) hphys.2⟩, hcarrier hfreq⟩
  · simpa only [retainedAnnularFrequencyCarrier, mem_inter_iff,
      mem_closedBall, dist_zero_right] using hfreq.1

end JanetCartan.ResponseTransfer.RetainedFactors
