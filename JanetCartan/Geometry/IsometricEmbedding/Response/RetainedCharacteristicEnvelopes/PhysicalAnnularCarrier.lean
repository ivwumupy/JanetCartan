module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SelectorGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.Carrier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.DiagonalBuffers.Geometry

/-!
# The literal physical multiplier on the compact annular carrier

The selected multiplier keeps its coordinate permutation inside the radial
cutoff at `2*threshold`. Its closed-support nesting in the canonical cutoff
proves containment of both selector shoulders. The resulting carrier and
radial identity feed the full-source envelope on the same stationary domain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral UniformEvolution ResidualCoordinates
open DirectEvolution AnnularSobolev AnnularComplement RegularSector.FiniteMasks
variable {d p : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean p
local notation "CW" => CarrierVariables (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "TC" => TwoTimePoint (Euclidean d)

/-- Construct the actual annular integration carrier for the literal doubled
physical multiplier. The permutation is retained inside the cutoff; only the
proved closed-support inclusion is used. Both orientations, physical masks,
radial shoulders and the fixed stationary domain remain unchanged. The annulus
comparison is the numerical input of the original finite selector, and must
be instantiated on its SAME returned chart
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_physical_capped_annular_integration_carrier (index : Fin (d + 1))
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z)
    {ε aperture a b g Rad δ : ℝ} (hε : 0 < ε) (hAp : 0 < aperture)
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) (hδg : δ ≤ g / (1 + ‖ℓ‖))
    (hcarrier : retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture
      (retainedSelectorGap z.2.2 (ε / 2) aperture a) (2 * b) ⊆
        retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad)
    (χout χsource : E → ℂ)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (ho : tsupport χout ⊆ elapsedPhysicalBox z (ε / 2))
    (hs : tsupport χsource ⊆ elapsedPhysicalBox z (ε / 2)) :
    let Dcrit := retainedOpenIntegrationDomain z ε
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad)
    let X₀ := tsupport χout ∪ tsupport χsource
    let π : E → ℂ := fun θ ↦ (annularSelector a b ha hb θ : ℂ)
    ∃ Kcrit : Set CW, IsCompact Kcrit ∧ Kcrit ⊆ Dcrit ∧
      ∀ (mask : E → ℝ),
        tsupport (mask ∘ physicalCoordinates index) ∩ sphere (0 : E) 1 ⊆
          fullAngularCone ℓ z.2.2 (ε / 4) (aperture / 2) →
      ∀ threshold > (0 : ℝ), ∀ lam : ℝ, 1 ≤ lam →
        let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask (2 * threshold) (physicalCoordinates index ξ) : ℂ)
        let F₀ := SmoothRepresentative.retainedFrequencyCarrier δ (2 * b) lam β
        IsCompact F₀ ∧ (0 : E) ∉ F₀ ∧ F₀ ⊆ tsupport β ∧
        (∀ (χ F : TC → ℝ) t x θ, lam • θ ∈ F₀ →
          elapsedPhase (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ F) t x (lam • θ) =
            lam * elapsedPhase (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ F) t x θ) ∧
        ∀ (q : ℕ) (A : TwoTimeAmplitude d q) t (order : ℤ) (adj : Bool),
          let α := if adj then normalizedAdjointAnnularElapsedAmplitude (P := Par)
            A χout χsource β π t lam order else normalizedAnnularElapsedAmplitude (P := Par)
            A χout χsource β π t lam order
          (∀ v ∈ tsupport (Function.uncurry α),
            v.1.1 ∈ X₀ ∧ v.2 ∈ Kcrit ∧ v.2.fst ∈ X₀ ∧
              ‖v.2.snd‖ ≤ 2 * b ∧ lam • v.2.snd ∈ F₀) ∧
          ∀ u : E × Par, Function.support (α u) ⊆ Kcrit := by
  intro Dcrit X₀ π
  let Fsel := retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture
    (retainedSelectorGap z.2.2 (ε / 2) aperture a) (2 * b)
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let Kcrit := e ⁻¹' (X₀ ×ˢ Fsel)
  have hK : IsCompact Kcrit := by
    have he : Kcrit = e.symm '' (X₀ ×ˢ Fsel) := by
      ext w
      constructor
      · intro hw
        exact ⟨e w, hw, e.symm_apply_apply w⟩
      · rintro ⟨v, hv, rfl⟩
        simpa only [Kcrit, mem_preimage, e.apply_symm_apply] using hv
    rw [he]
    exact ((hoc.union hsc).prod
      (retainedAnnularFrequencyCarrier_compact_convex ℓ z.2.2 (ε / 2) aperture
        (retainedSelectorGap z.2.2 (ε / 2) aperture a) (2 * b)).1).image e.symm.continuous
  have hKD : Kcrit ⊆ Dcrit := by
    intro w hw
    have hx := hw.1.elim (fun h ↦ ho h) (fun h ↦ hs h)
    exact ⟨⟨ball_subset_ball (by linarith : ε / 2 ≤ ε) hx.1,
      ball_subset_ball (by linarith : ε / 2 ≤ ε) hx.2⟩, hcarrier hw.2⟩
  refine ⟨Kcrit, hK, hKD, ?_⟩
  intro mask hm threshold ht lam hlam β F₀
  have hl : 0 < lam := zero_lt_one.trans_le hlam
  refine ⟨SmoothRepresentative.isCompact_retainedFrequencyCarrier _ _ _ _,
    SmoothRepresentative.zero_notMem_retainedFrequencyCarrier hδ hlam _ _,
    fun _ hv ↦ hv.2,
    fun χ F t x θ hθ ↦ SmoothRepresentative.elapsed_representative_smul_on_retainedCarrier
      ℓ hδ χ F (2 * b) β hlam t x θ hθ, ?_⟩
  intro q A t order adj α
  have hsupport v (hv : v ∈ tsupport (Function.uncurry α)) :
      v.1.1 ∈ X₀ ∧ v.2 ∈ Kcrit ∧ v.2.fst ∈ X₀ ∧
        ‖v.2.snd‖ ≤ 2 * b ∧ lam • v.2.snd ∈ F₀ := by
    have hboth : v.1.1 ∈ X₀ ∧ v.2.fst ∈ X₀ ∧
        lam • v.2.snd ∈ tsupport β ∧ v.2.snd ∈ tsupport π := by
      cases adj
      · have hh := tsupport_normalizedAnnularElapsedAmplitude_subset
          A χout χsource β π t hl.ne' order hv
        exact ⟨Or.inl hh.1, Or.inr hh.2.1, hh.2.2⟩
      · have hh := tsupport_normalizedAdjointAnnularElapsedAmplitude_subset
          A χout χsource β π t hl.ne' order hv
        exact ⟨Or.inr hh.1, Or.inl hh.2.1, hh.2.2⟩
    have hcanonical := RegularSector.FiniteEvolution.PhysicalCutoff.tsupport_complex_physical_dilatedConicMask_subset
      mask index ht hboth.2.2.1
    have hfreq := retained_selector_frequency_mem ℓ z.2.2 (half_pos hε) hAp ha hb
      (mask ∘ physicalCoordinates index)
      (by simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hm)
      ht hl hcanonical hboth.2.2.2
    have hgap : g < ℓ (spatialPart v.2.snd) := (hcarrier hfreq).2.2
    have hspatial : δ ≤ ‖spatialPart v.2.snd‖ := by
      apply hδg.trans
      apply (div_le_iff₀ (by positivity : 0 < 1 + ‖ℓ‖)).mpr
      have hn := (le_abs_self (ℓ (spatialPart v.2.snd))).trans
        (ℓ.le_opNorm (spatialPart v.2.snd))
      nlinarith only [hgap, hn, norm_nonneg (spatialPart v.2.snd)]
    have hnorm : ‖v.2.snd‖ ≤ 2 * b := by
      simpa only [mem_closedBall, dist_zero_right] using hfreq.1
    exact ⟨hboth.1, ⟨hboth.2.1, hfreq⟩, hboth.2.1, hnorm,
      SmoothRepresentative.smul_mem_annularFrequencyCarrier hl.le hspatial hnorm, hboth.2.2.1⟩
  refine ⟨hsupport, ?_⟩
  intro u w hw
  exact (hsupport (u, w) (subset_tsupport _ hw)).2.1

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
