module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.AnnularInput
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff.Multiplier

/-!
# Literal selector supports on a supplied selected stationary domain

The original doubled physical multiplier is retained. Its proved support
nesting supplies the canonical cone argument, without identifying the two
multipliers. The two numerical annulus comparisons below are exactly what the
selected stationary constructor must provide on its own returned family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RegularSector.Characteristic ConicPhase ResidualCoordinates EvolutionIntegral SymbolBudgets
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RetainedFactors FullSourceEnvelopes DirectEvolution AnnularSobolev AnnularComplement
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
  {A₀ : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d+1)

/-- Both radial shoulders of the literal selected multiplier fit the SAME
stationary frequency domain once its original fixed annulus covers the
selector's computed radial bounds. The original `gap/radius` containment is
provided by `ProtectedConstruction.FullSource`; the two comparisons are the
remaining producer obligation for `app:ch_response:eq:direct-envelope-profile`.
No alternative finite family or stationary domain is chosen. -/
theorem selected_physical_selector_frequency_mem
    (f : ActualMaskFamily Ω x RQ A₀ K₀ M) (p : f.centers)
    (z : RootState (Euclidean d)) {ε aperture a b gap radius : ℝ}
    (hε : 0 < ε) (hAp : 0 < aperture) (ha : 0 < a) (hb : 0 < b)
    (hcone : tsupport (f.angularMask p ∘ physicalCoordinates (f.chart p).index) ∩
      sphere (0 : E) 1 ⊆ fullAngularCone (f.chart p).radialSection z.2.2
        (ε/4) (aperture/2))
    {O : Set E}
    (hbase : retainedAnnularFrequencyCarrier (f.chart p).radialSection z.2.2
      (ε/2) aperture gap radius ⊆ O)
    (hgap : gap ≤ retainedSelectorGap z.2.2 (ε/2) aperture a)
    (hradius : 2*b ≤ radius)
    {threshold lam : ℝ} (hthreshold : 0 < threshold) (hlam : 0 < lam)
    {θ : E} (hβ : lam • θ ∈ tsupport (selectedEndpointMultiplier f p threshold))
    (hπ : θ ∈ tsupport (fun ξ ↦ (annularSelector a b ha hb ξ : ℂ))) :
    θ ∈ O := by
  have hcanonical := RegularSector.FiniteEvolution.PhysicalCutoff.tsupport_complex_physical_dilatedConicMask_subset
      (f.angularMask p) (f.chart p).index hthreshold hβ
  have hfreq := retained_selector_frequency_mem (f.chart p).radialSection z.2.2
    (half_pos hε) hAp ha hb (f.angularMask p ∘ physicalCoordinates (f.chart p).index)
    (by simpa only [div_div, show (2 : ℝ)*2=4 by norm_num] using hcone)
    hthreshold hlam hcanonical hπ
  exact hbase (retainedAnnularFrequencyCarrier_mono (f.chart p).radialSection
    z.2.2 (ε/2) aperture hgap hradius hfreq)

/-- The original physical masks, both radial shoulders and doubled threshold
remain on the SAME full-source critical carrier in both literal orientations.
This discharges the support deduction from the fixed annulus comparisons of
`selected_physical_selector_frequency_mem`; those comparisons still need to
hold for the actual selected stationary producer
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem selected_physical_annular_support
    (f : ActualMaskFamily Ω x RQ A₀ K₀ M) (p : f.centers)
    (z : RootState (Euclidean d)) {ε aperture a b gap radius : ℝ}
    (hε : 0 < ε) (hAp : 0 < aperture) (ha : 0 < a) (hb : 0 < b)
    (hcone : tsupport (f.angularMask p ∘ physicalCoordinates (f.chart p).index) ∩
      sphere (0 : E) 1 ⊆ fullAngularCone (f.chart p).radialSection z.2.2
        (ε/4) (aperture/2))
    {O : Set E}
    (hbase : retainedAnnularFrequencyCarrier (f.chart p).radialSection z.2.2
      (ε/2) aperture gap radius ⊆ O)
    (hgap : gap ≤ retainedSelectorGap z.2.2 (ε/2) aperture a)
    (hradius : 2*b ≤ radius)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (output : E → ℝ) (hout : ContDiff ℝ ∞ output)
    (hphysical : tsupport (endpointOutputMask f p output) ∪ tsupport (chartInputMask f p) ⊆
      elapsedPhysicalBox z (ε/2))
    {threshold lam : ℝ} (hthreshold : 0 < threshold) (hlam : 0 < lam)
    (t : ℝ) (o : ℕ) (adj : Bool) :
    let β := selectedEndpointMultiplier f p threshold
    let π : E → ℂ := fun ξ ↦ annularSelector a b ha hb ξ
    let X := tsupport (endpointOutputMask f p output) ∪ tsupport (chartInputMask f p)
    ∀ v ∈ tsupport (Function.uncurry (orientedAnnularAmplitude Par adj W
      (endpointOutputMask f p output) (chartInputMask f p) β π t lam (-(o : ℤ)))),
      v.1.1 ∈ X ∧ v.2.fst ∈ X ∧ v.2 ∈ retainedOpenIntegrationDomain z ε O ∧
        ‖v.2.snd‖ ≤ 2*b ∧ lam • v.2.snd ∈ tsupport β := by
  intro β π X v hv
  have ho : ContDiff ℝ ∞ (endpointOutputMask f p output) :=
    Complex.ofRealCLM.contDiff.comp (hout.comp (physicalCoordinates (f.chart p).index).contDiff)
  have hs := (chartPhysicalMasks_properties f p).2.1
  have hβ := (selectedEndpointMultiplier_bounds f p threshold).1
  have hπ : ContDiff ℝ ∞ π := Complex.ofRealCLM.contDiff.comp (contDiff_annularSelector ..)
  have hproj := fullSource_annularAmplitude_jets_support adj W
    (endpointOutputMask f p output) (chartInputMask f p) β π hW ho hs hβ hπ t hlam.ne' o
  rw [hproj.2.1] at hv
  let w : (E × Euclidean 3) × CW := ((v.1.1,v.1.2.1),v.2)
  have hparts : v.1.1 ∈ X ∧ v.2.fst ∈ X ∧
      lam • v.2.snd ∈ tsupport β ∧ v.2.snd ∈ tsupport π := by
    cases adj
    · have h := tsupport_normalizedAnnularElapsedAmplitude_subset W
        (endpointOutputMask f p output) (chartInputMask f p) β π t hlam.ne' (-(o : ℤ))
        (show w ∈ _ from hv)
      exact ⟨Or.inl h.1,Or.inr h.2.1,h.2.2⟩
    · have h := tsupport_normalizedAdjointAnnularElapsedAmplitude_subset W
        (endpointOutputMask f p output) (chartInputMask f p) β π t hlam.ne' (-(o : ℤ))
        (show w ∈ _ from hv)
      exact ⟨Or.inr h.1,Or.inl h.2.1,h.2.2⟩
  have hfreq := selected_physical_selector_frequency_mem f p z hε hAp ha hb
    hcone hbase hgap hradius hthreshold hlam hparts.2.2.1 hparts.2.2.2
  have hpos := hphysical hparts.2.1
  have hrad := tsupport_annularSelector_subset a b ha hb
    (tsupport_comp_subset Complex.ofReal_zero _ hparts.2.2.2)
  refine ⟨hparts.1,hparts.2.1,?_,hrad.2,hparts.2.2.1⟩
  exact ⟨⟨ball_subset_ball (by linarith : ε/2 ≤ ε) hpos.1,
    ball_subset_ball (by linarith : ε/2 ≤ ε) hpos.2⟩,hfreq⟩

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
