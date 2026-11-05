module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.Carriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SupportedCarriers.Domains
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.SourceAgreement.Collars

/-!
# Physical amplitude and phase carriers on the selected chart

The actual doubled multiplier supplies the spatial collar. Together with
the retained output box it places both elapsed time coordinates in the
original conic chart. Consumers: `hauxAmplitudeCarrier`, `hcarrier`, `hKV`
of `ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteResidual.SelectedChart RegularSector.FinitePdo
open Characteristic Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FiniteEvolution FiniteEvolution.PhysicalCutoff
open EvolutionLocalization EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.PhysicalShells
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)

/-- The SAME selected multiplier has a conic angular margin and a strict
spatial collar, including its entire closed support. The aperture is chosen
before the threshold. Its producers are the selected angular support and
spatial plateau in `ActualMaskFamily`; the cutoff remains at `2*threshold`
(`app:ch_regular:eq:high-amplitude`). -/
theorem exists_selectedEndpointMultiplier_retained_frequency_domain
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) :
    let c := f.chart p
    let e := coordinateSplit c.index
    let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
    ∃ aperture > (0 : ℝ), ∀ threshold, f.radialThreshold ≤ threshold →
      tsupport (selectedEndpointMultiplier f p threshold) ⊆
        retainedFrequencyDomain c.radialSection z
          (retainedRadius c.targetRadius c.bufferRadius) aperture (1/2) := by
  intro c e z
  obtain ⟨aperture, hAp, hcar⟩ := exists_chart_temporal_aperture c hρb hsrcρ
    (f.angularMask p) (f.angularMask_support p)
  refine ⟨aperture, hAp, ?_⟩
  intro threshold hthreshold ξ hξ
  have ht : 0 < threshold := (zero_lt_one.trans_le f.radialThreshold_ge_one).trans_le hthreshold
  have hcan := tsupport_complex_physical_dilatedConicMask_subset
    (f.angularMask p) c.index ht hξ
  have hr : ξ ∈ tsupport (dilatedConicMask
      (f.angularMask p ∘ physicalCoordinates c.index) threshold) :=
    tsupport_comp_subset Complex.ofReal_zero _ hcan
  refine ⟨dilatedConicMask_tsupport_subset_fullAngularCone c.radialSection z _ _ _ hcar ht hr, ?_⟩
  have he := (selectedEndpointMultiplier_spatialMask_plateau f p hthreshold hξ).eq_of_nhds
  have hn : conicMask (f.spatialMask p) (spatialPart ξ) ≠ 0 := by rw [he]; exact one_ne_zero
  have hb := (conicMask_tsupport_subset (f.spatialMask p) (subset_tsupport _ hn)).1
  change (1/2 : ℝ) < ‖spatialPart ξ‖
  linarith

/-- Construct the open physical phase domain, compact carriers for every
graph branch, and an open two-time amplitude domain on the original retained
chart. All choices precede the amplitude, scale, elapsed time, and shell.
The actual mask support discharges the physical amplitude carrier inclusion
even at source shoulders and for the contracting graph branch. No analytic
amplitude or phase estimate is an input (`app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_elapsed_physical_carriers
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius) :
    let c := f.chart p
    let e := coordinateSplit c.index
    let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
    let ε := retainedRadius c.targetRadius c.bufferRadius
    let Δ := 3 * c.maskRadius / 4
    ∃ Vphase : Set (E × E), ∃ Ua : Set (SymbolBudgets.TwoTimePoint d),
      IsOpen Vphase ∧ IsOpen Ua ∧
      Vphase ⊆ elapsedPhysicalBox z ε ×ˢ (spatialPart ⁻¹' angularCone c.radialSection z.2.2 ε) ∧
      Ua ⊆ bufferedBase z ε ×ˢ angularCone c.radialSection z.2.2 ε ∧
      (∀ w ∈ Ua, (1/2 : ℝ) < ‖w.2‖) ∧
      (∀ r ∈ Icc 0 Δ, ∀ w ∈ Vphase, elapsedPhasePoint r w ∈ Ua) ∧
      ∀ threshold, f.radialThreshold ≤ threshold →
        ∃ Kphase : Bool → ℕ → Set (E × E),
          (∀ low j, IsCompact (Kphase low j)) ∧
          (∀ low j, Kphase low j ⊆ Vphase) ∧
          (∀ r ∈ Icc 0 Δ, ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
            ∀ w ∈ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p),
              SymbolBudgets.elapsedPoint r (w, ξ) ∈ Ua) ∧
          ∀ (b : TwoTimeAmplitude d q) ρ, ρ ≠ 0 → ∀ r ∈ Icc 0 Δ,
            ∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
              ∀ w ∈ tsupport (fun w : E × E ↦ elapsedAmplitude b
                (endpointOutputMask f p output) (chartInputMask f p)
                (selectedEndpointMultiplier f p threshold) r w.1 w.2 (ρ • ξ)),
                (w.1, ρ • ξ) ∈ Kphase low j ∧
                  SymbolBudgets.elapsedPoint r (w, ρ • ξ) ∈ Ua := by
  intro c e z ε Δ
  let D := angularCone c.radialSection z.2.2 ε ∩ {η | (1/2 : ℝ) < ‖η‖}
  let Vphase := elapsedPhysicalBox z ε ×ˢ (spatialPart ⁻¹' D)
  let Ua := bufferedBase z ε ×ˢ D
  have hε : 0 < ε := (retainedRadius_bounds c.targetRadius_pos c.bufferRadius_pos).1
  have hΔε : Δ < ε := (UniformAmplitudes.retained_source_slab_bounds
    c.maskRadius_pos hρb hsrcρ).2
  have hD : IsOpen D := (isOpen_angularCone _ _ _).inter (isOpen_lt continuous_const continuous_norm)
  have hmap : ∀ r ∈ Icc 0 Δ, ∀ w ∈ Vphase, elapsedPhasePoint r w ∈ Ua := by
    intro r hr w hw
    exact ⟨elapsed_mem_bufferedBase hε ⟨hr.1, hr.2.trans hΔε.le⟩ hw.1, hw.2⟩
  have houtput : tsupport (endpointOutputMask f p output) ⊆ elapsedPhysicalBox z ε := by
    intro u hu
    have hb := (selected_output_retained_geometry f p hρb hsrcρ).1
      (endpointOutputMask_tsupport_subset_chartOutputMask f p output hout hu)
    exact ⟨ball_subset_ball (by dsimp [ε]; linarith) hb.1,
      ball_subset_ball (by dsimp [ε]; linarith) hb.2⟩
  refine ⟨Vphase, Ua, (isOpen_elapsedPhysicalBox _ _).prod
    (hD.preimage spatialPartCLM.continuous), isOpen_ball.prod hD,
    (fun _ hw ↦ ⟨hw.1, hw.2.1⟩), (fun _ hw ↦ ⟨hw.1, hw.2.1⟩),
    (fun _ hw ↦ hw.2.2), hmap, ?_⟩
  intro threshold hthreshold
  obtain ⟨aperture, _, hβ⟩ := exists_selectedEndpointMultiplier_retained_frequency_domain f p hρb hsrcρ
  have hfrequency : tsupport (selectedEndpointMultiplier f p threshold) ⊆ spatialPart ⁻¹' D := by
    intro ξ hξ
    have hf := hβ threshold hthreshold hξ
    exact ⟨⟨hf.1.1.1, ball_subset_ball (by dsimp [ε]; linarith) hf.1.1.2⟩, hf.2⟩
  let Kphase := elapsedPhysicalPhaseCarrier (endpointOutputMask f p output)
    (selectedEndpointMultiplier f p threshold) univ
  have hKV : ∀ low j, Kphase low j ⊆ Vphase := by
    intro low j w hw
    exact ⟨houtput hw.1, hfrequency hw.2.2.1⟩
  refine ⟨Kphase, fun low j ↦ isCompact_elapsedPhysicalPhaseCarrier
    (endpointOutputMask_properties f p ho hoc hout).2.1 _ isClosed_univ low j, hKV, ?_, ?_⟩
  · intro r hr ξ hξ w hw
    simpa only [SymbolBudgets.elapsedPoint_eq, elapsedPhasePoint] using
      hmap r hr (w.1, ξ) ⟨houtput hw.1, hfrequency hξ⟩
  · intro b ρ hρ r hr low j ξ hξ w hw
    have hk := tsupport_elapsedAmplitude_slice_subset_physicalPhaseCarrier b
      (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointMultiplier f p threshold)
      isClosed_univ (fun _ _ _ _ hh ↦ False.elim (hh (mem_univ _))) hρ r low j ξ hξ w hw
    refine ⟨hk, ?_⟩
    simpa only [SymbolBudgets.elapsedPoint_eq, elapsedPhasePoint] using
      hmap r hr _ (hKV low j hk)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
