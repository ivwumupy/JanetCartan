module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ResidualSupport
public import JanetCartan.Analysis.Microlocal.SelectedSectorProtection.SelectedBuffers

/-!
# Positions, frequencies and clock on the selected comparable carrier

The angular radius for the proof masks comes from the original doubled
multiplier, not the larger amplitude jet buffer. The radial coordinate is
recovered before dilation. The temporal graph covector detects elapsed times
outside the common physical interval, even for the literal adjoint.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
open RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization FiniteChain.Graph
open PhysicalShells SelectedSectorProtection
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => ℝ × JointVariables E
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Literally the right side of `Kglobal` in
`exists_selected_direct_residual_carriers`; no shell or operator is changed
(`app:ch_regular:eq:joint-kernel-phase`). -/
abbrev selectedResidualComparableCarrier (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (threshold c C a b : ℝ) :=
  Comparable.comparableJointCarrier c C a b
    (elapsedComparableCarrier (endpointOutputMask f p output)
      (selectedEndpointMultiplier f p threshold) univ c C a b)
    (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
    (frequencyAnnulus a b)

/-- The explicit compact support used for the selected residual Fourier
estimate. The same set is used for the amplitude, all output jets and the
two open phase domains (`app:ch_regular:eq:chain-tail`). -/
abbrev selectedRetainedResidualCarrier (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (threshold c C a b : ℝ) (θ : ℝ → ℂ) (ra rb tlo thi : ℝ) : Set V :=
  let lc := f.chart p
  let e := coordinateSplit lc.index
  let z := ((e x).1, ((e x).2, (e p.val.val).2))
  retainedResidualJetCarrier
    (tsupport θ ×ˢ selectedResidualComparableCarrier f p output threshold c C a b)
    lc.radialSection z (lc.bufferRadius/2) ra rb tlo thi ∩
      {v | v.1 ≤ 3 * lc.maskRadius / 4}

/-- The unchanged physical endpoint and input put the output in its half
mask box and their two clocks at distance at most four physical radii. The
bound uses the output radius once and the original input radius three times
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem selectedResidualComparableCarrier_positions (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) {output : E → ℝ} (hout : tsupport output ⊆ ball x f.physicalRadius)
    {threshold c C a b : ℝ} {v : JointVariables E}
    (hv : v ∈ selectedResidualComparableCarrier f p output threshold c C a b) :
    let lc := f.chart p
    let e := coordinateSplit lc.index
    v.1.1 0 ∈ closedBall (e x).1 (lc.maskRadius / 2) ∧
      spatialPart v.1.1 ∈ closedBall (e x).2 (lc.maskRadius / 2) ∧
      |v.1.1 0 - v.1.2 0| ≤ 4 * f.physicalRadius := by
  intro lc e
  let g := physicalCoordinates lc.index
  have ho := tsupport_comp_subset_preimage (fun w ↦ (output w : ℂ)) g.continuous hv.1.1.1
  have hi := tsupport_comp_subset_preimage (fun w ↦ (f.inputMask w : ℂ)) g.continuous hv.1.1.2
  have hu := hout (tsupport_comp_subset Complex.ofReal_zero output ho)
  have hz := f.inputMask_support (tsupport_comp_subset Complex.ofReal_zero f.inputMask hi)
  have hbox := f.physicalBall_in_chart p (a := g v.1.1)
    (ball_subset_closedBall ((ball_subset_ball (by linarith [f.physicalRadius_pos] :
        f.physicalRadius ≤ 4 * f.physicalRadius)) hu))
  change dist (coordinateSplit lc.index (physicalCoordinates lc.index v.1.1)) (e x) <
    lc.neighborhoodRadius at hbox
  rw [split_physicalCoordinates, Prod.dist_eq, max_lt_iff] at hbox
  have hhalf : lc.neighborhoodRadius ≤ lc.maskRadius / 2 :=
    (min_le_left _ _ : lc.neighborhoodRadius ≤ lc.maskRadius / 8).trans
      (by linarith [lc.maskRadius_pos])
  refine ⟨hbox.1.le.trans hhalf, hbox.2.le.trans hhalf, ?_⟩
  have hd := (PiLp.dist_apply_le (g v.1.1) (g v.1.2) lc.index).trans
    (dist_triangle (g v.1.1) x (g v.1.2))
  have htime (w : E) : (g w) lc.index = w 0 := by
    change (coordinateSplit lc.index (physicalCoordinates lc.index w)).1 = w 0
    rw [split_physicalCoordinates]
  rw [Real.dist_eq, htime, htime, dist_comm x] at hd
  linarith [mem_ball.mp hu, mem_ball.mp hz]

/-- The closure of the actual selected frequency cone has the tighter angular
margin of the proof gaps. Normalize after taking out the positive comparable
scale, with no radial action on either proof mask
(`app:ch_regular:eq:chain-tail`). -/
theorem selectedResidualComparableCarrier_angular (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) {threshold : ℝ} (ht : f.radialThreshold ≤ threshold)
    {output : E → ℝ} {c C a b : ℝ} {v : JointVariables E}
    (hv : v ∈ selectedResidualComparableCarrier f p output threshold c C a b)
    (hne : spatialPart v.2.1 ≠ 0) :
    let lc := f.chart p
    spatialPart v.2.1 ∈ angularCone lc.radialSection (coordinateSplit lc.index p.val.val).2
      (lc.maskRadius / 2) := by
  intro lc
  let ℓ := lc.radialSection
  let η₀ := (coordinateSplit lc.index p.val.val).2
  apply closure_angularCone_subset (ρ := lc.neighborhoodRadius)
    ((lc.neighborhoodRadius_lt_mask).trans (by linarith [lc.maskRadius_pos]))
  refine ⟨?_, hne⟩
  apply spatialPartCLM.continuous.closure_preimage_subset
  apply closure_mono (s := {ξ : E | ∃ ρ : ℝ, 1 ≤ ρ ∧
    ρ • ξ ∈ elapsedFrequencyCarrier (selectedEndpointMultiplier f p threshold) univ})
    (t := spatialPart ⁻¹' angularCone ℓ η₀ lc.neighborhoodRadius) ?_ hv.2.2.2
  rintro ξ ⟨ρ, hρ, hξ⟩
  have hraw := tsupport_comp_subset_preimage (dilatedConicMask (f.angularMask p) f.radialThreshold)
    (physicalCoordinates lc.index).continuous (selectedEndpointMultiplier_tsupport_subset f p ht hξ.1)
  have hcone := lc.angularNeighborhood_of_mem_rightSupport (f.angularMask_support p)
    f.radialThreshold_ge_one hraw
  change (coordinateSplit lc.index (physicalCoordinates lc.index (ρ • ξ))).2 ∈ lc.spatialCone at hcone
  rw [split_physicalCoordinates] at hcone
  have h' := smul_mem_angularCone (ℓ := ℓ) (η₀ := η₀) (ρ := lc.neighborhoodRadius)
    (η := spatialPart (ρ • ξ)) hcone (inv_pos.mpr (zero_lt_one.trans_le hρ))
  change spatialPart ξ ∈ angularCone ℓ η₀ lc.neighborhoodRadius
  simpa only [SymbolBudgets.spatialPart_smul, inv_smul_smul₀ (zero_lt_one.trans_le hρ).ne'] using h'

/-- The actual graph frequency lies in the phase band with the original
half-mask aperture and the *undilated* section interval. The two inequalities
on the phase radii are purely scalar. In particular the retained amplitude
band is never substituted at the original graph covector
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem retainedResidualJetCarrier_phase_band (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) {threshold : ℝ} (ht : f.radialThreshold ≤ threshold)
    {output : E → ℝ} {c C a b : ℝ} {θ : ℝ → ℂ} {ra rb tlo thi aPhase bPhase : ℝ}
    (hlo : 0 < tlo) (hra : 0 < ra) (hleft : aPhase ≤ ra / thi) (hright : ra / tlo ≤ bPhase)
    {v : V}
    (hv : let lc := f.chart p
          let e := coordinateSplit lc.index
          let z := ((e x).1, ((e x).2, (e p.val.val).2))
          v ∈ retainedResidualJetCarrier
            (tsupport θ ×ˢ selectedResidualComparableCarrier f p output threshold c C a b)
            lc.radialSection z (lc.bufferRadius/2) ra rb tlo thi) :
    let lc := f.chart p
    spatialPart v.2.2.1 ∈ radialSectionBand lc.radialSection (coordinateSplit lc.index p.val.val).2
      (lc.maskRadius / 2) aPhase bPhase := by
  intro lc
  have hr := section_mem_Icc_of_retainedResidualJetCarrier hlo hra hv
  have hthi : 0 < thi := by
    obtain ⟨_, t, h, _⟩ := hv
    exact (hlo.trans_le h.1).trans_le h.2
  have hpos : 0 < lc.radialSection (spatialPart v.2.2.1) := (div_pos hra hthi).trans_le hr.1
  have hne : spatialPart v.2.2.1 ≠ 0 := by intro he; simp [he] at hpos
  have hang := selectedResidualComparableCarrier_angular f p ht hv.1.2 hne
  let s := lc.radialSection (spatialPart v.2.2.1)
  refine ⟨(s, s⁻¹ • spatialPart v.2.2.1), ⟨⟨hleft.trans hr.1, hr.2.trans hright⟩,
    ball_subset_closedBall hang.2, ?_⟩, smul_inv_smul₀ hpos.ne' _⟩
  change lc.radialSection (s⁻¹ • spatialPart v.2.2.1) = 1
  simp only [map_smul, smul_eq_mul, ← show lc.radialSection (spatialPart v.2.2.1) = s from rfl,
    inv_mul_cancel₀ hpos.ne']

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
