module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.EnvelopeCritical
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.IncidenceParameters
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.FullSourceLocalChart
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.EnvelopeGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.RadialComparison

/-!
# One original local chart for both source signs

Apply the actual coefficient-capped stationary producer to every original source
incidence on a frozen regular sector. Choose a common positive time and angular neighborhood for both source signs before the
source mask. The coefficient cap is the original sector-history producer's
output and precedes every reference, history and operator.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ConstructedCarrierJets
open ResponseTransfer.RetainedFactors ResponseTransfer.DirectEvolution
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles ArbitraryAccuracy
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.RootFamily
open EvolutionIntegral.KernelIdentification RegularSector.Characteristic.AmplitudeBounds
open FullSourceStationary LeadingWave.FullModulation UniformEvolution
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.UniformAmplitudes
variable {d : ℕ} {ι : Type*} [Finite ι]
    {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (P : ι → Patch (d + 1)) (T : ∀ j, PatchQuantitativeFamily (P j) U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)

/-- Choose the same protected chart and all original source-incidence
radii from a fixed coefficient cap before reference selection. Construct the
smaller physical buffer, inner angular neighborhood, elapsed-gradient constants
and annulus covering every original source center. The complete source interval,
actual root, masks, collars and both critical branches are retained (`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_localChart_with_signed_full_source_envelope_margins
    (hframe : ∀ j, closedBall (0 : E) (T j).data.localReference.stateRadius ⊆ U)
    (Csrc : ι → Set Param) (hCsrc : ∀ j, IsCompact (Csrc j))
    (hcsrc : ∀ j c, c ∈ Csrc j →
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T j)) (T j).family.radius)
    (Xsrc : ι → Set E) (hXsrc : ∀ j, IsCompact (Xsrc j))
    (hsource : ∀ j, Xsrc j ×ˢ Csrc j ⊆ LeadingWave.FullModulation.domain (T j))
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hKprimary : ∀ j, closedBall x RQ ⊆ ball 0 (T j).physicalRadius)
    {ξ : E} (hξ : ξ ≠ 0) (hp : determinant (cubeStress (d + 1)) ξ = 0)
    (hreg : fderiv ℝ (determinant (cubeStress (d + 1))) ξ ≠ 0)
    {M aperture gap radius : ℝ} (hM : 0 ≤ M) (hAp : 0 < aperture) (hgap : 0 < gap)
    (hApξ : ∀ i, |ξ i| < aperture / 2)
    {coefficientCap : ℝ} (hcoefficientCap : 0 ≤ coefficientCap) :
    ∃ α > (0 : ℝ), ∃ τ > (0 : ℝ), ∀ cap > (0 : ℝ),
    ∃ chart : LocalChart Ω x RQ (cubeStress (d + 1)) ξ M,
      chart.bufferRadius ≤ chart.targetRadius ∧ chart.maskRadius ≤ chart.bufferRadius / 4 ∧
      chart.maskRadius ≤ cap ∧ chart.maskRadius ≤ τ ∧
      Icc (0 : ℝ) (3 * chart.maskRadius / 4) ⊆ Ioo (-2 * τ) (2 * τ) ∧
      RootBuffer chart.index chart.row chart.col (cubeStress (d + 1)) ξ chart.root
        chart.coefficientRadius chart.rootRadius chart.minorGap chart.transportGap ∧
      MapsTo (rootPhysicalPosition (coordinateSplit chart.index)) (tsupport chart.sourceMask)
        (closedBall x RQ) ∧
    ∃ evolutionTime speedGap rootSize rootCost,
      LocalProtectionCertificate chart evolutionTime speedGap rootSize rootCost ∧
    ∃ εcarrier > (0 : ℝ), εcarrier ≤ chart.rootRadius ∧ 4 * εcarrier ≤ chart.targetRadius ∧
      εcarrier ≤ chart.bufferRadius / 8 ∧ chart.maskRadius ≤ εcarrier ∧
      closedBall (NormedSpace.normalize ξ) α ⊆ primaryCoordinateChange chart.index ⁻¹'
        fullAngularCone chart.radialSection (coordinateSplit chart.index ξ).2
          (εcarrier / 4) (aperture / 2) ∧
    let z := ((coordinateSplit chart.index x).1, ((coordinateSplit chart.index x).2,
      (coordinateSplit chart.index ξ).2))
    ∃ gradientLower > (0 : ℝ), gradientLower ≤ 1 ∧
    ∃ gradientUpper : ℝ, 1 ≤ gradientUpper ∧
    (∀ (Q : E → Coeff), cNorm (closedBall x RQ) 3 Q ≤ coefficientCap →
      ∀ (h : RootState (Euclidean d) → ℝ)
        (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC),
      closedBall (z.1, z) chart.targetRadius ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C v) v) →
      (∀ v ∈ closedBall (z.1, z) chart.targetRadius, ‖twoTimePhaseMixed C v - 1‖ ≤ 1 / 2) →
      (∀ j, cNorm (closedBall (z.1, z) chart.targetRadius) j (twoTimePhase C) ≤
        chart.phaseCost j * (1 + cNorm (closedBall x RQ) (j + 1) Q)) →
      ∀ t ∈ Icc (0 : ℝ) εcarrier, ∀ y ∈ elapsedPhysicalBox z (εcarrier / 2),
      ∀ ζ ∈ retainedFrequencyDomain chart.radialSection z εcarrier aperture (1 / 2),
        gradientLower * ‖ζ‖ ≤ ‖fderiv ℝ (fun v ↦ elapsedPhase (curriedPhase chart.radialSection C) t v ζ) y‖ ∧
        ‖fderiv ℝ (fun v ↦ elapsedPhase (curriedPhase chart.radialSection C) t v ζ) y‖ ≤ gradientUpper * ‖ζ‖) ∧
    ∃ amplitudeLo > (0 : ℝ), ∃ amplitudeHi > amplitudeLo,
    ∀ negative : Bool, ∀ j : ι,
    let sourcePhase := fun Q ↦ if negative then
      (T j).negativeFullSourcePhaseInCoordinates chart.index Q else
      (T j).fullSourcePhaseInCoordinates chart.index Q
    let sourceGradient := fun Q y ζ ↦ if negative then
      -(LeadingWave.FullModulation.phaseGradient (T j) Q y ζ) else
      LeadingWave.FullModulation.phaseGradient (T j) Q y ζ
    let sourceCovector := fun c : Param ↦ if negative then
      -((T j).reference.covector (0, c.2)) else (T j).reference.covector (0, c.2)
    ∃ V : Set Param, IsOpen V ∧ IsCompact (closure V) ∧
      (∀ c ∈ closure V,
        c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T j)) (T j).family.radius) ∧
    ∃ δ > (0 : ℝ), δ ≤ (T j).family.threshold ∧
      (∀ mask : E → ℝ,
        tsupport mask ∩ sphere (0 : E) 1 ⊆ closedBall (NormedSpace.normalize ξ) α →
        ∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ y ∈ Xsrc j, ∀ c ∈ Csrc j, ∀ scale : ℝ, 0 < scale →
          scale • sourceGradient Q y c.2 ∈
            tsupport (RegularSector.FiniteMasks.conicMask mask) → c ∈ V) ∧
    ∃ sourceLower sourceUpper : ℝ, 0 < sourceLower ∧ sourceLower < sourceUpper ∧
      (∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ q ∈ closure (elapsedPhysicalBox z εcarrier) ×ˢ closure V,
          sourceLower ≤ ‖fderiv ℝ (fun y ↦ sourcePhase Q y q.2) q.1‖ ∧
          ‖fderiv ℝ (fun y ↦ sourcePhase Q y q.2) q.1‖ ≤ sourceUpper) ∧
    ∃ envelopeGap > (0 : ℝ), ∃ envelopeRadius > (0 : ℝ),
      envelopeGap ≤ gap ∧ radius ≤ envelopeRadius ∧
      envelopeGap ≤ retainedSelectorGap z.2.2 (εcarrier / 2) aperture
        (sourceLower / (2 * gradientUpper)) ∧
      4 * sourceUpper / gradientLower ≤ envelopeRadius ∧
      (∀ c₀ ∈ Csrc j,
        envelopeGap ≤ retainedSelectorGap z.2.2 (εcarrier / 2) aperture
          ((‖sourceCovector c₀‖ / 2) / (2 * gradientUpper)) ∧
        4 * (2 * ‖sourceCovector c₀‖) / gradientLower ≤ envelopeRadius) ∧
    ∃ ρ > (0 : ℝ), ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ),
    ∃ InvBound > (0 : ℝ),
      amplitudeLo ≤ g / 2 ∧ g + 1 + (1 + ‖chart.radialSection‖) * Rad ≤ amplitudeHi ∧
      let O := retainedOpenAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z εcarrier O
      let U₀ := elapsedPhysicalBox z (εcarrier / 2) ×ˢ V
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture gap radius ⊆ O ∧
      retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture
        envelopeGap envelopeRadius ⊆ O ∧
      (∀ c ∈ closure V, primaryCoordinateChange chart.index (sourceCovector c) ∈ O) ∧
      ∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 4 Q.1 ≤ coefficientCap →
        cNorm (closedBall x RQ) 4 Q.1 ≤ coefficientCap →
        cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC) (a : ℝ),
        (C : TC → TC) = twoTimeProjection Φ →
        C.source = ball (z.1, z) a → (∀ v ∈ ball z a, Φ (v, 0) = v) →
        closedBall (z.1, z) chart.targetRadius ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m, cNorm (closedBall (z.1, z) chart.targetRadius) m (twoTimePhase C) ≤
          chart.phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q.1)) →
      a ≤ chart.rootRadius →
      closedBall z chart.rootRadius ⊆ fieldDomain (coordinateSplit chart.index) Ω chart.radialSection (coordinateSplit chart.index ξ).2 chart.coefficientRadius →
      (∀ w ∈ fieldDomain (coordinateSplit chart.index) Ω chart.radialSection (coordinateSplit chart.index ξ).2 chart.coefficientRadius,
        ∀ t : ℝ, 0 < t → fieldRoot (coordinateSplit chart.index) Q.1 chart.root (w.1, (w.2.1, t • w.2.2)) =
          t * fieldRoot (coordinateSplit chart.index) Q.1 chart.root w) →
      (∀ v ∈ C.target, twoTimeState Φ (C.symm v) ∈
          fieldDomain (coordinateSplit chart.index) Ω chart.radialSection (coordinateSplit chart.index ξ).2 chart.coefficientRadius ∧
        (twoTimeState Φ (C.symm v)).1 = v.1) →
      (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C)
        (twoTimePhaseDifferential (fieldRoot (coordinateSplit chart.index) Q.1 chart.root) Φ C v) v) →
      ∃ κ : Bool → Par → W, ∀ adj : Bool,
        ContDiffOn ℝ ∞
          (fullSourceJointPhase adj (curriedPhase chart.radialSection C) (sourcePhase Q))
          ((Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D) ∧
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ sourcePhase Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            (sourcePhase Q) (p, w)) (κ adj p) = 0 ∧
          fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            (sourcePhase Q) (p, κ adj p) = 0 ∧
          dist (κ adj p) (WithLp.toLp 2
            (p.2.1, gradient (fun y ↦ sourcePhase Q y p.2.2) p.2.1)) ≤ ρ / 2 ∧
          (∀ w ∈ closure D,
            let f := fun q w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
              (sourcePhase Q) ((p.1, q), w)
            IsUnit (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w) ∧
              ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w)‖ ≤ InvBound) ∧
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈ fullSourceSignedCarrier z εcarrier (closure V) O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain chart.radialSection C.target := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨row, col, hm⟩ := exists_nonzero_adjugate_entry_of_regular
    (cubeStress (d + 1)) ξ hreg
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    hρb, μ, hμ, ν, hν, phaseCost, hphaseCost, rootCost, hrootCost,
    evolutionTime, hevolutionTime, speedGap, hspeedGap, rootSize, hrootSize,
    haR, haT, htimeDomain, hℓ, hroot, haL, hrootPhys, hwholeState, hcap⟩ :=
    exists_protected_conic_pencilAmplitudes_below_source_cap
      hΩ x hRQ hKΩ (cubeStress (d + 1)) ξ row col hξ hp hreg hm hM
  let z := ((coordinateSplit i x).1, ((coordinateSplit i x).2, (coordinateSplit i ξ).2))
  let εcarrier := min (min (b / 8) (ρ / 8)) (L / 2)
  have hεcarrier : 0 < εcarrier := lt_min (lt_min (by positivity) (by positivity)) (half_pos hL)
  have hεL : εcarrier ≤ L := (min_le_right _ _).trans (by linarith)
  have hεb : 4 * εcarrier ≤ b := by
    have hle := (min_le_left (min (b / 8) (ρ / 8)) (L / 2)).trans (min_le_left _ _)
    dsimp only [εcarrier]
    linarith
  have hphysical : MapsTo (primaryCoordinateChange i).symm
      (closure (elapsedPhysicalBox z εcarrier)) (closedBall x RQ) :=
    retained_primary_physical_buffer i z hεL hrootPhys
  have hερ : εcarrier ≤ ρ / 8 :=
    (min_le_left (min (b / 8) (ρ / 8)) (L / 2)).trans (min_le_right _ _)
  obtain ⟨_, _, _, _, gradientLower, hgradLo, hgradLoOne, gradientUpper, hgradHi, hfrequency⟩ :=
    exists_retained_elapsed_frequency_comparison (aperture := aperture) ℓ z hεcarrier
      (by linarith : 2 * εcarrier ≤ b) phaseCost hphaseCost coefficientCap
  have hnorms (j : ι) := (T j).exists_full_source_frozen_gradient_bounds_on_compact (hCsrc j) (hcsrc j)
  choose normLo hnormLo normHi hnormHi hnorm using hnorms
  have hannulus (j : ι) := exists_full_source_envelope_annulus z.2.2 hεcarrier hAp hgap
    (radius := radius) (hnormLo j) (hnormHi j) hgradLo (zero_lt_one.trans_le hgradHi)
  choose centerGap hgapC centerRadius hradiusC hgapOrigC hradiusOrigC hselectorC using hannulus
  have hcritical (j : ι) := (T j).exists_conic_root_neighborhood_with_capped_critical_maps_for_all_annuli
    (hframe j) hξ i row col ℓ hℓ H hε hL hμ hν hroot z hεcarrier hεb hAp (hphysical.mono_right hKΩ)
    (KQ := closedBall x RQ) hcoefficientCap phaseCost hphaseCost
  choose N hN hbase hNcone hmaps using hcritical
  let Wcone : ι → Set E := fun j ↦
    (fun θ ↦ (cubeStress (d + 1), θ)) ⁻¹' N j ∩
      primaryCoordinateChange i ⁻¹' fullAngularCone ℓ z.2.2 (εcarrier / 2) aperture
  have hW (j : ι) : IsOpen (Wcone j) :=
    ((hN j).preimage (continuous_const.prodMk continuous_id)).inter
      ((isOpen_fullAngularCone _ _ _ _).preimage (primaryCoordinateChange i).continuous)
  have hξcone : primaryCoordinateChange i ξ ∈
      fullAngularCone ℓ z.2.2 (εcarrier / 2) aperture := by
    refine ⟨?_, ?_⟩
    · change 0 < ℓ (coordinateSplit i ξ).2 ∧
        (ℓ (coordinateSplit i ξ).2)⁻¹ • (coordinateSplit i ξ).2 ∈
          ball (coordinateSplit i ξ).2 (εcarrier / 2)
      rw [hℓ]
      simpa only [inv_one, one_smul] using
        And.intro zero_lt_one (mem_ball_self (half_pos hεcarrier))
    · simpa only [primaryCoordinateChange_apply, timeSpacePoint_time,
        spatialPart_timeSpacePoint, hℓ, mul_one] using
        (hApξ i).trans (half_lt_self hAp)
  have hξW (j : ι) : ξ ∈ Wcone j := ⟨hbase j, hξcone⟩
  have hWcone (j : ι) (θ : E) (hθ : θ ∈ Wcone j) (t : ℝ) (ht : 0 < t) :
      t • θ ∈ Wcone j := by
    refine ⟨hNcone j _ hθ.1 t ht, ?_⟩
    change primaryCoordinateChange i (t • θ) ∈ fullAngularCone ℓ z.2.2 (εcarrier / 2) aperture
    rw [map_smul]
    exact smul_mem_fullAngularCone ht hθ.2
  have hparameters (j : ι) := (T j).exists_full_source_scaled_conic_incidence_buffer
    (hCsrc j) (hcsrc j) (hXsrc j) (hsource j) hξ (hW j) (hξW j) (hWcone j)
  choose αj hαj V hV hVK hparam δc hδc hδcT hcapture using hparameters
  have hprimary (j : ι) : ∀ q ∈ closure (elapsedPhysicalBox z εcarrier) ×ˢ closure (V j),
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain (T j) := by
    intro q hq
    exact (T j).full_source_mem_phaseDomain_of_physical_buffer
      (ball_subset_closedBall (hKprimary j (hphysical hq.1))) ((hparam j q.2 hq.2).1)
  have hsourceBand (j : ι) := (T j).exists_full_source_gradient_band_on_physical_incidence
    i z εcarrier (hVK j) (hprimary j)
  choose sourceLower sourceUpper δg hsourceLo hsourceHi hδg hδgT hsourceBand using hsourceBand
  let envelopeGap : ι → ℝ := fun j ↦ min (centerGap j)
    (retainedSelectorGap z.2.2 (εcarrier / 2) aperture (sourceLower j / (2 * gradientUpper)))
  let envelopeRadius : ι → ℝ := fun j ↦ max (centerRadius j) (4 * sourceUpper j / gradientLower)
  have hgapE (j : ι) : 0 < envelopeGap j := lt_min (hgapC j)
    (retainedSelectorGap_pos _ (half_pos hεcarrier) hAp
      (div_pos (hsourceLo j) (by positivity)))
  have hradiusE (j : ι) : 0 < envelopeRadius j := (hradiusC j).trans_le (le_max_left _ _)
  have hgapOrig (j : ι) : envelopeGap j ≤ gap := (min_le_left _ _).trans (hgapOrigC j)
  have hradiusOrig (j : ι) : radius ≤ envelopeRadius j := (hradiusOrigC j).trans (le_max_left _ _)
  have hselector (j : ι) (c : Param) (hc : c ∈ Csrc j) :
      envelopeGap j ≤ retainedSelectorGap z.2.2 (εcarrier / 2) aperture
        ((‖(T j).reference.covector (0, c.2)‖ / 2) / (2 * gradientUpper)) ∧
      4 * (2 * ‖(T j).reference.covector (0, c.2)‖) / gradientLower ≤ envelopeRadius j := by
    have hh := hselectorC j _ (hnorm j c hc).1 (hnorm j c hc).2
    exact ⟨(min_le_left _ _).trans hh.1, hh.2.trans (le_max_left _ _)⟩
  have hstationary (j : ι) := hmaps j (envelopeGap j) (hgapE j) (envelopeRadius j)
    (closure (V j)) (V j) (hVK j) (hV j) subset_closure (hprimary j)
    (fun c hc ↦ (hparam j c hc).2.2) (fun c hc ↦ (hparam j c hc).2.1)
  choose δs hδs hδsT margin hmargin g hg Rad hRad τj hτj hτjε
    InvBound hInvBound hstationary using hstationary
  have hcriticalNeg (j : ι) := (T j).exists_negative_conic_root_neighborhood_with_capped_critical_maps_for_all_annuli
    (hframe j) hξ i row col ℓ hℓ H hε hL hμ hν hroot z hεcarrier hεb hAp (hphysical.mono_right hKΩ)
    (KQ := closedBall x RQ) hcoefficientCap phaseCost hphaseCost
  choose NNeg hNNeg hbaseNeg hNconeNeg hmapsNeg using hcriticalNeg
  let WconeNeg : ι → Set E := fun j ↦
    (fun θ ↦ (cubeStress (d + 1), θ)) ⁻¹' NNeg j ∩
      primaryCoordinateChange i ⁻¹' fullAngularCone ℓ z.2.2 (εcarrier / 2) aperture
  have hWNeg (j : ι) : IsOpen (WconeNeg j) :=
    ((hNNeg j).preimage (continuous_const.prodMk continuous_id)).inter
      ((isOpen_fullAngularCone _ _ _ _).preimage (primaryCoordinateChange i).continuous)
  have hξconeNeg : primaryCoordinateChange i ξ ∈
      fullAngularCone ℓ z.2.2 (εcarrier / 2) aperture := by
    refine ⟨?_, ?_⟩
    · change 0 < ℓ (coordinateSplit i ξ).2 ∧
        (ℓ (coordinateSplit i ξ).2)⁻¹ • (coordinateSplit i ξ).2 ∈
          ball (coordinateSplit i ξ).2 (εcarrier / 2)
      rw [hℓ]
      simpa only [inv_one, one_smul] using
        And.intro zero_lt_one (mem_ball_self (half_pos hεcarrier))
    · simpa only [primaryCoordinateChange_apply, timeSpacePoint_time,
        spatialPart_timeSpacePoint, hℓ, mul_one] using
        (hApξ i).trans (half_lt_self hAp)
  have hξWNeg (j : ι) : ξ ∈ WconeNeg j := ⟨hbaseNeg j, hξconeNeg⟩
  have hWconeNeg (j : ι) (θ : E) (hθ : θ ∈ WconeNeg j) (t : ℝ) (ht : 0 < t) :
      t • θ ∈ WconeNeg j := by
    refine ⟨hNconeNeg j _ hθ.1 t ht, ?_⟩
    change primaryCoordinateChange i (t • θ) ∈ fullAngularCone ℓ z.2.2 (εcarrier / 2) aperture
    rw [map_smul]
    exact smul_mem_fullAngularCone ht hθ.2
  have hparametersNeg (j : ι) := (T j).exists_negative_full_source_scaled_conic_incidence_buffer
    (hCsrc j) (hcsrc j) (hXsrc j) (hsource j) hξ (hWNeg j) (hξWNeg j) (hWconeNeg j)
  choose αjNeg hαjNeg VNeg hVNeg hVKNeg hparamNeg δcNeg hδcNeg hδcTNeg hcaptureNeg using hparametersNeg
  have hprimaryNeg (j : ι) : ∀ q ∈ closure (elapsedPhysicalBox z εcarrier) ×ˢ closure (VNeg j),
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain (T j) := by
    intro q hq
    exact (T j).full_source_mem_phaseDomain_of_physical_buffer
      (ball_subset_closedBall (hKprimary j (hphysical hq.1))) ((hparamNeg j q.2 hq.2).1)
  have hsourceBandNeg (j : ι) := (T j).exists_negative_full_source_gradient_band_on_physical_incidence
    i z εcarrier (hVKNeg j) (hprimaryNeg j)
  choose sourceLowerNeg sourceUpperNeg δgNeg hsourceLoNeg hsourceHiNeg hδgNeg hδgTNeg hsourceBandNeg using hsourceBandNeg
  let envelopeGapNeg : ι → ℝ := fun j ↦ min (centerGap j)
    (retainedSelectorGap z.2.2 (εcarrier / 2) aperture (sourceLowerNeg j / (2 * gradientUpper)))
  let envelopeRadiusNeg : ι → ℝ := fun j ↦ max (centerRadius j) (4 * sourceUpperNeg j / gradientLower)
  have hgapENeg (j : ι) : 0 < envelopeGapNeg j := lt_min (hgapC j)
    (retainedSelectorGap_pos _ (half_pos hεcarrier) hAp
      (div_pos (hsourceLoNeg j) (by positivity)))
  have hradiusENeg (j : ι) : 0 < envelopeRadiusNeg j := (hradiusC j).trans_le (le_max_left _ _)
  have hgapOrigNeg (j : ι) : envelopeGapNeg j ≤ gap := (min_le_left _ _).trans (hgapOrigC j)
  have hradiusOrigNeg (j : ι) : radius ≤ envelopeRadiusNeg j := (hradiusOrigC j).trans (le_max_left _ _)
  have hselectorNeg (j : ι) (c : Param) (hc : c ∈ Csrc j) :
      envelopeGapNeg j ≤ retainedSelectorGap z.2.2 (εcarrier / 2) aperture
        ((‖(T j).reference.covector (0, c.2)‖ / 2) / (2 * gradientUpper)) ∧
      4 * (2 * ‖(T j).reference.covector (0, c.2)‖) / gradientLower ≤ envelopeRadiusNeg j := by
    have hh := hselectorC j _ (hnorm j c hc).1 (hnorm j c hc).2
    exact ⟨(min_le_left _ _).trans hh.1, hh.2.trans (le_max_left _ _)⟩
  have hstationaryNeg (j : ι) := hmapsNeg j (envelopeGapNeg j) (hgapENeg j) (envelopeRadiusNeg j)
    (closure (VNeg j)) (VNeg j) (hVKNeg j) (hVNeg j) subset_closure (hprimaryNeg j)
    (fun c hc ↦ (hparamNeg j c hc).2.2) (fun c hc ↦ (hparamNeg j c hc).2.1)
  choose δsNeg hδsNeg hδsTNeg marginNeg hmarginNeg gNeg hgNeg RadNeg hRadNeg τjNeg hτjNeg hτjεNeg
    InvBoundNeg hInvBoundNeg hstationaryNeg using hstationaryNeg
  let gSigned : Bool × ι → ℝ := fun p ↦ if p.1 then gNeg p.2 else g p.2
  let RadSigned : Bool × ι → ℝ := fun p ↦ if p.1 then RadNeg p.2 else Rad p.2
  have hgSigned : ∀ p, 0 < gSigned p := by
    rintro ⟨negative, j⟩
    cases negative
    · exact hg j
    · exact hgNeg j
  obtain ⟨amplitudeLo, hamplitudeLo, amplitudeHi, hamplitudeHi, hband⟩ :=
    exists_retained_envelope_amplitude_band ℓ gSigned RadSigned hgSigned
  have hbandPos (j : ι) := hband (false, j)
  have hbandNeg (j : ι) := hband (true, j)
  obtain ⟨αinner, hαinner, hinner⟩ :=
    exists_pulledback_inner_cone_radius i ξ hξ ℓ hℓ hεcarrier (hApξ i)
  let αSigned : Bool × ι → ℝ := fun p ↦ if p.1 then αjNeg p.2 else αj p.2
  let τSigned : Bool × ι → ℝ := fun p ↦ if p.1 then τjNeg p.2 else τj p.2
  have hαSigned : ∀ p, 0 < αSigned p := by
    rintro ⟨negative, j⟩
    cases negative
    · exact hαj j
    · exact hαjNeg j
  have hτSigned : ∀ p, 0 < τSigned p := by
    rintro ⟨negative, j⟩
    cases negative
    · exact hτj j
    · exact hτjNeg j
  obtain ⟨αsource, hαsource, hαsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : Bool × ι ↦ (0 : ℝ)) (y := αSigned) hαSigned
  obtain ⟨τ, hτ, hτsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : Bool × ι ↦ (0 : ℝ)) (y := τSigned) hτSigned
  let α := min αsource αinner
  have hα : 0 < α := lt_min hαsource hαinner
  have hαle (j : ι) : α ≤ αj j :=
    (min_le_left _ _).trans (by simpa only [αSigned, Bool.false_eq_true, ↓reduceIte, zero_add] using (hαsmall (false, j)).le)
  have hαleNeg (j : ι) : α ≤ αjNeg j :=
    (min_le_left _ _).trans (by simpa only [αSigned, ↓reduceIte, zero_add] using (hαsmall (true, j)).le)
  have hαinnerle : α ≤ αinner := min_le_right _ _
  have hτle (j : ι) : τ ≤ τj j := by
    simpa only [τSigned, Bool.false_eq_true, ↓reduceIte, zero_add] using (hτsmall (false, j)).le
  have hτleNeg (j : ι) : τ ≤ τjNeg j := by
    simpa only [τSigned, ↓reduceIte, zero_add] using (hτsmall (true, j)).le
  refine ⟨α, hα, τ, hτ, ?_⟩
  intro cap hcapPos
  obtain ⟨src, hsrc, hsrccap, hsrca, hsrcρ, _, σ, κ, hσ, hκ, hσr, hκr,
    hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, hevolution⟩ := hcap (min (min cap τ) εcarrier) (lt_min (lt_min hcapPos hτ) hεcarrier)
  have hsrcτ : src ≤ τ := hsrccap.trans ((min_le_left _ _).trans (min_le_right cap τ))
  let chart : LocalChart Ω x RQ (cubeStress (d + 1)) ξ M :=
    ⟨i, row, col, hm, ℓ, H, ε, L, a, b, ρ, ρo, src, μ, ν,
      phaseCost, σ, κ, hε, hL, ha, hb, hρ, hρo, hsrc, hsrca, hμ, hν,
      hphaseCost, hℓ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ,
      hevolution.toUniformChartEvolution⟩
  have hsourceMask : MapsTo (rootPhysicalPosition (coordinateSplit i)) (tsupport σ)
      (closedBall x RQ) := fun w hw ↦ hrootPhys
    (closedBall_subset_closedBall (by linarith : src / 2 ≤ L) (ball_subset_closedBall (hsσ hw)))
  have hinterval : Icc (0 : ℝ) (3 * src / 4) ⊆ Ioo (-2 * τ) (2 * τ) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨chart, hρb, hsrcρ, hsrccap.trans ((min_le_left _ _).trans (min_le_left cap τ)), hsrcτ, hinterval,
    hroot, hsourceMask, evolutionTime, speedGap, rootSize, rootCost,
    ⟨hevolutionTime, hspeedGap, hrootSize, hrootCost, haR, haT, htimeDomain,
      haL, hwholeState, hevolution⟩, εcarrier, hεcarrier, hεL, hεb, hερ,
    hsrccap.trans (min_le_right _ _),
    (closedBall_subset_closedBall hαinnerle).trans hinner,
    gradientLower, hgradLo, hgradLoOne, gradientUpper, hgradHi, ?_,
    amplitudeLo, hamplitudeLo, amplitudeHi, hamplitudeHi, ?_⟩
  · intro Q hQ h Φ C hbuffer hCsm hdiff hnear hphase t ht
    exact (hfrequency (closedBall x RQ) Q hQ h Φ C hbuffer hCsm hdiff hnear hphase t ht).2.2.2.2
  intro negative j
  cases negative
  · dsimp only
    obtain ⟨hO, hOc, hOK, hFO, hfreq, hbranch⟩ := hstationary j
    refine ⟨V j, hV j, hVK j, (fun c hc ↦ (hparam j c hc).1),
      min (min (δc j) (δs j)) (δg j), lt_min (lt_min (hδc j) (hδs j)) (hδg j),
      (min_le_right _ _).trans (hδgT j),
      ?_, sourceLower j, sourceUpper j, hsourceLo j, hsourceHi j,
      (fun Q hQ ↦ hsourceBand j Q (hQ.trans_le (min_le_right _ _))), envelopeGap j, hgapE j, envelopeRadius j, hradiusE j,
      hgapOrig j, hradiusOrig j, min_le_right _ _, le_max_right _ _, hselector j,
      margin j, hmargin j, g j, hg j, Rad j, hRad j,
      InvBound j, hInvBound j, (hbandPos j).1, (hbandPos j).2, hO, hOc, hOK,
      (retainedAnnularFrequencyCarrier_mono ℓ z.2.2 (εcarrier / 2) aperture
        (hgapOrig j) (hradiusOrig j)).trans hFO, hFO, hfreq, ?_⟩
    · intro mask hmask Q hQ y hy c hc scale hscale hinc
      exact hcapture j mask (hmask.trans (closedBall_subset_closedBall (hαle j))) Q
        (hQ.trans_le ((min_le_left _ _).trans (min_le_left _ _))) y hy c hc scale hscale hinc
    · intro Q hQstate hQcoeff hQlow Φ C a' hC hsource' hi hbuffer hCsm hbudget
        ha'L hLD hhom hstate hphase
      obtain ⟨w, hw⟩ := hbranch Q hQstate hQcoeff
        (hQlow.trans_le ((min_le_left _ _).trans (min_le_right _ _))) Φ C a' hC hsource' hi hbuffer hCsm hbudget
        ha'L hLD hhom hstate hphase
      have hsub : Ioo (-2 * τ) (2 * τ) ×ˢ
          (elapsedPhysicalBox z (εcarrier / 2) ×ˢ V j) ⊆
          Ioo (-2 * τj j) (2 * τj j) ×ˢ
            (elapsedPhysicalBox z (εcarrier / 2) ×ˢ V j) := by
        rintro ⟨t, q⟩ ⟨ht, hq⟩
        exact ⟨⟨by linarith [ht.1, hτle j], by linarith [ht.2, hτle j]⟩, hq⟩
      exact ⟨w, fun adj ↦ ⟨(hw adj).1.mono (prod_mono hsub Subset.rfl),
        (hw adj).2.1.mono hsub, (hw adj).2.2.1,
        fun p hp ↦ (hw adj).2.2.2 p (hsub hp)⟩⟩
  · dsimp only
    obtain ⟨hO, hOc, hOK, hFO, hfreq, hbranch⟩ := hstationaryNeg j
    refine ⟨VNeg j, hVNeg j, hVKNeg j, (fun c hc ↦ (hparamNeg j c hc).1),
      min (min (δcNeg j) (δsNeg j)) (δgNeg j), lt_min (lt_min (hδcNeg j) (hδsNeg j)) (hδgNeg j),
      (min_le_right _ _).trans (hδgTNeg j),
      ?_, sourceLowerNeg j, sourceUpperNeg j, hsourceLoNeg j, hsourceHiNeg j,
      (fun Q hQ ↦ hsourceBandNeg j Q (hQ.trans_le (min_le_right _ _))), envelopeGapNeg j, hgapENeg j, envelopeRadiusNeg j, hradiusENeg j,
      hgapOrigNeg j, hradiusOrigNeg j, min_le_right _ _, le_max_right _ _, (by simpa only [↓reduceIte, norm_neg] using hselectorNeg j),
      marginNeg j, hmarginNeg j, gNeg j, hgNeg j, RadNeg j, hRadNeg j,
      InvBoundNeg j, hInvBoundNeg j, (hbandNeg j).1, (hbandNeg j).2, hO, hOc, hOK,
      (retainedAnnularFrequencyCarrier_mono ℓ z.2.2 (εcarrier / 2) aperture
        (hgapOrigNeg j) (hradiusOrigNeg j)).trans hFO, hFO, hfreq, ?_⟩
    · intro mask hmask Q hQ y hy c hc scale hscale hinc
      exact hcaptureNeg j mask (hmask.trans (closedBall_subset_closedBall (hαleNeg j))) Q
        (hQ.trans_le ((min_le_left _ _).trans (min_le_left _ _))) y hy c hc scale hscale hinc
    · intro Q hQstate hQcoeff hQlow Φ C a' hC hsource' hi hbuffer hCsm hbudget
        ha'L hLD hhom hstate hphase
      obtain ⟨w, hw⟩ := hbranch Q hQstate hQcoeff
        (hQlow.trans_le ((min_le_left _ _).trans (min_le_right _ _))) Φ C a' hC hsource' hi hbuffer hCsm hbudget
        ha'L hLD hhom hstate hphase
      have hsub : Ioo (-2 * τ) (2 * τ) ×ˢ
          (elapsedPhysicalBox z (εcarrier / 2) ×ˢ VNeg j) ⊆
          Ioo (-2 * τjNeg j) (2 * τjNeg j) ×ˢ
            (elapsedPhysicalBox z (εcarrier / 2) ×ˢ VNeg j) := by
        rintro ⟨t, q⟩ ⟨ht, hq⟩
        exact ⟨⟨by linarith [ht.1, hτleNeg j], by linarith [ht.2, hτleNeg j]⟩, hq⟩
      exact ⟨w, fun adj ↦ ⟨(hw adj).1.mono (prod_mono hsub Subset.rfl),
        (hw adj).2.1.mono hsub, (hw adj).2.2.1,
        fun p hp ↦ (hw adj).2.2.2 p (hsub hp)⟩⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
