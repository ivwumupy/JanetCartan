module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.IncidenceCritical
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.IncidenceParameters
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.FullSourceLocalChart
public import Mathlib.Algebra.Order.Field.Pi

/-!
# Protected sector charts for all original source incidences

The sector chart is constructed from its frozen regular zero. It is shared by
the fixed finite family of original full sources, whose source labels need not
be chart centers. Compact incidence protection and actual stationary maps give
one common elapsed interval before source masks. No primary patch, operator or
inverse is reselected. Consumer: finite selection retaining these same charts
in `app:ch_response:eq:fixed-factor-transfer`.
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
open FullSourceStationary LeadingWave.FullModulation
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

/-- Construct a protected sector chart from determinant regularity, then
protect EVERY original source incident to a sufficiently narrow angular mask.
The finite original primary family is fixed independently of the sector center.
Conic incidence buffers are constructed for its unchanged full parameter
supports; the actual stationary producer gives one positive time common to
all these source families. Only afterwards are the SAME primitive source
masks chosen below that time and the optional cap. The original protection,
full annular support, both critical orientations, zero values and inverse
bounds are retained, with constants before histories and operators
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_localChart_with_full_source_incidence_radii
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
    (hApξ : ∀ i, |ξ i| < aperture)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
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
    let z := ((coordinateSplit chart.index x).1, ((coordinateSplit chart.index x).2,
      (coordinateSplit chart.index ξ).2))
    ∀ j : ι,
    ∃ V : Set Param, IsOpen V ∧ IsCompact (closure V) ∧
      (∀ c ∈ closure V,
        c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T j)) (T j).family.radius) ∧
    ∃ δ > (0 : ℝ), δ ≤ (T j).family.threshold ∧
      (∀ mask : E → ℝ,
        tsupport mask ∩ sphere (0 : E) 1 ⊆ closedBall (NormedSpace.normalize ξ) α →
        ∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ y ∈ Xsrc j, ∀ c ∈ Csrc j, ∀ scale : ℝ, 0 < scale →
          scale • LeadingWave.FullModulation.phaseGradient (T j) Q y c.2 ∈
            tsupport (RegularSector.FiniteMasks.conicMask mask) → c ∈ V) ∧
    ∃ ρ > (0 : ℝ), ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ), ∃ S : ℝ, 2 ≤ S ∧
    ∃ InvBound > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z εcarrier O
      let U₀ := elapsedPhysicalBox z (εcarrier / 2) ×ˢ V
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture gap radius ⊆ O ∧
      (∀ c ∈ closure V, primaryCoordinateChange chart.index ((T j).reference.covector (0, c.2)) ∈ O) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
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
          (fullSourceJointPhase adj (curriedPhase chart.radialSection C) ((T j).fullSourcePhaseInCoordinates chart.index Q))
          ((Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D) ∧
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ (T j).fullSourcePhaseInCoordinates chart.index Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            ((T j).fullSourcePhaseInCoordinates chart.index Q) (p, w)) (κ adj p) = 0 ∧
          fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            ((T j).fullSourcePhaseInCoordinates chart.index Q) (p, κ adj p) = 0 ∧
          dist (κ adj p) (WithLp.toLp 2
            (p.2.1, gradient (fun y ↦ (T j).fullSourcePhaseInCoordinates chart.index Q y p.2.2) p.2.1)) ≤ ρ / 2 ∧
          (∀ w ∈ closure D,
            let f := fun q w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
              ((T j).fullSourcePhaseInCoordinates chart.index Q) ((p.1, q), w)
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
  let εcarrier := min (b / 8) (L / 2)
  have hεcarrier : 0 < εcarrier := lt_min (by positivity) (half_pos hL)
  have hεL : εcarrier ≤ L := (min_le_right _ _).trans (by linarith)
  have hεb : 4 * εcarrier ≤ b := by
    have hle := min_le_left (b / 8) (L / 2)
    dsimp only [εcarrier]
    linarith
  have hphysical : MapsTo (primaryCoordinateChange i).symm
      (closure (elapsedPhysicalBox z εcarrier)) (closedBall x RQ) :=
    retained_primary_physical_buffer i z hεL hrootPhys
  have hcritical (j : ι) := (T j).exists_uniform_full_source_incidence_critical_inverse_maps
    (hframe j) hξ i row col ℓ hℓ H hε hL hμ hν hroot z hεcarrier hεb hAp hgap
    (radius := radius) (hphysical.mono_right hKΩ)
    G hr hrR hR ext hextcenter hextradius hStar horder (isCompact_closedBall x RQ)
    phaseCost hphaseCost
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
        spatialPart_timeSpacePoint, hℓ, mul_one] using hApξ i
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
  have hstationary (j : ι) := hmaps j (closure (V j)) (V j) (hVK j) (hV j) subset_closure
    (fun q hq ↦ (T j).full_source_mem_phaseDomain_of_physical_buffer
      (ball_subset_closedBall (hKprimary j (hphysical hq.1))) ((hparam j q.2 hq.2).1))
    (fun c hc ↦ (hparam j c hc).2.2) (fun c hc ↦ (hparam j c hc).2.1)
  choose δs hδs hδsT margin hmargin g hg Rad hRad S hS τj hτj hτjε
    InvBound hInvBound hstationary using hstationary
  obtain ⟨α, hα, hαsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : ι ↦ (0 : ℝ)) (y := αj) hαj
  obtain ⟨τ, hτ, hτsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : ι ↦ (0 : ℝ)) (y := τj) hτj
  have hαle (j : ι) : α ≤ αj j := by simpa using (hαsmall j).le
  have hτle (j : ι) : τ ≤ τj j := by simpa using (hτsmall j).le
  refine ⟨α, hα, τ, hτ, ?_⟩
  intro cap hcapPos
  obtain ⟨src, hsrc, hsrccap, hsrca, hsrcρ, _, σ, κ, hσ, hκ, hσr, hκr,
    hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, hevolution⟩ := hcap (min cap τ) (lt_min hcapPos hτ)
  have hsrcτ : src ≤ τ := hsrccap.trans (min_le_right cap τ)
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
  refine ⟨chart, hρb, hsrcρ, hsrccap.trans (min_le_left cap τ), hsrcτ, hinterval,
    hroot, hsourceMask, evolutionTime, speedGap, rootSize, rootCost,
    ⟨hevolutionTime, hspeedGap, hrootSize, hrootCost, haR, haT, htimeDomain,
      haL, hwholeState, hevolution⟩, εcarrier, hεcarrier, hεL, hεb, ?_⟩
  dsimp only
  intro j
  obtain ⟨hO, hOc, hOK, hFO, hfreq, hbranch⟩ := hstationary j
  refine ⟨V j, hV j, hVK j, (fun c hc ↦ (hparam j c hc).1),
    min (δc j) (δs j), lt_min (hδc j) (hδs j), (min_le_left _ _).trans (hδcT j),
    ?_, margin j, hmargin j, g j, hg j, Rad j, hRad j, S j, hS j,
    InvBound j, hInvBound j, hO, hOc, hOK, hFO, hfreq, ?_⟩
  · intro mask hmask Q hQ y hy c hc scale hscale hinc
    exact hcapture j mask (hmask.trans (closedBall_subset_closedBall (hαle j))) Q
      (hQ.trans_le (min_le_left _ _)) y hy c hc scale hscale hinc
  · intro R₀ hR₀ n u ell hu Q hQ hQlow Φ C a' hC hsource' hi hbuffer hCsm hbudget
      ha'L hLD hhom hstate hphase
    obtain ⟨w, hw⟩ := hbranch R₀ hR₀ n u ell hu Q hQ
      (hQlow.trans_le (min_le_right _ _)) Φ C a' hC hsource' hi hbuffer hCsm hbudget
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

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
