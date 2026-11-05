module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.ProtectedSourceCap
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.FullSourceRegularity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.ProtectionCertificates.LocalChart
public import JanetCartan.Analysis.Microlocal.FullSourceStationary

/-!
# Protected charts for the original full source parameters

Choose the root and protected evolution geometry once, apply the actual
history stationary/Hessian producer to that root, and only then construct
the source masks. Every chart projection and protection certificate belongs
to the same returned chart. The finite selector can subsequently choose its
angular and physical cover. Consumer: `app:ch_response:eq:fixed-factor-transfer`
and the full elapsed interval in `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ConstructedCarrierJets
open ResponseTransfer.RetainedFactors ResponseTransfer.DirectEvolution
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles ArbitraryAccuracy
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.RootFamily
open EvolutionIntegral.KernelIdentification RegularSector.Characteristic.AmplitudeBounds
open FullSourceStationary
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.UniformAmplitudes
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)

/-- Construct the protected chart at the literal frozen covector of an
original full source. Its source-parameter neighborhood and stationary radius
are chosen before the optional common mask cap. Every later cap yields masks
for this same root/evolution, with zero critical value and inverse-Hessian
bounds on the complete elapsed interval in both orientations. This permits
finite selection on the UNCHANGED compact full parameter support, followed by
one common cap, without choosing a replacement primary patch
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_localChart_with_full_source_stationary_radius
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {c₀ : Param}
    (hc₀ : c₀.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hKprimary : closedBall x RQ ⊆ ball 0 T.physicalRadius)
    {M aperture gap radius : ℝ} (hM : 0 ≤ M)
    (hAp : 0 < aperture) (hgap : 0 < gap)
    (hApξ : ∀ i, |(T.reference.covector (0, c₀.2)) i| < aperture)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    ∃ s > (0 : ℝ), ∃ τ > (0 : ℝ), ∀ cap > (0 : ℝ),
    ∃ chart : LocalChart Ω x RQ (cubeStress (d + 1)) (T.reference.covector (0, c₀.2)) M,
      chart.bufferRadius ≤ chart.targetRadius ∧
      chart.maskRadius ≤ chart.bufferRadius / 4 ∧ chart.maskRadius ≤ cap ∧
      RootBuffer chart.index chart.row chart.col (cubeStress (d + 1)) (T.reference.covector (0, c₀.2))
        chart.root chart.coefficientRadius chart.rootRadius chart.minorGap chart.transportGap ∧
      MapsTo (rootPhysicalPosition (coordinateSplit chart.index)) (tsupport chart.sourceMask)
        (closedBall x RQ) ∧
    ∃ evolutionTime speedGap rootSize rootCost,
      LocalProtectionCertificate chart evolutionTime speedGap rootSize rootCost ∧
    ∃ εcarrier > (0 : ℝ), εcarrier ≤ chart.rootRadius ∧
      4 * εcarrier ≤ chart.targetRadius ∧
    let z := ((coordinateSplit chart.index x).1, ((coordinateSplit chart.index x).2,
      (coordinateSplit chart.index (T.reference.covector (0, c₀.2))).2))
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      closedBall c₀ (4 * s) ⊆ univ ×ˢ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius ∧
    ∃ ρ > (0 : ℝ), ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ),
    ∃ S : ℝ, 2 ≤ S ∧ τ ≤ εcarrier ∧
      chart.maskRadius ≤ τ ∧
      Icc (0 : ℝ) (3 * chart.maskRadius / 4) ⊆ Ioo (-2 * τ) (2 * τ) ∧
    ∃ InvBound > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z εcarrier O
      let U₀ := elapsedPhysicalBox z (εcarrier / 2) ×ˢ ball c₀ (2 * s)
      let X := (primaryCoordinateChange chart.index).symm ⁻¹' ball (0 : E) T.physicalRadius
      let Ω := X ×ˢ ball c₀ (4 * s)
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      IsOpen D ∧ Convex ℝ D ∧ IsCompact (closure D) ∧
      IsOpen U₀ ∧ Convex ℝ U₀ ∧ IsCompact (closure U₀) ∧
      (primaryCoordinateChange chart.index x, c₀) ∈ U₀ ∧
      retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture gap radius ⊆ O ∧
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E ⁻¹'
        (closure (elapsedPhysicalBox z (εcarrier / 2)) ×ˢ
          retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture gap radius)) ⊆ D ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ContDiffOn ℝ ∞ (fun q ↦ T.fullSourcePhaseInCoordinates chart.index Q q.1 q.2) Ω ∧
        (∀ q ∈ X ×ˢ closedBall c₀ (4 * s),
          rootSuspension (fieldRoot (coordinateSplit chart.index) Q.1 chart.root)
            (q.1, gradient (fun x ↦ T.fullSourcePhaseInCoordinates chart.index Q x q.2) q.1) = 0) ∧
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC) (a : ℝ),
        (C : TC → TC) = twoTimeProjection Φ →
        C.source = ball (z.1, z) a → (∀ v ∈ ball z a, Φ (v, 0) = v) →
        closedBall (z.1, z) chart.targetRadius ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m, cNorm (closedBall (z.1, z) chart.targetRadius) m (twoTimePhase C) ≤
          chart.phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q.1)) →
      ∀ rootDomain : Set (RootState (Euclidean d)),
        a ≤ chart.rootRadius →
        closedBall z chart.rootRadius ⊆ rootDomain →
        (∀ w ∈ rootDomain, ∀ t : ℝ, 0 < t →
          fieldRoot (coordinateSplit chart.index) Q.1 chart.root (w.1, (w.2.1, t • w.2.2)) =
            t * fieldRoot (coordinateSplit chart.index) Q.1 chart.root w) →
        (∀ v ∈ C.target, twoTimeState Φ (C.symm v) ∈ rootDomain ∧
          (twoTimeState Φ (C.symm v)).1 = v.1) →
        (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C)
          (twoTimePhaseDifferential (fieldRoot (coordinateSplit chart.index) Q.1 chart.root) Φ C v) v) →
      ∃ κ : Bool → Par → W, ∀ adj : Bool,
        ContDiffOn ℝ ∞
          (fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            (T.fullSourcePhaseInCoordinates chart.index Q))
          ((Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D) ∧
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates chart.index Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            (T.fullSourcePhaseInCoordinates chart.index Q) (p, w)) (κ adj p) = 0 ∧
          fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            (T.fullSourcePhaseInCoordinates chart.index Q) (p, κ adj p) = 0 ∧
          dist (κ adj p) (WithLp.toLp 2
            (p.2.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates chart.index Q y p.2.2) p.2.1)) ≤ ρ / 2 ∧
          (∀ w ∈ closure D,
            let f := fun q w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
              (T.fullSourcePhaseInCoordinates chart.index Q) ((p.1, q), w)
            IsUnit (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w) ∧
              ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w)‖ ≤ InvBound) ∧
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              fullSourceSignedCarrier z εcarrier (closedBall c₀ (2 * s)) O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain chart.radialSection C.target := by
  obtain ⟨hξ, hp, hreg⟩ := T.full_source_frozen_covector_regular hc₀
  obtain ⟨row, col, hm⟩ := exists_nonzero_adjugate_entry_of_regular
    (cubeStress (d + 1)) (T.reference.covector (0, c₀.2)) hreg
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    hρb, μ, hμ, ν, hν, phaseCost, hphaseCost, rootCost, hrootCost,
    evolutionTime, hevolutionTime, speedGap, hspeedGap, rootSize, hrootSize,
    haR, haT, htimeDomain, hℓ, hroot, haL, hrootPhys, hwholeState, hcap⟩ :=
    exists_protected_conic_pencilAmplitudes_below_source_cap
      hΩ x hRQ hKΩ (cubeStress (d + 1)) (T.reference.covector (0, c₀.2)) row col hξ hp hreg hm hM
  let εcarrier := min (b / 8) (L / 2)
  have hεcarrier : 0 < εcarrier := lt_min (by positivity) (half_pos hL)
  have hεL : εcarrier ≤ L := (min_le_right _ _).trans (by linarith)
  have hεb : 4 * εcarrier ≤ b := by
    have hle := min_le_left (b / 8) (L / 2)
    dsimp only [εcarrier]
    linarith
  obtain ⟨δ, hδ, hδT, s, hs, hparam, margin, hmargin, g, hg, Rad, hRad,
    S, hS, τ, hτ, hτε, InvBound, hInvBound, hstationary⟩ :=
    T.exists_uniform_full_source_critical_inverse_maps hframe hc₀ hξ x
      i row col ℓ H hε hL hμ hν hroot hεcarrier hAp hgap (radius := radius)
      hεb hℓ (hApξ i) hKprimary hεL hrootPhys G hr hrR hR ext hextcenter
      hextradius hStar horder (isCompact_closedBall x RQ) phaseCost hphaseCost
  refine ⟨s, hs, τ, hτ, ?_⟩
  intro cap hcapPos
  obtain ⟨src, hsrc, hsrccap, hsrca, hsrcρ, hslab, σ, κ, hσ, hκ, hσr, hκr,
    hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, hevolution⟩ := hcap (min cap τ) (lt_min hcapPos hτ)
  have hsrcτ := hsrccap.trans (min_le_right cap τ)
  let chart : LocalChart Ω x RQ (cubeStress (d + 1)) (T.reference.covector (0, c₀.2)) M :=
    ⟨i, row, col, hm, ℓ, H, ε, L, a, b, ρ, ρo, src, μ, ν,
      phaseCost, σ, κ, hε, hL, ha, hb, hρ, hρo, hsrc, hsrca, hμ, hν,
      hphaseCost, hℓ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ,
      hevolution.toUniformChartEvolution⟩
  have hsource : MapsTo (rootPhysicalPosition (coordinateSplit i)) (tsupport σ)
      (closedBall x RQ) := by
    intro w hw
    exact hrootPhys (closedBall_subset_closedBall (by linarith : src / 2 ≤ L)
      (ball_subset_closedBall (hsσ hw)))
  have hinterval : Icc (0 : ℝ) (3 * src / 4) ⊆ Ioo (-2 * τ) (2 * τ) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨chart, hρb, hsrcρ, hsrccap.trans (min_le_left cap τ), hroot, hsource,
    evolutionTime, speedGap, rootSize, rootCost,
    ⟨hevolutionTime, hspeedGap, hrootSize, hrootCost, haR, haT, htimeDomain,
      haL, hwholeState, hevolution⟩,
    εcarrier, hεcarrier, hεL, hεb,
    δ, hδ, hδT, hparam, margin, hmargin, g, hg, Rad, hRad,
    S, hS, hτε, hsrcτ, hinterval, InvBound, hInvBound, hstationary⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
