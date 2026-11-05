module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.HistoryMaps
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.HistoryHessian

/-!
# Common stationary maps and averaged-Hessian inverses for the full source

The full-source stationary maps and actual history Hessian stability are
combined before choosing source masks. Both orientations retain the original
full phase, all independent source parameters, and the whole enlarged
integration closure. Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
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
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)

/-- Actual uniform stationary maps and inverse bounds on their ENTIRE
supported segments for the original full source, in both literal orientations.
One parameter cap, coefficient threshold and elapsed interval precede histories,
source masks and operators. The actual history jets and explicit zero-time
block inverse supply all analytic bounds. This realizes the full-source
stationary/inverse specification with its original physical and annular sets
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_full_source_stationary_inverse_maps
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {c₀ : Param}
    (hc₀ : c₀.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    (hξ : T.reference.covector (0, c₀.2) ≠ 0) (x₀ : E) (i r' c' : Fin (d + 1))
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (H : Coeff × Euclidean d → ℝ) {rootRadius L μ ν : ℝ}
    (hr : 0 < rootRadius) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i r' c' (cubeStress (d + 1)) (T.reference.covector (0, c₀.2)) H rootRadius L μ ν)
    {ε aperture gap radius b : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < gap)
    (hεb : 4 * ε ≤ b)
    (hℓ : ℓ (coordinateSplit i (T.reference.covector (0, c₀.2))).2 = 1)
    (hApθ : |T.reference.covector (0, c₀.2) i| < aperture)
    {RQ : ℝ} (hKprimary : closedBall x₀ RQ ⊆ ball 0 T.physicalRadius)
    (hεL : ε ≤ L)
    (hrootPhysical : MapsTo (rootPhysicalPosition (coordinateSplit i))
      (closedBall
        ((coordinateSplit i x₀).1, ((coordinateSplit i x₀).2,
          (coordinateSplit i (T.reference.covector (0, c₀.2))).2)) L) (closedBall x₀ RQ))
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr' : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin)
    {KQ : Set E} (hKQ : IsCompact KQ)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    let z := ((coordinateSplit i x₀).1, ((coordinateSplit i x₀).2,
      (coordinateSplit i (T.reference.covector (0, c₀.2))).2))
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ s > (0 : ℝ),
      closedBall c₀ (4 * s) ⊆
        univ ×ˢ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius ∧
    ∃ ρ > (0 : ℝ), ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ),
    ∃ S : ℝ, 2 ≤ S ∧ ∃ τ > (0 : ℝ), τ ≤ ε ∧ ∃ M > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z ε O
      let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ ball c₀ (2 * s)
      let X := (primaryCoordinateChange i).symm ⁻¹' ball (0 : E) T.physicalRadius
      let Ω := X ×ˢ ball c₀ (4 * s)
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      IsOpen D ∧ Convex ℝ D ∧ IsCompact (closure D) ∧
      IsOpen U₀ ∧ Convex ℝ U₀ ∧ IsCompact (closure U₀) ∧
      (primaryCoordinateChange i x₀, c₀) ∈ U₀ ∧
      retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius ⊆ O ∧
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E ⁻¹'
        (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ
          retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius)) ⊆ D ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ContDiffOn ℝ ∞ (fun q ↦ T.fullSourcePhaseInCoordinates i Q q.1 q.2) Ω ∧
        (∀ q ∈ X ×ˢ closedBall c₀ (4 * s),
          rootSuspension (fieldRoot (coordinateSplit i) Q.1 H)
            (q.1, gradient (fun x ↦ T.fullSourcePhaseInCoordinates i Q x q.2) q.1) = 0) ∧
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC) (a : ℝ),
        (C : TC → TC) = twoTimeProjection Φ →
        C.source = ball (z.1, z) a → (∀ v ∈ ball z a, Φ (v, 0) = v) →
        closedBall (z.1, z) b ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
          phaseCost m * (1 + cNorm KQ (m + 1) Q.1)) →
      ∃ κ : Bool → Par → W, ∀ adj : Bool,
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
            (T.fullSourcePhaseInCoordinates i Q) (p, w)) (κ adj p) = 0 ∧
          dist (κ adj p) (WithLp.toLp 2
            (p.2.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y p.2.2) p.2.1)) ≤ ρ / 2 ∧
          (∀ w ∈ closure D,
            let f := fun q w ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
              (T.fullSourcePhaseInCoordinates i Q) ((p.1, q), w)
            IsUnit (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w) ∧
              ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w)‖ ≤ M) ∧
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              fullSourceSignedCarrier z ε (closedBall c₀ (2 * s)) O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain ℓ C.target := by
  intro z
  obtain ⟨δ, hδ, hδT, s, hs, hparam, ρ, hρ, g, hg', Rad, hRad,
    Scrit, hScrit, τcrit, hτcrit, hτcritε,
    hO, hOc, hOK, hD, hDc, hDK, hU₀, hU₀c, hU₀K, hbase, hFO, hsupport,
    hbranch⟩ := T.exists_uniform_full_source_stationary_maps hframe hc₀ hξ x₀
      i r' c' ℓ H hr hL hμ hν hH hε hAp hg hεb hℓ hApθ hKprimary hεL
      hrootPhysical G hr' hrR hR ext hextcenter hextradius hStar horder hKQ phaseCost hphaseCost
  let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
  let D := retainedOpenIntegrationDomain z ε O
  let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ ball c₀ (2 * s)
  let KP := closure (elapsedPhysicalBox z ε) ×ˢ closedBall c₀ (2 * s)
  have hphysical : MapsTo (primaryCoordinateChange i).symm
      (closure (elapsedPhysicalBox z ε)) (ball 0 T.physicalRadius) :=
    retained_primary_physical_buffer i z hεL (fun _ hw ↦ hKprimary (hrootPhysical hw))
  have hKP q (hq : q ∈ KP) :
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T :=
    T.full_source_mem_phaseDomain_of_physical_buffer
      (ball_subset_closedBall (hphysical hq.1))
      (hparam (closedBall_subset_closedBall (by linarith : 2 * s ≤ 4 * s) hq.2)).2
  have hU₀KP : U₀ ⊆ KP := fun _ hq ↦
    ⟨subset_closure (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε
      (subset_closure hq.1)), ball_subset_closedBall hq.2⟩
  obtain ⟨SI, hSI, M, hM, τI, hτI, hτIε, inverseVariation, _hVariation, hinverse⟩ :=
    T.exists_admissible_history_full_source_hessian_inverse_stability
      i ℓ z hε hεb hAp hg' (isCompact_closedBall c₀ (2 * s)) hO hOc hOK hKP
      G hr' hrR hR ext hextcenter hextradius hStar horder hKQ phaseCost hphaseCost
  let τ := min τcrit τI / 2
  have hτ : 0 < τ := half_pos (lt_min hτcrit hτI)
  have hτcrit' : 2 * τ ≤ τcrit := by
    dsimp [τ]; linarith [min_le_left τcrit τI]
  have hτI' : 2 * τ ≤ τI := by
    dsimp [τ]; linarith [min_le_right τcrit τI]
  let S := max Scrit SI
  have hScrit' : Scrit ≤ S := le_max_left _ _
  have hSI' : SI ≤ S := le_max_right _ _
  refine ⟨δ, hδ, hδT, s, hs, hparam, ρ, hρ, g, hg', Rad, hRad,
    S, hScrit.trans hScrit', τ, hτ, by linarith, M, hM,
    hO, hOc, hOK, hD, hDc, hDK, hU₀, hU₀c, hU₀K, hbase, hFO, hsupport, ?_⟩
  intro R₀ hR₀ n u ell hu Q hQ hQlow
  obtain ⟨hφ, he, hmaps⟩ := hbranch R₀ (hScrit'.trans hR₀) n u ell hu Q hQ hQlow
  refine ⟨hφ, he, ?_⟩
  intro Φ C a hC hsource hi hbuffer hCsm hbudget
  obtain ⟨κ, hκ⟩ := hmaps Φ C a hC hsource hi hbuffer hCsm hbudget
  have hmono : Ioo (-2 * τ) (2 * τ) ×ˢ U₀ ⊆ Ioo (-2 * τcrit) (2 * τcrit) ×ˢ U₀ := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩
  refine ⟨κ, fun adj ↦ ⟨(hκ adj).1.mono hmono, (hκ adj).2.1, ?_⟩⟩
  intro p hp
  obtain ⟨hκD, hstat, hdist, hseg⟩ := (hκ adj).2.2 p (hmono hp)
  refine ⟨hκD, hstat, hdist, ?_, hseg⟩
  intro w hw
  have ht : |p.1| ≤ τI := abs_le.mpr
    ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  have hh := hinverse R₀ (hSI'.trans hR₀) n u ell hu Q hQ
    Φ C a hC hsource hi hbuffer hCsm hbudget adj p.1 ht p.2 (hU₀KP hp.2)
      (κ adj p) (subset_closure hκD) w hw
  exact ⟨hh.1, hh.2.1⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
