module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.StationaryInverse
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.StationaryValue

/-!
# Full-source critical maps with uniform averaged-Hessian inverse bounds

Construct both critical maps for the original full source, with zero value,
all segment containments and inverse bounds on one common interval. The
root/chart differential inputs are literal outputs of the retained-evolution
producer. All remaining geometric and analytic source inputs are discharged
by the actual full-source domain and history estimates. Consumer:
`app:ch_response:eq:direct-envelope-profile`.
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
open FullSourceStationary
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)

/-- Actual critical maps with zero critical value and quantitative averaged
Hessian inverses for BOTH literal orientations of the ORIGINAL full source.
The source phase is exactly `T.fullSourcePhaseInCoordinates i Q`, anchored at
`T.reference.covector (0,c₀.2)`; every independent covector parameter and the
full original annulus are retained. The one parameter cap and signed interval
precede histories and operators. The additional root homogeneity, endpoint
state/clock and phase differential are the original primitive outputs of
`exists_uniform_supported_conic_pencilAmplitudes_with_retained_evolution`.
No successful-stationary-map or inverse-bound hypothesis is introduced
(`app:ch_response:eq:response-exact-phase`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_full_source_critical_inverse_maps
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
      ∀ rootDomain : Set (RootState (Euclidean d)),
        a ≤ L → closedBall z L ⊆ rootDomain →
        (∀ w ∈ rootDomain, ∀ t : ℝ, 0 < t →
          fieldRoot (coordinateSplit i) Q.1 H (w.1, (w.2.1, t • w.2.2)) =
            t * fieldRoot (coordinateSplit i) Q.1 H w) →
        (∀ v ∈ C.target, twoTimeState Φ (C.symm v) ∈ rootDomain ∧
          (twoTimeState Φ (C.symm v)).1 = v.1) →
        (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C)
          (twoTimePhaseDifferential (fieldRoot (coordinateSplit i) Q.1 H) Φ C v) v) →
      ∃ κ : Bool → Par → W, ∀ adj : Bool,
        ContDiffOn ℝ ∞
          (fullSourceJointPhase adj (curriedPhase ℓ C)
            (T.fullSourcePhaseInCoordinates i Q))
          ((Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D) ∧
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
            (T.fullSourcePhaseInCoordinates i Q) (p, w)) (κ adj p) = 0 ∧
          fullSourceJointPhase adj (curriedPhase ℓ C)
            (T.fullSourcePhaseInCoordinates i Q) (p, κ adj p) = 0 ∧
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
    S, hS, τ, hτ, hτε, M, hM, hO, hOc, hOK, hD, hDc, hDK, hU₀, hU₀c, hU₀K,
    hbase, hFO, hsupport, hbranches⟩ :=
    T.exists_uniform_full_source_stationary_inverse_maps hframe hc₀ hξ x₀ i r' c' ℓ H
      hr hL hμ hν hH hε hAp hg hεb hℓ hApθ hKprimary hεL hrootPhysical
      G hr' hrR hR ext hextcenter hextradius hStar horder hKQ phaseCost hphaseCost
      (radius := radius)
  let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
  let D := retainedOpenIntegrationDomain z ε O
  let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ ball c₀ (2 * s)
  let X := (primaryCoordinateChange i).symm ⁻¹' ball (0 : E) T.physicalRadius
  let Ω := X ×ˢ ball c₀ (4 * s)
  let K := fullSourceSignedCarrier z ε (closedBall c₀ (2 * s)) O
  have hΩ : IsOpen Ω :=
    (isOpen_ball.preimage (primaryCoordinateChange i).symm.continuous).prod isOpen_ball
  have hphysical : MapsTo (primaryCoordinateChange i).symm
      (closure (elapsedPhysicalBox z ε)) (ball 0 T.physicalRadius) :=
    retained_primary_physical_buffer i z hεL (fun _ hw ↦ hKprimary (hrootPhysical hw))
  have hKPΩ : closure (elapsedPhysicalBox z ε) ×ˢ closedBall c₀ (2 * s) ⊆ Ω :=
    fun _ hq ↦ ⟨hphysical hq.1, closedBall_subset_ball (by linarith : 2 * s < 4 * s) hq.2⟩
  have hUΩ : U₀ ⊆ Ω := fun _ hq ↦ hKPΩ
    ⟨subset_closure (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε
      (subset_closure hq.1)), ball_subset_closedBall hq.2⟩
  have hgeom := fullSourceSignedCarrier_geometry z ε (isCompact_closedBall c₀ (2 * s)) hO hOc hOK
  refine ⟨δ, hδ, hδT, s, hs, hparam, ρ, hρ, g, hg', Rad, hRad,
    S, hS, τ, hτ, hτε, M, hM, hO, hOc, hOK, hD, hDc, hDK, hU₀, hU₀c, hU₀K,
    hbase, hFO, hsupport, ?_⟩
  intro R₀ hR₀ n u ell hu Q hQ hQlow
  obtain ⟨hφ, he, hbranch⟩ := hbranches R₀ hR₀ n u ell hu Q hQ hQlow
  refine ⟨hφ, he, ?_⟩
  intro Φ C a hC hsource hi hbuffer hCsm hbudget rootDomain haL hLD hhom hstate hphase
  obtain ⟨κ, hκ⟩ := hbranch Φ C a hC hsource hi hbuffer hCsm hbudget
  have heΩ : ∀ q ∈ Ω, rootSuspension (fieldRoot (coordinateSplit i) Q.1 H)
      (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1) = 0 :=
    fun q hq ↦ he q ⟨hq.1, ball_subset_closedBall hq.2⟩
  have hκK adj p (hp : p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀) : (p, κ adj p) ∈ K := by
    have hh := ((hκ adj).2.2 p hp).2.2.2.2 (κ adj p)
      (subset_closure ((hκ adj).2.2 p hp).1) p.1 right_mem_uIcc 0 (by simp)
    simpa only [zero_smul, add_zero, Prod.eta] using hh.1
  have hsrc adj p (hp : p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀) :
      ((κ adj p).fst, p.2.2) ∈ Ω := hKPΩ ((hgeom.2 _ (hκK adj p hp)).1)
  have hgraphs adj : MapsTo (fullSourceGraphPoint adj) K (domain ℓ C.target) := by
    intro v hv
    have hh := fullSourceSignedCarrier_normalizes ℓ z hε hAp hg' hO hOc hOK adj hv
    exact ⟨by simpa only [fullSourceGraphPoint] using hh.1,
      hbuffer (closedBall_subset_closedBall hεb hh.2)⟩
  have hvalue := full_source_uniform_stationary_value_eq_zero ℓ hhom hC hsource haL hLD hi
    hstate hCsm hphase (T.fullSourcePhaseInCoordinates i Q) hΩ hφ heΩ hU₀ hUΩ hτ κ
    (fun adj ↦ (hκ adj).1) (fun adj ↦ (hκ adj).2.1)
    (fun adj p hp ↦ ((hκ adj).2.2 p hp).2.1) hsrc
    (fun adj p hp ↦ hgraphs adj (hκK adj p hp))
  have hproduct : ((Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D) ⊆ K := by
    rintro ⟨⟨t, q⟩, w⟩ ⟨⟨ht, hq⟩, hw⟩
    exact ⟨⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      ⟨subset_closure (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε
        (subset_closure hq.1)), ball_subset_closedBall hq.2⟩⟩, subset_closure hw⟩
  obtain ⟨V, _, hKV, hsmooth⟩ := exists_full_source_joint_phase_smooth_neighborhood ℓ C hCsm
    (T.fullSourcePhaseInCoordinates i Q) hΩ hφ hgraphs
    (fun v hv ↦ hKPΩ (hgeom.2 v hv).1) (fun v hv ↦ hKPΩ (hgeom.2 v hv).2)
  refine ⟨κ, fun adj ↦ ⟨(hsmooth adj).mono (hproduct.trans hKV),
    (hκ adj).1, (hκ adj).2.1, ?_⟩⟩
  intro p hp
  obtain ⟨hκD, hstat, hdist, hinverse, hseg⟩ := (hκ adj).2.2 p hp
  exact ⟨hκD, hstat, hvalue adj p hp, hdist, hinverse, hseg⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
