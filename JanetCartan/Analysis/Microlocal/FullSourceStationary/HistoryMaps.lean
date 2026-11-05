module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.StationaryBranch
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.JointProfiles

/-!
# Actual uniform stationary maps for the original full source

Instantiate the full-parameter contraction and IFT with the actual source
incidence domain, diagonal buffers, and original history phase profiles. Both
literal orientations retain the same source and the whole enlarged integration
closure. All constants precede histories and chart witnesses. Consumer:
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
open FullSourceStationary LeadingWave.FullModulation
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)

/-- Construct jointly smooth stationary maps of the original full source in
both literal orientations on ONE interval chosen before histories, masks and
operators. The actual full-covector comparison, source root equation and
history phase jets discharge all diagonal, smoothness and contraction inputs.
The entire source/annular integration closure and its full segments stay in
the same original conic chart. No source covector is replaced by a carrier value
(`app:ch_response:eq:response-exact-phase`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_full_source_stationary_maps
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
    ∃ S : ℝ, 2 ≤ S ∧ ∃ τ > (0 : ℝ), τ ≤ ε ∧
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
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              fullSourceSignedCarrier z ε (closedBall c₀ (2 * s)) O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain ℓ C.target := by
  intro z
  obtain ⟨δ, hδ, hδT, s, hs, hparam, ρ, hρ, g, hg', Rad, hRad,
    hO, hOc, hOK, hD, hDc, hDK, hU₀, hU₀c, hU₀K, hbase, hFO, hsupport,
    _, hdiagonal⟩ := T.exists_uniform_full_source_diagonal_buffers hframe hc₀ hξ x₀ i r' c' ℓ H
      hr hL hμ hν hH hε hAp hg hℓ hApθ hKprimary hεL hrootPhysical
        (radius := radius)
  let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
  let D := retainedOpenIntegrationDomain z ε O
  let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ ball c₀ (2 * s)
  let KP := closure (elapsedPhysicalBox z ε) ×ˢ closedBall c₀ (2 * s)
  let K := fullSourceSignedCarrier z ε (closedBall c₀ (2 * s)) O
  let J := closedBall (z.1, z) b
  let X := (primaryCoordinateChange i).symm ⁻¹' ball (0 : E) T.physicalRadius
  let Ω := X ×ˢ ball c₀ (4 * s)
  have hphysical : MapsTo (primaryCoordinateChange i).symm
      (closure (elapsedPhysicalBox z ε)) (ball 0 T.physicalRadius) :=
    retained_primary_physical_buffer i z hεL (fun _ hw ↦ hKprimary (hrootPhysical hw))
  have hKP : IsCompact KP := by
    have hh := isCompact_closure_retained_physicalBox z (2 * ε)
    simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hh
    exact hh.prod (isCompact_closedBall _ _)
  have hKPU q (hq : q ∈ KP) :
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T :=
    T.full_source_mem_phaseDomain_of_physical_buffer
      (ball_subset_closedBall (hphysical hq.1))
      (hparam (closedBall_subset_closedBall (by linarith : 2 * s ≤ 4 * s) hq.2)).2
  have hKPΩ : KP ⊆ Ω := fun _ hq ↦
    ⟨hphysical hq.1, closedBall_subset_ball (by linarith : 2 * s < 4 * s) hq.2⟩
  have hU₀KP : U₀ ⊆ KP := fun _ hq ↦
    ⟨subset_closure (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε
      (subset_closure hq.1)), ball_subset_closedBall hq.2⟩
  have hgeom := fullSourceSignedCarrier_geometry z ε (isCompact_closedBall c₀ (2 * s)) hO hOc hOK
  have hK : IsCompact K := hgeom.1
  have hpos (v : FullSourcePoint d) (hv : v ∈ K) : 0 < ℓ (spatialPart v.2.snd) :=
    (fullSourceSignedCarrier_normalizes ℓ z hε hAp hg' hO hOc hOK false hv).1
  have hmap (adj : Bool) : MapsTo (ConicPhase.normalize ℓ ∘ fullSourceGraphPoint adj) K J :=
    fun _ hv ↦ closedBall_subset_closedBall hεb
      (fullSourceSignedCarrier_normalizes ℓ z hε hAp hg' hO hOc hOK adj hv).2
  have hsrc v (hv : v ∈ K) : (v.2.fst, v.1.2.2) ∈ KP := (hgeom.2 v hv).1
  have hout v (hv : v ∈ K) : v.1.2 ∈ KP := (hgeom.2 v hv).2
  obtain ⟨SP, hSP, AP, hAP, hprimary⟩ :=
    T.exists_admissible_history_full_source_phase_profiles i hKP hKPU G hr' hrR hR ext
      hextcenter hextradius hStar (Rstar := 3) (by omega) horder
  have hprofiles (adj : Bool) :=
    T.exists_admissible_history_full_source_joint_phase_profiles i adj ℓ hK
      (isCompact_closedBall _ _) hKP hpos (hmap adj) hsrc hout hKPU G hr' hrR hR ext
      hextcenter hextradius hStar (Rstar := 3) (by omega) horder hKQ phaseCost hphaseCost
  choose SF hSF AF hAF hprofile using hprofiles
  let B := fun m ↦ AF false m + AF true m
  have hB m : 0 ≤ B m := add_nonneg (hAF false m) (hAF true m)
  have hAB adj m : AF adj m ≤ B m := by
    cases adj <;> dsimp [B] <;> linarith [hAF false m, hAF true m]
  obtain ⟨τ, hτ, hτε, _, hbranch⟩ := exists_uniform_full_source_conic_stationary_branches
    U₀ hU₀ hρ hε (hAP 2) (hB 2) (hB 3)
  refine ⟨δ, hδ, hδT, s, hs, hparam, ρ, hρ, g, hg', Rad, hRad,
    max SP (max (SF false) (SF true)), hSP.trans (le_max_left _ _), τ, hτ, hτε,
    hO, hOc, hOK, hD, hDc, hDK, hU₀, hU₀c, hU₀K, hbase, hFO, hsupport, ?_⟩
  intro R₀ hR₀ n u ell hu Q hQ hQlow
  obtain ⟨hΩ, _, hφ, _, he, hmargin⟩ := hdiagonal Q hQlow
  refine ⟨hφ, he, ?_⟩
  intro Φ C a hC hsource hi hbuffer hCsm hbudget
  have hR₀P : SP ≤ R₀ := (le_max_left _ _).trans hR₀
  have hR₀F (adj : Bool) : SF adj ≤ R₀ := by
    apply le_trans _ ((le_max_right _ _).trans hR₀)
    cases adj
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hgraphs (adj : Bool) : MapsTo (fullSourceGraphPoint adj) K (domain ℓ C.target) :=
    fun v hv ↦ ⟨by simpa only [fullSourceGraphPoint] using hpos v hv, hbuffer (hmap adj hv)⟩
  obtain ⟨V, hV, hKV, hsmooth⟩ := exists_full_source_joint_phase_smooth_neighborhood ℓ C hCsm
    (T.fullSourcePhaseInCoordinates i Q) hΩ hφ hgraphs
      (fun v hv ↦ hKPΩ (hsrc v hv)) (fun v hv ↦ hKPΩ (hout v hv))
  have hdiag q (hq : q ∈ U₀) : closedBall
      (WithLp.toLp 2 (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1))
        (4 * ρ) ⊆ D := hmargin q ⟨subset_closure hq.1, ball_subset_closedBall hq.2⟩
  have hbuf q (hq : q ∈ U₀) :
      (Icc (-ε) ε ×ˢ {q}) ×ˢ closedBall
        (WithLp.toLp 2 (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1))
          (4 * ρ) ⊆ K := by
    rintro ⟨⟨t, q'⟩, w⟩ ⟨⟨ht, hq'⟩, hw⟩
    have heq : q' = q := hq'
    subst q'
    exact ⟨⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hU₀KP hq⟩,
      subset_closure (hdiag q hq hw)⟩
  have hprimary2 : ∀ q ∈ U₀, ‖iteratedFDeriv ℝ 2
      (Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) q‖ ≤ AP 2 := by
    intro q hq
    have hp := hprimary R₀ hR₀P n u ell hu Q hQ 2
    simp only [show 2 - 3 = 0 by omega, pow_zero, mul_one] at hp
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hKP
      (fun v hv ↦ (hφ.contDiffAt (hΩ.mem_nhds (hKPΩ hv))).of_le
        (by simp : (2 : ℕ∞ω) ≤ ∞)) (hU₀KP hq) le_rfl).trans hp
  have hgraph0 : ∀ q ∈ U₀, elapsedChartPoint 0 q.1
      (gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1) ∈ domain ℓ C.target := by
    intro q hq
    have hv := hbuf q hq (show ((0, q), WithLp.toLp 2
        (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1)) ∈
        (Icc (-ε) ε ×ˢ {q}) ×ˢ closedBall
          (WithLp.toLp 2 (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1))
            (4 * ρ) from
      ⟨⟨⟨by linarith, hε.le⟩, rfl⟩, mem_closedBall_self (by positivity)⟩)
    exact hgraphs false hv
  have hphase23 : ∀ adj : Bool,
      cNorm K 2 (fullSourceJointPhase adj (curriedPhase ℓ C)
        (T.fullSourcePhaseInCoordinates i Q)) ≤ B 2 ∧
      cNorm K 3 (fullSourceJointPhase adj (curriedPhase ℓ C)
        (T.fullSourcePhaseInCoordinates i Q)) ≤ B 3 := by
    intro adj
    have h2 := (hprofile adj R₀ (hR₀F adj) n u ell hu Q hQ C hbuffer hCsm hbudget 2).1
    have h3 := (hprofile adj R₀ (hR₀F adj) n u ell hu Q hQ C hbuffer hCsm hbudget 3).1
    simp only [show 2 - 3 = 0 by omega, pow_zero, mul_one] at h2 h3
    exact ⟨h2.trans (hAB adj 2), h3.trans (hAB adj 3)⟩
  obtain ⟨κ, hκ⟩ := hbranch (T.fullSourcePhaseInCoordinates i Q) Ω hΩ hφ
    (hU₀KP.trans hKPΩ) hprimary2 ℓ Φ C hC z a hsource hi hgraph0
    V K hV hK hKV hbuf hsmooth hphase23 D hdiag
  refine ⟨κ, fun adj ↦ ⟨(hκ adj).1, (hκ adj).2.1, ?_⟩⟩
  intro p hp
  obtain ⟨hκD, hstat, hdist⟩ := (hκ adj).2.2 p hp
  refine ⟨hκD, hstat, hdist, ?_⟩
  intro w hw u hu v hv
  have htime : |p.1| ≤ 2 * ε := abs_le.mpr
    ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  have hseg := (fullSourceSignedCarrier_segments z ε hOc htime (hU₀KP hp.2)
    (subset_closure hκD) hw u hu v hv).1
  exact ⟨hseg, fun o ↦ hgraphs o hseg⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
