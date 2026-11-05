module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CompactDiagonalMargins
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CompactAnnularBuffer
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.StationaryBranch
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.HistoryHessian

/-!
# Actual stationary maps on compact source-incidence sets

A fixed solver chart can meet several original source labels and radial values.
The full-source parameter set is retained as supplied. Its compact frequency
image determines one enlarged annulus, and the original momentum comparison
produces uniform diagonal margins. Apply the existing full-parameter contraction
and actual history profiles, then the actual averaged-Hessian producer to the
SAME maps. No source is replaced by a patch centered at the solver covector.
Consumer: finite same-family stationary/source-radius selection for
`app:ch_response:eq:fixed-factor-transfer` and
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
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)

/-- Construct the actual stationary maps and inverse averaged-Hessian
bounds for every full source in a supplied compact angular incidence set.
The root-chart center and the source labels are independent; no equality
between them is required. The original source parameters, full annular carrier,
both orientations and every integration segment are retained. Only geometric
source-domain/cone containments and the original chart's phase budget occur
as inputs. All constants precede histories and chart/operator witnesses.
Zero critical value and the finite mask-incidence selection remain downstream
obligations (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_full_source_incidence_stationary_inverse_maps
    (i : Fin (d + 1)) (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε b aperture gap radius : ℝ} (hε : 0 < ε) (hεb : 4 * ε ≤ b)
    (hAp : 0 < aperture) (hgap : 0 < gap)
    {A V : Set Param} (hA : IsCompact A) (hV : IsOpen V) (hVA : V ⊆ A)
    (hprimary : ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    (hfrequency : ∀ c ∈ A,
      primaryCoordinateChange i (T.reference.covector (0, c.2)) ∈
        fullAngularCone ℓ z.2.2 (ε / 2) aperture)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin)
    {KQ : Set E} (hKQ : IsCompact KQ)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ ρ > (0 : ℝ),
    ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ), ∃ S : ℝ, 2 ≤ S ∧
    ∃ τ > (0 : ℝ), τ ≤ ε ∧ ∃ InvBound > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z ε O
      let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ V
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius ⊆ O ∧
      (∀ c ∈ A, primaryCoordinateChange i (T.reference.covector (0, c.2)) ∈ O) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC) (a : ℝ),
        (C : TC → TC) = twoTimeProjection Φ →
        C.source = ball (z.1, z) a → (∀ v ∈ ball z a, Φ (v, 0) = v) →
        closedBall (z.1, z) b ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
          phaseCost m * (1 + cNorm KQ (m + 1) Q.1)) →
      ∃ κ : Bool → Par → W, ∀ adj : Bool,
        ContDiffOn ℝ ∞
          (fullSourceJointPhase adj (curriedPhase ℓ C) (T.fullSourcePhaseInCoordinates i Q))
          ((Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D) ∧
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
              ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w)‖ ≤ InvBound) ∧
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈ fullSourceSignedCarrier z ε A O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain ℓ C.target := by
  let coord := primaryCoordinateChange i
  let pull : E × Param → E × Param := fun q ↦ (coord.symm q.1, q.2)
  have hpull : Continuous pull := (coord.symm.continuous.comp continuous_fst).prodMk continuous_snd
  have hphysical := isCompact_closure_retained_physicalBox z (2 * ε)
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hphysical
  let KP := closure (elapsedPhysicalBox z ε) ×ˢ A
  have hKP : IsCompact KP := hphysical.prod hA
  let freq : Param → E := fun c ↦ coord (T.reference.covector (0, c.2))
  let q₀ : E := timeSpacePoint z.1 z.2.1
  have hq₀ : q₀ ∈ closure (elapsedPhysicalBox z ε) := subset_closure (by
    simp only [q₀, elapsedPhysicalBox, mem_ofPred_eq, timeSpacePoint_time, spatialPart_timeSpacePoint]
    exact ⟨mem_ball_self hε, mem_ball_self hε⟩)
  have hfreq₀ : ContinuousOn (fun c : Param ↦ T.reference.covector (0, c.2)) A :=
    T.continuousOn_frozen_full_source_pair.snd.comp
      (f := fun c : Param ↦ (coord.symm q₀, c))
      (continuousOn_const.prodMk continuousOn_id) (fun c hc ↦ hprimary (q₀, c) ⟨hq₀, hc⟩)
  have hfreq : ContinuousOn freq A := coord.continuous.comp_continuousOn hfreq₀
  obtain ⟨g, hg, Rad, hRad, hO, hOc, hOK, hFO, hfreqO, _⟩ :=
    exists_retained_open_annular_frequency_buffer_of_compact ℓ z.2.2 (half_pos hε) hAp hgap
      (radius := radius) (hA.image_of_continuousOn hfreq)
      (by rintro _ ⟨c, hc, rfl⟩; exact hfrequency c hc)
  let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
  let D := retainedOpenIntegrationDomain z ε O
  let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ V
  have hU₀ : IsOpen U₀ := (isOpen_elapsedPhysicalBox _ _).prod hV
  have hU₀KP : U₀ ⊆ KP := fun q hq ↦
    ⟨subset_closure (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε
      (subset_closure hq.1)), hVA hq.2⟩
  let J := pull '' (closure (elapsedPhysicalBox z (ε / 2)) ×ˢ A)
  have hJ : IsCompact J :=
    ((isCompact_closure_retained_physicalBox z ε).prod hA).image hpull
  have hJT : J ⊆ LeadingWave.FullModulation.domain T := by
    rintro w ⟨q, hq, rfl⟩
    exact hprimary q ⟨subset_closure
      (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε hq.1), hq.2⟩
  obtain ⟨δ, hδ, hδT, ρ, hρ, hmargin⟩ :=
    T.exists_uniform_full_source_compact_diagonal_margin i z hε hJ hJT
      (by rintro w ⟨q, hq, rfl⟩; simpa only [pull, coord, ContinuousLinearEquiv.apply_symm_apply] using hq.1)
      hO (by rintro w ⟨q, hq, rfl⟩; exact hfreqO (mem_image_of_mem freq hq.2))
  let K := fullSourceSignedCarrier z ε A O
  have hgeom := fullSourceSignedCarrier_geometry z ε hA hO hOc hOK
  have hK : IsCompact K := hgeom.1
  have hpos v (hv : v ∈ K) := (fullSourceSignedCarrier_normalizes ℓ z hε hAp hg hO hOc hOK false hv).1
  have hmap (adj : Bool) : MapsTo (ConicPhase.normalize ℓ ∘ fullSourceGraphPoint adj) K
      (closedBall (z.1, z) b) := fun v hv ↦ closedBall_subset_closedBall hεb
    (fullSourceSignedCarrier_normalizes ℓ z hε hAp hg hO hOc hOK adj hv).2
  obtain ⟨SP, hSP, AP, hAP, hprimaryBound⟩ :=
    T.exists_admissible_history_full_source_phase_profiles i hKP hprimary G hr hrR hR ext
      hextcenter hextradius hStar (Rstar := 3) (by omega) horder
  have hprofiles (adj : Bool) :=
    T.exists_admissible_history_full_source_joint_phase_profiles i adj ℓ hK
      (isCompact_closedBall _ _) hKP hpos (hmap adj)
      (fun v hv ↦ (hgeom.2 v hv).1) (fun v hv ↦ (hgeom.2 v hv).2) hprimary
      G hr hrR hR ext hextcenter hextradius hStar (Rstar := 3) (by omega) horder hKQ phaseCost hphaseCost
  choose SF hSF AF hAF hprofile using hprofiles
  let B := fun m ↦ AF false m + AF true m
  have hB m : 0 ≤ B m := add_nonneg (hAF false m) (hAF true m)
  have hAB adj m : AF adj m ≤ B m := by
    cases adj <;> dsimp [B] <;> linarith [hAF false m, hAF true m]
  obtain ⟨τ₀, hτ₀, hτ₀ε, _, hbranch⟩ := exists_uniform_full_source_conic_stationary_branches
    U₀ hU₀ hρ hε (hAP 2) (hB 2) (hB 3)
  obtain ⟨SI, hSI, InvBound, hInvBound, τI, hτI, _, inverseVariation, _, hinverse⟩ :=
    T.exists_admissible_history_full_source_hessian_inverse_stability i ℓ z hε hεb hAp hg
      hA hO hOc hOK hprimary G hr hrR hR ext hextcenter hextradius hStar horder
      hKQ phaseCost hphaseCost
  let τ := min τ₀ τI / 2
  have hτ : 0 < τ := half_pos (lt_min hτ₀ hτI)
  have hτ₀' : 2 * τ ≤ τ₀ := by dsimp [τ]; linarith [min_le_left τ₀ τI]
  have hτI' : 2 * τ ≤ τI := by dsimp [τ]; linarith [min_le_right τ₀ τI]
  have hτε : τ ≤ ε := (by linarith : τ ≤ τ₀).trans hτ₀ε
  have hinterval : Ioo (-2 * τ) (2 * τ) ×ˢ U₀ ⊆ Ioo (-2 * τ₀) (2 * τ₀) ×ˢ U₀ := by
    rintro ⟨t, q⟩ ⟨ht, hq⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hq⟩
  refine ⟨δ, hδ, hδT, ρ, hρ, g, hg, Rad, hRad,
    max (max SP (max (SF false) (SF true))) SI,
    hSI.trans (le_max_right _ _), τ, hτ, hτε, InvBound, hInvBound,
    hO, hOc, hOK, hFO, (fun c hc ↦ hfreqO (mem_image_of_mem freq hc)), ?_⟩
  intro R₀ hR₀ n u ell hu Q hQ hQlow Φ C a hC hsource hi hbuffer hCsm hbudget
  let Ω : Set (E × Param) := {q | (coord.symm q.1, q.2.2) ∈ phaseDomain T}
  have hΩ : IsOpen Ω := isOpen_ball.preimage
    ((coord.symm.continuous.comp continuous_fst).prodMk continuous_snd.snd)
  have hφ := T.fullSourcePhaseInCoordinates_smooth i Q (Ω := Ω) (fun _ hq ↦ hq)
  have hKPΩ : KP ⊆ Ω := hprimary
  have hgraphs (adj : Bool) : MapsTo (fullSourceGraphPoint adj) K (domain ℓ C.target) :=
    fun v hv ↦ ⟨by simpa only [fullSourceGraphPoint] using hpos v hv, hbuffer (hmap adj hv)⟩
  obtain ⟨W₀, hW₀, hKW₀, hsmooth⟩ := exists_full_source_joint_phase_smooth_neighborhood ℓ C hCsm
    (T.fullSourcePhaseInCoordinates i Q) hΩ hφ hgraphs
      (fun v hv ↦ hKPΩ (hgeom.2 v hv).1) (fun v hv ↦ hKPΩ (hgeom.2 v hv).2)
  have hdiag q (hq : q ∈ U₀) : closedBall
      (WithLp.toLp 2 (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1))
        (4 * ρ) ⊆ D := by
    have hh := hmargin Q hQlow (pull q)
      (mem_image_of_mem pull ⟨subset_closure hq.1, hVA hq.2⟩)
    simpa only [pull, coord, ContinuousLinearEquiv.apply_symm_apply] using hh
  have hbuf q (hq : q ∈ U₀) :
      (Icc (-ε) ε ×ˢ {q}) ×ˢ closedBall
        (WithLp.toLp 2 (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1))
          (4 * ρ) ⊆ K := by
    rintro ⟨⟨t, q'⟩, w⟩ ⟨⟨ht, hq'⟩, hw⟩
    have heq : q' = q := hq'
    subst q'
    exact ⟨⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hU₀KP hq⟩,
      subset_closure (hdiag q hq hw)⟩
  have hRcrit : max SP (max (SF false) (SF true)) ≤ R₀ := (le_max_left _ _).trans hR₀
  have hR₀P : SP ≤ R₀ := (le_max_left _ _).trans hRcrit
  have hR₀F (adj : Bool) : SF adj ≤ R₀ := by
    apply le_trans _ ((le_max_right _ _).trans hRcrit)
    cases adj
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hprimary2 : ∀ q ∈ U₀, ‖iteratedFDeriv ℝ 2
      (Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) q‖ ≤ AP 2 := by
    intro q hq
    have hb := hprimaryBound R₀ hR₀P n u ell hu Q hQ 2
    simp only [show 2 - 3 = 0 by omega, pow_zero, mul_one] at hb
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hKP
      (fun v hv ↦ (hφ.contDiffAt (hΩ.mem_nhds (hKPΩ hv))).of_le (by simp))
      (hU₀KP hq) le_rfl).trans hb
  have hgraph0 q (hq : q ∈ U₀) : elapsedChartPoint 0 q.1
      (gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1) ∈ domain ℓ C.target := by
    have hv : ((0, q), WithLp.toLp 2
        (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1)) ∈ K :=
      hbuf q hq ⟨⟨⟨by linarith, hε.le⟩, rfl⟩, mem_closedBall_self (by positivity)⟩
    exact hgraphs false hv
  have hphase23 adj :
      cNorm K 2 (fullSourceJointPhase adj (curriedPhase ℓ C) (T.fullSourcePhaseInCoordinates i Q)) ≤ B 2 ∧
      cNorm K 3 (fullSourceJointPhase adj (curriedPhase ℓ C) (T.fullSourcePhaseInCoordinates i Q)) ≤ B 3 := by
    have h2 := (hprofile adj R₀ (hR₀F adj) n u ell hu Q hQ C hbuffer hCsm hbudget 2).1
    have h3 := (hprofile adj R₀ (hR₀F adj) n u ell hu Q hQ C hbuffer hCsm hbudget 3).1
    simp only [show 2 - 3 = 0 by omega, pow_zero, mul_one] at h2 h3
    exact ⟨h2.trans (hAB adj 2), h3.trans (hAB adj 3)⟩
  obtain ⟨κ, hκ⟩ := hbranch (T.fullSourcePhaseInCoordinates i Q) Ω hΩ hφ
    (hU₀KP.trans hKPΩ) hprimary2 ℓ Φ C hC z a hsource hi hgraph0
    W₀ K hW₀ hK hKW₀ hbuf hsmooth hphase23 D hdiag
  have hproduct : (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D ⊆ K := by
    rintro ⟨⟨t, q⟩, w⟩ ⟨⟨ht, hq⟩, hw⟩
    exact ⟨⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hU₀KP hq⟩, subset_closure hw⟩
  refine ⟨κ, fun adj ↦ ⟨(hsmooth adj).mono (hproduct.trans hKW₀),
    (hκ adj).1.mono hinterval, (hκ adj).2.1, ?_⟩⟩
  intro p hp
  obtain ⟨hκD, hstat, hdist⟩ := (hκ adj).2.2 p (hinterval hp)
  refine ⟨hκD, hstat, hdist, ?_, ?_⟩
  · intro w hw
    have ht : |p.1| ≤ τI := (abs_le.mpr
      ⟨by linarith [hp.1.1], hp.1.2.le⟩).trans hτI'
    have hh := hinverse R₀ ((le_max_right _ _).trans hR₀) n u ell hu Q hQ
      Φ C a hC hsource hi hbuffer hCsm hbudget adj p.1 ht p.2 (hU₀KP hp.2)
      (κ adj p) (subset_closure hκD) w hw
    exact ⟨hh.1, hh.2.1⟩
  intro w hw u hu v hv
  have htime : |p.1| ≤ 2 * ε := abs_le.mpr ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  have hseg := (fullSourceSignedCarrier_segments z ε hOc htime (hU₀KP hp.2)
    (subset_closure hκD) hw u hu v hv).1
  exact ⟨hseg, fun adj ↦ hgraphs adj hseg⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
