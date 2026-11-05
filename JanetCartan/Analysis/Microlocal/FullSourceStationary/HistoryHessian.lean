module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.AveragedHessian
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.JointProfiles

/-!
# Actual uniform averaged-Hessian inverses for the full source

The original history phase profiles control the second source jet and third
joint phase jet. The explicit zero-time block inverse and elapsed perturbation
give one inverse bound and interval for BOTH literal orientations on the SAME
full signed carrier, before histories and operators. Consumer:
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
open RegularSector.Characteristic ConicPhase EvolutionIntegral FullSourceStationary
open LeadingWave.FullModulation
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "TC" => TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)

/-- The original full-source history jets construct one inverse bound,
elapsed radius, and inverse-variation constant for BOTH literal orientations
on every segment in the full integration closure. These constants precede
the varying history, source masks, chart witnesses and operators. Neither an
inverse bound nor a Hessian perturbation estimate is an input
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_full_source_hessian_inverse_stability
    (i : Fin (d + 1)) (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε b aperture gap radius : ℝ} (hε : 0 < ε) (hεb : 4 * ε ≤ b)
    (hAp : 0 < aperture) (hg : 0 < gap)
    {A : Set Param} (hA : IsCompact A)
    (hO : IsOpen (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius))
    (hOc : Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius))
    (hOK : IsCompact (closure
      (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius)))
    (hprimary : ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin)
    {KQ : Set E} (hKQ : IsCompact KQ)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ M > (0 : ℝ), ∃ τ > (0 : ℝ), τ ≤ ε ∧
      ∃ inverseVariation > (0 : ℝ),
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC) (a : ℝ),
        (C : TC → TC) = twoTimeProjection Φ →
        C.source = ball (z.1, z) a → (∀ v ∈ ball z a, Φ (v, 0) = v) →
        closedBall (z.1, z) b ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
          phaseCost m * (1 + cNorm KQ (m + 1) Q.1)) →
      let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius
      let D := retainedOpenIntegrationDomain z ε O
      ∀ adj : Bool, ∀ t : ℝ, |t| ≤ τ → ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
        ∀ v ∈ closure D, ∀ w ∈ closure D,
        let f := fullSourceJointPhase adj (curriedPhase ℓ C) (T.fullSourcePhaseInCoordinates i Q)
        let H := averagedPhaseHessian (fun p y ↦ f ((t, p), y)) (fun _ ↦ v) q w
        let H₀ := averagedPhaseHessian (fun p y ↦ f ((0, p), y)) (fun _ ↦ v) q w
        IsUnit H ∧ ‖Ring.inverse H‖ ≤ M ∧
          ‖Ring.inverse H - Ring.inverse H₀‖ ≤ inverseVariation * |t| := by
  let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius
  let K := fullSourceSignedCarrier z ε A O
  let KP := closure (elapsedPhysicalBox z ε) ×ˢ A
  have hgeom := fullSourceSignedCarrier_geometry z ε hA hO hOc hOK
  have hK : IsCompact K := hgeom.1
  have hKP : IsCompact KP := by
    have hx := isCompact_closure_retained_physicalBox z (2 * ε)
    simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hx
    exact hx.prod hA
  have hpos (v : FullSourcePoint d) (hv : v ∈ K) : 0 < ℓ (spatialPart v.2.snd) :=
    (fullSourceSignedCarrier_normalizes ℓ z hε hAp hg hO hOc hOK false hv).1
  have hmap (adj : Bool) : MapsTo (ConicPhase.normalize ℓ ∘ fullSourceGraphPoint adj) K
      (closedBall (z.1, z) b) := fun _ hv ↦
    closedBall_subset_closedBall hεb
      (fullSourceSignedCarrier_normalizes ℓ z hε hAp hg hO hOc hOK adj hv).2
  have hsrc (v : FullSourcePoint d) (hv : v ∈ K) : (v.2.fst, v.1.2.2) ∈ KP :=
    (hgeom.2 v hv).1
  have hout (v : FullSourcePoint d) (hv : v ∈ K) : v.1.2 ∈ KP := (hgeom.2 v hv).2
  obtain ⟨SP, hSP, AP, hAP, hprofileP⟩ :=
    T.exists_admissible_history_full_source_phase_profiles i hKP hprimary G hr hrR hR ext
      hextcenter hextradius hStar (Rstar := 3) (by omega) horder
  have hprofiles (adj : Bool) :=
    T.exists_admissible_history_full_source_joint_phase_profiles i adj ℓ hK
      (isCompact_closedBall _ _) hKP hpos (hmap adj) hsrc hout hprimary G hr hrR hR ext
      hextcenter hextradius hStar (Rstar := 3) (by omega) horder hKQ phaseCost hphaseCost
  choose SF hSF AF hAF hprofileF using hprofiles
  let B := 1 + AF false 3 + AF true 3
  have hB : 0 < B := by dsimp [B]; linarith [hAF false 3, hAF true 3]
  have hAB (adj : Bool) : AF adj 3 ≤ B := by
    cases adj <;> dsimp [B] <;> linarith [hAF false 3, hAF true 3]
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let M₀ := 1 + ‖e.symm.toContinuousLinearMap‖ * (1 + AP 2) * ‖e.toContinuousLinearMap‖
  have hM₀ : 0 < M₀ := by have hp := hAP 2; dsimp [M₀]; positivity
  let τ := min ε (2 * M₀ * B)⁻¹
  have hτ : 0 < τ := lt_min hε (by positivity)
  have hhalf : M₀ * (B * (2 * M₀ * B)⁻¹) = 1 / 2 := by field_simp
  refine ⟨max SP (max (SF false) (SF true)), hSP.trans (le_max_left _ _),
    2 * M₀, by positivity, τ, hτ, min_le_left _ _, 2 * M₀ ^ 2 * B, by positivity, ?_⟩
  intro R₀ hR₀ n u ell hu Q hQ Φ C a hC hsource hi hbuffer hCsm hbudget
  dsimp only
  intro adj t ht q hq v hv w hw
  have hR₀P : SP ≤ R₀ := (le_max_left _ _).trans hR₀
  have hR₀F (o : Bool) : SF o ≤ R₀ := by
    apply le_trans _ ((le_max_right _ _).trans hR₀)
    cases o
    · exact le_max_left _ _
    · exact le_max_right _ _
  let F : E × Param → E × Euclidean d :=
    fun p ↦ ((primaryCoordinateChange i).symm p.1, p.2.2)
  let Ω := F ⁻¹' phaseDomain T
  have hF : ContDiff ℝ ∞ F :=
    ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd.snd
  have hΩ : IsOpen Ω := isOpen_ball.preimage hF.continuous
  have hφ : ContDiffOn ℝ ∞ (Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) Ω :=
    T.fullSourcePhaseInCoordinates_smooth i Q (fun _ hp ↦ hp)
  have hgraphs (o : Bool) : MapsTo (fullSourceGraphPoint o) K (domain ℓ C.target) :=
    fun p hp ↦ ⟨by simpa only [fullSourceGraphPoint] using hpos p hp, hbuffer (hmap o hp)⟩
  obtain ⟨V, hV, hKV, hsmooth⟩ := exists_full_source_joint_phase_smooth_neighborhood ℓ C hCsm
    (T.fullSourcePhaseInCoordinates i Q) hΩ hφ hgraphs
      (fun p hp ↦ hprimary _ (hsrc p hp)) (fun p hp ↦ hprimary _ (hout p hp))
  have htime : |t| ≤ 2 * ε := (ht.trans (min_le_left _ _)).trans (by linarith)
  have hsegments : ∀ s ∈ uIcc (0 : ℝ) t, ∀ k ∈ Icc (0 : ℝ) 1,
      ((s, q), v + k • (w - v)) ∈ K := fun s hs k hk ↦
    (fullSourceSignedCarrier_segments z ε hOc htime hq hv hw s hs k hk).1
  have hz := full_source_conic_zeroTime_averagedHessian_bound adj ℓ hC hsource hi
    hΩ hφ hKP (fun p hp ↦ hprimary p hp) (fun _ ↦ v) q w
    (fun k hk ↦ hsrc _ (hsegments 0 left_mem_uIcc k hk))
    (fun o k hk ↦ hgraphs o (hsegments 0 left_mem_uIcc k hk))
  have hp₂ : cNorm KP 2 (Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) ≤ AP 2 := by
    change cNorm KP 2 (fun p : E × Param ↦ T.fullSourcePhaseInCoordinates i Q p.1 p.2) ≤ AP 2
    simpa only [show 2 - 3 = 0 by omega, pow_zero, mul_one] using
      hprofileP R₀ hR₀P n u ell hu Q hQ 2
  have hinv₀ : ‖Ring.inverse (averagedPhaseHessian
      (fun p y ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
        (T.fullSourcePhaseInCoordinates i Q) ((0, p), y)) (fun _ ↦ v) q w)‖ ≤ M₀ := by
    apply hz.2.trans
    calc
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * (1 + AP 2) * ‖e.toContinuousLinearMap‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hp₂) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ M₀ := by dsimp [M₀]; linarith
  have hp₃ : cNorm K 3 (fullSourceJointPhase adj (curriedPhase ℓ C)
      (T.fullSourcePhaseInCoordinates i Q)) ≤ B := by
    have hh := (hprofileF adj R₀ (hR₀F adj) n u ell hu Q hQ C hbuffer hCsm hbudget 3).1
    simp only [Nat.sub_self, pow_zero, mul_one] at hh
    exact hh.trans (hAB adj)
  have hp := (norm_full_source_averagedHessian_sub_zero_le hV hK hKV
    (hsmooth adj) t q v w hsegments).trans
      (mul_le_mul_of_nonneg_right hp₃ (abs_nonneg t))
  have hsmall : M₀ * ‖averagedPhaseHessian
      (fun p y ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
        (T.fullSourcePhaseInCoordinates i Q) ((t, p), y)) (fun _ ↦ v) q w -
      averagedPhaseHessian
      (fun p y ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
        (T.fullSourcePhaseInCoordinates i Q) ((0, p), y)) (fun _ ↦ v) q w‖ ≤ 1 / 2 := by
    calc
      _ ≤ M₀ * (B * |t|) := mul_le_mul_of_nonneg_left hp hM₀.le
      _ ≤ M₀ * (B * (2 * M₀ * B)⁻¹) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (ht.trans (min_le_right _ _)) hB.le) hM₀.le
      _ = _ := hhalf
  obtain ⟨hunit, hnorm, hdifference⟩ :=
    OperatorInverse.inverse_stability_half _ _ hz.1 hinv₀ hsmall
  refine ⟨hunit, hnorm, hdifference.trans ?_⟩
  calc
    _ ≤ 2 * M₀ ^ 2 * (B * |t|) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (2 * M₀ ^ 2 * B) * |t| := by ring

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
