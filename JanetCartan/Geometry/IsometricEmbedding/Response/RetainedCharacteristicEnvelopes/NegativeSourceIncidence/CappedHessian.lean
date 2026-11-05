module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.AveragedHessian
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence.LowPhaseBudgets

/-!
# Negative full-source inverse stability from a cap fixed before the reference

The original order-four coefficient cap supplies the second source jet and
third joint jet through the actual phase producers. Thus the explicit block
inverse and elapsed perturbation choose the common radius without any reference
or history. Consumer: `FixedResponseSelection.IncidenceStationary` and
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

/-- Construct the inverse bound, elapsed radius and inverse-variation constant
BEFORE every common reference and history, from one fixed coefficient C4 cap.
Both literal orientations and complete integration segments use the original
full source and original conic chart. The actual source and joint phase bounds
are proved from the cap by `exists_negative_full_source_low_phase_budgets_of_coefficient_cap`;
no Hessian or successful-stationary-map estimate is assumed. The cap's producer
is `exists_reference_tolerance_for_stationary_coefficient_cap`
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_negative_full_source_hessian_inverse_stability_of_coefficient_cap
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
    {cap : ℝ} (hcap : 0 ≤ cap) (KQ : Set E)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    ∃ M > (0 : ℝ), ∃ τ > (0 : ℝ), τ ≤ ε ∧
      ∃ inverseVariation > (0 : ℝ),
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 4 Q.1 ≤ cap →
        cNorm KQ 4 Q.1 ≤ cap →
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC) (a : ℝ),
        (C : TC → TC) = twoTimeProjection Φ →
        C.source = ball (z.1, z) a → (∀ v ∈ ball z a, Φ (v, 0) = v) →
        closedBall (z.1, z) b ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m ≤ 3, cNorm (closedBall (z.1, z) b) m (twoTimePhase C) ≤
          phaseCost m * (1 + cNorm KQ (m + 1) Q.1)) →
      let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius
      let D := retainedOpenIntegrationDomain z ε O
      ∀ adj : Bool, ∀ t : ℝ, |t| ≤ τ → ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
        ∀ v ∈ closure D, ∀ w ∈ closure D,
        let f := fullSourceJointPhase adj (curriedPhase ℓ C) (T.negativeFullSourcePhaseInCoordinates i Q)
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
  obtain ⟨AP, AF, hAP, hAF, hbudgets⟩ :=
    T.exists_negative_full_source_low_phase_budgets_of_coefficient_cap i ℓ hK
      (isCompact_closedBall _ _) hKP hpos hmap hsrc hout hprimary hcap KQ phaseCost hphaseCost
  let B := 1 + AF 3
  have hB : 0 < B := by dsimp [B]; linarith [hAF 3]
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let M₀ := 1 + ‖e.symm.toContinuousLinearMap‖ * (1 + AP 2) * ‖e.toContinuousLinearMap‖
  have hM₀ : 0 < M₀ := by have hp := hAP 2; dsimp [M₀]; positivity
  let τ := min ε (2 * M₀ * B)⁻¹
  have hτ : 0 < τ := lt_min hε (by positivity)
  have hhalf : M₀ * (B * (2 * M₀ * B)⁻¹) = 1 / 2 := by field_simp
  refine ⟨2 * M₀, by positivity, τ, hτ, min_le_left _ _, 2 * M₀ ^ 2 * B, by positivity, ?_⟩
  intro Q hQframe hQcap Φ C a hC hsource hi hbuffer hCsm hbudget
  dsimp only
  intro adj t ht q hq v hv w hw
  obtain ⟨hprimaryBudget, hjointBudget⟩ := hbudgets Q hQframe hQcap
  let F : E × Param → E × Euclidean d :=
    fun p ↦ ((primaryCoordinateChange i).symm p.1, p.2.2)
  let Ω := F ⁻¹' phaseDomain T
  have hF : ContDiff ℝ ∞ F :=
    ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd.snd
  have hΩ : IsOpen Ω := isOpen_ball.preimage hF.continuous
  have hφ : ContDiffOn ℝ ∞ (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q)) Ω :=
    T.negativeFullSourcePhaseInCoordinates_smooth i Q (fun _ hp ↦ hp)
  have hgraphs (o : Bool) : MapsTo (fullSourceGraphPoint o) K (domain ℓ C.target) :=
    fun p hp ↦ ⟨by simpa only [fullSourceGraphPoint] using hpos p hp, hbuffer (hmap o hp)⟩
  obtain ⟨V, hV, hKV, hsmooth⟩ := exists_full_source_joint_phase_smooth_neighborhood ℓ C hCsm
    (T.negativeFullSourcePhaseInCoordinates i Q) hΩ hφ hgraphs
      (fun p hp ↦ hprimary _ (hsrc p hp)) (fun p hp ↦ hprimary _ (hout p hp))
  have htime : |t| ≤ 2 * ε := (ht.trans (min_le_left _ _)).trans (by linarith)
  have hsegments : ∀ s ∈ uIcc (0 : ℝ) t, ∀ k ∈ Icc (0 : ℝ) 1,
      ((s, q), v + k • (w - v)) ∈ K := fun s hs k hk ↦
    (fullSourceSignedCarrier_segments z ε hOc htime hq hv hw s hs k hk).1
  have hz := full_source_conic_zeroTime_averagedHessian_bound adj ℓ hC hsource hi
    hΩ hφ hKP (fun p hp ↦ hprimary p hp) (fun _ ↦ v) q w
    (fun k hk ↦ hsrc _ (hsegments 0 left_mem_uIcc k hk))
    (fun o k hk ↦ hgraphs o (hsegments 0 left_mem_uIcc k hk))
  have hp₂ : cNorm KP 2 (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q)) ≤ AP 2 :=
    hprimaryBudget 2 (by omega)
  have hinv₀ : ‖Ring.inverse (averagedPhaseHessian
      (fun p y ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
        (T.negativeFullSourcePhaseInCoordinates i Q) ((0, p), y)) (fun _ ↦ v) q w)‖ ≤ M₀ := by
    apply hz.2.trans
    calc
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * (1 + AP 2) * ‖e.toContinuousLinearMap‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hp₂) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ M₀ := by dsimp [M₀]; linarith
  have hp₃ : cNorm K 3 (fullSourceJointPhase adj (curriedPhase ℓ C)
      (T.negativeFullSourcePhaseInCoordinates i Q)) ≤ B :=
    (hjointBudget C hbuffer hCsm hbudget adj 3 (by omega)).trans (by dsimp [B]; linarith)
  have hp := (norm_full_source_averagedHessian_sub_zero_le hV hK hKV
    (hsmooth adj) t q v w hsegments).trans
      (mul_le_mul_of_nonneg_right hp₃ (abs_nonneg t))
  have hsmall : M₀ * ‖averagedPhaseHessian
      (fun p y ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
        (T.negativeFullSourcePhaseInCoordinates i Q) ((t, p), y)) (fun _ ↦ v) q w -
      averagedPhaseHessian
      (fun p y ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
        (T.negativeFullSourcePhaseInCoordinates i Q) ((0, p), y)) (fun _ ↦ v) q w‖ ≤ 1 / 2 := by
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
