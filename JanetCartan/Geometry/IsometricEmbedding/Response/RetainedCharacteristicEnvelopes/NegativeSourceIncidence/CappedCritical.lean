module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence.CappedIncidence
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence.ConicRoot
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.StationaryValue

/-!
# Negative source pre-reference critical values for the full incidence source

The compact incidence geometry and capped stationary producer fix radii before
all references and histories. The literal Hamilton--Jacobi identities then give
zero critical values on those SAME branches and full source parameters.
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

/-- Retain the original conic incidence and prove zero critical value on
both capped branches. The source/mask radius can now be chosen before reference
admission; no source or root is replaced (`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_negative_full_source_incidence_critical_inverse_maps_of_coefficient_cap
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {ξ : E} (hξ : ξ ≠ 0) (i row col : Fin (d + 1))
    (ℓ : Euclidean d →L[ℝ] ℝ) (hℓ : ℓ (coordinateSplit i ξ).2 = 1)
    (H : Coeff × Euclidean d → ℝ) {rootRadius L μ ν : ℝ}
    (hradius : 0 < rootRadius) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i row col (cubeStress (d + 1)) ξ H rootRadius L μ ν)
    (z : RootState (Euclidean d))
    {ε b aperture gap radius : ℝ} (hε : 0 < ε) (hεb : 4 * ε ≤ b)
    (hAp : 0 < aperture) (hgap : 0 < gap)
    {Ωfield : Set E}
    (hphysical : MapsTo (primaryCoordinateChange i).symm
      (closure (elapsedPhysicalBox z ε)) Ωfield)
    {KQ : Set E} {cap : ℝ} (hcap : 0 ≤ cap)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    ∃ N : Set (Coeff × E), IsOpen N ∧ (cubeStress (d + 1), ξ) ∈ N ∧
      (∀ p ∈ N, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ N) ∧
    ∀ A V : Set Param, IsCompact A → IsOpen V → V ⊆ A →
      (∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
        ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T) →
      (∀ c ∈ A, primaryCoordinateChange i (-T.reference.covector (0, c.2)) ∈
        fullAngularCone ℓ z.2.2 (ε / 2) aperture) →
      (∀ c ∈ A, (cubeStress (d + 1), -T.reference.covector (0, c.2)) ∈ N) →
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ ρ > (0 : ℝ),
    ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ),
    ∃ τ > (0 : ℝ), τ ≤ ε ∧ ∃ InvBound > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z ε O
      let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ V
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius ⊆ O ∧
      (∀ c ∈ A, primaryCoordinateChange i (-T.reference.covector (0, c.2)) ∈ O) ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 4 Q.1 ≤ cap →
        cNorm KQ 4 Q.1 ≤ cap →
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
      a ≤ L →
      closedBall z L ⊆ fieldDomain (coordinateSplit i) Ωfield ℓ (coordinateSplit i ξ).2 rootRadius →
      (∀ w ∈ fieldDomain (coordinateSplit i) Ωfield ℓ (coordinateSplit i ξ).2 rootRadius,
        ∀ t : ℝ, 0 < t → fieldRoot (coordinateSplit i) Q.1 H (w.1, (w.2.1, t • w.2.2)) =
          t * fieldRoot (coordinateSplit i) Q.1 H w) →
      (∀ v ∈ C.target, twoTimeState Φ (C.symm v) ∈
          fieldDomain (coordinateSplit i) Ωfield ℓ (coordinateSplit i ξ).2 rootRadius ∧
        (twoTimeState Φ (C.symm v)).1 = v.1) →
      (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C)
        (twoTimePhaseDifferential (fieldRoot (coordinateSplit i) Q.1 H) Φ C v) v) →
      ∃ κ : Bool → Par → W, ∀ adj : Bool,
        ContDiffOn ℝ ∞
          (fullSourceJointPhase adj (curriedPhase ℓ C) (T.negativeFullSourcePhaseInCoordinates i Q))
          ((Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ×ˢ D) ∧
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ) (2 * τ) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ T.negativeFullSourcePhaseInCoordinates i Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ) (2 * τ) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
            (T.negativeFullSourcePhaseInCoordinates i Q) (p, w)) (κ adj p) = 0 ∧
          fullSourceJointPhase adj (curriedPhase ℓ C)
            (T.negativeFullSourcePhaseInCoordinates i Q) (p, κ adj p) = 0 ∧
          dist (κ adj p) (WithLp.toLp 2
            (p.2.1, gradient (fun y ↦ T.negativeFullSourcePhaseInCoordinates i Q y p.2.2) p.2.1)) ≤ ρ / 2 ∧
          (∀ w ∈ closure D,
            let f := fun q w ↦ fullSourceJointPhase adj (curriedPhase ℓ C)
              (T.negativeFullSourcePhaseInCoordinates i Q) ((p.1, q), w)
            IsUnit (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w) ∧
              ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w)‖ ≤ InvBound) ∧
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈ fullSourceSignedCarrier z ε A O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain ℓ C.target := by
  obtain ⟨N, hN, hbase, hcone, hroots⟩ :=
    T.exists_uniform_negative_full_source_conic_root_domain hframe hξ ℓ hℓ hradius hL hμ hν hH
  refine ⟨N, hN, hbase, hcone, ?_⟩
  intro A V hA hV hVA hprimary hfrequency hincidence
  let coord := primaryCoordinateChange i
  let pull : E × Param → E × Param := fun q ↦ (coord.symm q.1, q.2)
  let J := pull '' (closure (elapsedPhysicalBox z ε) ×ˢ A)
  have hX := isCompact_closure_retained_physicalBox z (2 * ε)
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hX
  have hJ : IsCompact J := (hX.prod hA).image
    ((coord.symm.continuous.comp continuous_fst).prodMk continuous_snd)
  have hJT : J ⊆ LeadingWave.FullModulation.domain T := by
    rintro w ⟨q, hq, rfl⟩
    exact hprimary q hq
  have hJN : ∀ w ∈ J, (cubeStress (d + 1), -T.reference.covector (0, w.2.2)) ∈ N := by
    rintro w ⟨q, hq, rfl⟩
    exact hincidence q.2 hq.2
  obtain ⟨δroot, hδroot, _, hroot⟩ := hroots J hJ hJT hJN
  obtain ⟨δstat, hδstat, hδstatT, ρ, hρ, g, hg, Rad, hRad, τ, hτ, hτε,
    InvBound, hInvBound, hO, hOc, hOK, hFO, hfreq, hmaps⟩ :=
    T.exists_uniform_negative_full_source_incidence_stationary_inverse_maps_of_coefficient_cap i ℓ z hε hεb hAp hgap
      hA hV hVA hprimary hfrequency (KQ := KQ) hcap phaseCost hphaseCost
  refine ⟨min δroot δstat, lt_min hδroot hδstat, (min_le_right _ _).trans hδstatT,
    ρ, hρ, g, hg, Rad, hRad, τ, hτ, hτε, InvBound, hInvBound,
    hO, hOc, hOK, hFO, hfreq, ?_⟩
  intro Q hQstate hQcoeff hQlow Φ C a hC hsource hi hbuffer hCsm hbudget
    haL hLD hhom hstate hphase
  obtain ⟨κ, hκ⟩ := hmaps Q hQstate hQcoeff
    (hQlow.trans_le (min_le_right _ _)) Φ C a hC hsource hi hbuffer hCsm hbudget
  let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
  let D := retainedOpenIntegrationDomain z ε O
  let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ V
  let Ω := elapsedPhysicalBox z ε ×ˢ V
  have hΩ : IsOpen Ω := (isOpen_elapsedPhysicalBox _ _).prod hV
  have hφ := T.negativeFullSourcePhaseInCoordinates_smooth i Q (Ω := Ω)
    (fun q hq ↦ hprimary q ⟨subset_closure hq.1, hVA hq.2⟩)
  have he : ∀ q ∈ Ω,
      rootSuspension (fieldRoot (coordinateSplit i) Q.1 H)
        (q.1, gradient (fun y ↦ T.negativeFullSourcePhaseInCoordinates i Q y q.2) q.1) = 0 := by
    intro q hq
    have hp := hroot Q (hQlow.trans_le (min_le_left _ _)) Ωfield hhom
      (pull q) (mem_image_of_mem pull ⟨subset_closure hq.1, hVA hq.2⟩)
      (hphysical (subset_closure hq.1))
    simpa only [pull, coord, ContinuousLinearEquiv.apply_symm_apply] using hp.2
  have hU₀ : IsOpen U₀ := (isOpen_elapsedPhysicalBox _ _).prod hV
  have hUΩ : U₀ ⊆ Ω := fun q hq ↦
    ⟨UniformEvolution.closure_elapsedPhysicalBox_half_subset hε (subset_closure hq.1), hq.2⟩
  have hvalue := full_source_uniform_stationary_value_eq_zero ℓ hhom hC hsource haL hLD hi
    hstate hCsm hphase (T.negativeFullSourcePhaseInCoordinates i Q) hΩ hφ he hU₀ hUΩ hτ κ
    (fun adj ↦ (hκ adj).2.1) (fun adj ↦ (hκ adj).2.2.1)
    (fun adj p hp ↦ ((hκ adj).2.2.2 p hp).2.1)
    (fun adj p hp ↦ ⟨((hκ adj).2.2.2 p hp).1.1, hp.2.2⟩)
    (fun adj p hp ↦ by
      have hh := (hκ adj).2.2.2 p hp
      simpa only [zero_smul, add_zero, Prod.mk.eta] using
        (hh.2.2.2.2 (κ adj p) (subset_closure hh.1) p.1 right_mem_uIcc 0
          ⟨le_rfl, zero_le_one⟩).2 adj)
  refine ⟨κ, fun adj ↦ ⟨(hκ adj).1, (hκ adj).2.1, (hκ adj).2.2.1, ?_⟩⟩
  intro p hp
  obtain ⟨hD, hstat, hdist, hinverse, hsegments⟩ := (hκ adj).2.2.2 p hp
  exact ⟨hD, hstat, hvalue adj p hp, hdist, hinverse, hsegments⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
