module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CompactDiagonalMargins
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CompactAnnularBuffer
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.StationaryBranch
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.CappedStationary

/-!
# Pre-reference stationary radii on the original source-incidence compact

Apply the coefficient-capped full-source producer to the actual compact annular
and diagonal buffers. The coefficient cap precedes all fields, references and
histories; the unchanged full source compact retains both orientations and all
integration segments. Consumer: pre-reference finite terminal-cover selection.
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

/-- Construct the actual compact incidence buffers, then apply the
reference-independent stationary/Hessian producer at the fixed coefficient cap.
The original full source parameters, both orientations and complete segments
remain unchanged (`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_full_source_incidence_stationary_inverse_maps_of_coefficient_cap
    (i : Fin (d + 1)) (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε b aperture gap radius : ℝ} (hε : 0 < ε) (hεb : 4 * ε ≤ b)
    (hAp : 0 < aperture) (hgap : 0 < gap)
    {A V : Set Param} (hA : IsCompact A) (hV : IsOpen V) (hVA : V ⊆ A)
    (hprimary : ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    (hfrequency : ∀ c ∈ A,
      primaryCoordinateChange i (T.reference.covector (0, c.2)) ∈
        fullAngularCone ℓ z.2.2 (ε / 2) aperture)
    {KQ : Set E} {cap : ℝ} (hcap : 0 ≤ cap)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ ρ > (0 : ℝ),
    ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ),
    ∃ τ > (0 : ℝ), τ ≤ ε ∧ ∃ InvBound > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z ε O
      let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ V
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture gap radius ⊆ O ∧
      (∀ c ∈ A, primaryCoordinateChange i (T.reference.covector (0, c.2)) ∈ O) ∧
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
  obtain ⟨τ, hτ, hτε, InvBound, hInvBound, hmaps⟩ :=
    T.exists_full_source_stationary_inverse_maps_of_coefficient_cap i ℓ z hε hεb hAp hg
      hA hO hOc hOK hprimary hU₀ hU₀KP hρ hcap KQ phaseCost hphaseCost
  refine ⟨δ, hδ, hδT, ρ, hρ, g, hg, Rad, hRad, τ, hτ, hτε, InvBound, hInvBound,
    hO, hOc, hOK, hFO, (fun c hc ↦ hfreqO (mem_image_of_mem freq hc)), ?_⟩
  intro Q hQstate hQcoeff hQlow Φ C a hC hsource hi hbuffer hCsm hbudget
  apply hmaps Q hQstate hQcoeff ?_ Φ C a hC hsource hi hbuffer hCsm (fun m _ ↦ hbudget m)
  intro q hq
  have hh := hmargin Q hQlow (pull q)
    (mem_image_of_mem pull ⟨subset_closure hq.1, hVA hq.2⟩)
  simpa only [pull, coord, ContinuousLinearEquiv.apply_symm_apply] using hh

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
