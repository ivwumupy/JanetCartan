module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourcePhase
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SignedSmoothPhase

/-!
# The actual full-source critical data on the representative's elapsed slice

The stationary producer works with the original conic chart and primary phase;
the physical integral uses their smooth representatives. On the entire open
integration box both source terms are on the primary plateau. The chart term
lies on the same signed conic plateau in each literal orientation. Thus the
critical value, gradient, averaged Hessian (including its full segment), and
all coefficient-profile jets transfer without changing the critical map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullSourceEnvelopes
open ActualCarriers ActualCarriers.CurrentFullPhase CompatibleResponse FrozenMenu HamiltonPhase
open ConstructedCarrierJets
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open FullSourceStationary RetainedFactors DirectEvolution

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d + 1)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)

/-- The primary plateau and the signed graph plateau identify the full joint
phase pointwise on the original signed carrier. The projection into the older
conic geometry applies only to the zero-source chart term; both original
source-phase evaluations keep their full independent parameter
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem fullSource_jointPhase_representative_eq_on_carrier
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε aperture g R : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g)
    (hO : IsOpen (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hcO : Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hKO : IsCompact (closure (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)))
    {δ : ℝ} (hδ : 0 < δ) (hδg : δ ≤ g / (1 + ‖ℓ‖))
    {χg : TC → ℝ} (heg : ∀ p ∈ closedBall (z.1, z) (4 * ε), χg =ᶠ[𝓝 p] (fun _ ↦ 1))
    (C : OpenPartialHomeomorph TC TC)
    {A : Set Par} (hA : IsCompact A) (φ : E → Par → ℝ) (χ : E × Par → ℝ)
    (hχ : ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A, χ q = 1)
    (adj : Bool) {v : FullSourcePoint d} (hv : v ∈ fullSourceSignedCarrier z ε A (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)) :
    fullSourceJointPhase adj (SmoothRepresentative.curriedRepresentative ℓ δ hδ χg (twoTimePhase C)) (fun y c ↦ χ (y, c) * φ y c) v =
      fullSourceJointPhase adj (curriedPhase ℓ C) φ v := by
  let O := (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)
  let p : RetainedCarrierPoint d := ((v.1.1, (v.1.2.1, v.1.2.2.1)), v.2)
  have hp : p ∈ retainedSignedCarrier z ε univ O := ⟨⟨hv.1.1, hv.1.2.1, mem_univ _⟩, hv.2⟩
  have hn := retainedSignedCarrier_normalizes ℓ z hε hAp hg hO hcO hKO adj hp
  have hfreq := (retainedSignedCarrier_frequency_lower_bound ℓ z hg hO hcO hKO).2 p hp
  have he := (jointRetainedCarrierPhase_representative_eventuallyEq adj ℓ C hδ heg (fun _ _ ↦ 0)
    (v := p) ⟨by simpa only [carrierGraphPoint] using hn.1, hn.2⟩ (hδg.trans hfreq)).eq_of_nhds
  have hpos := (fullSourceSignedCarrier_geometry z ε hA hO hcO hKO).2 v hv
  rw [fullSourceJointPhase_eq_zero_source, fullSourceJointPhase_eq_zero_source]
  simpa only [hχ _ hpos.1, hχ _ hpos.2, one_mul] using
    congrArg (fun a ↦ a + φ v.2.fst v.1.2.2 - φ v.1.2.1 v.1.2.2) he

variable {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
  (i : Fin (d + 1))

/-- Specialization of the stationary producer to the exact representative
input of `fullSource_fullElapsed_envelopes_of_supported_phase`.
The first three critical-map hypotheses are projections of the SAME supplied
`exists_uniform_full_source_critical_inverse_maps` witness, and the last jet
bound is the fixed-time projection of
`exists_admissible_history_full_source_joint_phase_profiles`. Neither map nor
phase is reselected. `src ≤ τ` places the entire physical elapsed interval in
the producer's open interval (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem fullSource_critical_slice_of_stationary_data
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε aperture g R : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g)
    (hO : IsOpen (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hcO : Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hKO : IsCompact (closure (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)))
    {δ : ℝ} (hδ : 0 < δ) (hδg : δ ≤ g / (1 + ‖ℓ‖))
    {χg : TC → ℝ} (heg : ∀ p ∈ closedBall (z.1, z) (4 * ε), χg =ᶠ[𝓝 p] (fun _ ↦ 1))
    (C : OpenPartialHomeomorph TC TC)
    (c₀ : Par) (s : ℝ)
    (Q : {Q : E → Fin (d + 1) → MetricTensor (d + 1) // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (χ : E × Par → ℝ) (hχ : ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ closedBall c₀ (2 * s), χ q = 1)
    {τ src : ℝ} (hτ : 0 < τ) (hτε : τ ≤ ε) (hsrc : src ≤ τ)
    (κ : (ℝ × (E × Par)) → W) (adj : Bool) (InvBound L : ℝ) (Rstar : ℕ) (Aphase : ℕ → ℝ) :
    let O := (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)
    let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ ball c₀ (2 * s)
    let D := retainedOpenIntegrationDomain z ε O
    let A₀ := closedBall c₀ (2 * s)
    let φ := T.fullSourcePhaseInCoordinates i Q
    let F := fullSourceJointPhase adj (curriedPhase ℓ C) φ
    let Fr := fullSourceJointPhase adj (SmoothRepresentative.curriedRepresentative ℓ δ hδ χg (twoTimePhase C)) (fun y c ↦ χ (y, c) * φ y c)
    let Z := Ioo (-2 * τ) (2 * τ) ×ˢ U₀
    ContDiffOn ℝ ∞ F (Z ×ˢ D) → ContDiffOn ℝ ∞ κ Z →
    (∀ p ∈ Z, κ p ∈ D ∧ gradient (fun w ↦ F (p, w)) (κ p) = 0 ∧ F (p, κ p) = 0) →
    (∀ p ∈ Z, ∀ w ∈ closure D,
      let f := fun q w ↦ F ((p.1, q), w)
      IsUnit (averagedPhaseHessian f (fun q ↦ κ (p.1, q)) p.2 w) ∧
        ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ (p.1, q)) p.2 w)‖ ≤ InvBound) →
    (∀ j t (v : (E × Par) × W), ((t, v.1), v.2) ∈ fullSourceSignedCarrier z ε A₀ O →
      ‖iteratedFDeriv ℝ j (fun b : (E × Par) × W ↦ F ((t, b.1), b.2)) v‖ ≤ Aphase j * L^ (j - Rstar)) →
    ∀ t ∈ Icc 0 (3 * src / 4),
      let f := fun q w ↦ Fr ((t, q), w)
      let w₀ := fun q ↦ κ (t, q)
      ContDiffOn ℝ ∞ (Function.uncurry f) (U₀ ×ˢ D) ∧
      ContDiffOn ℝ ∞ w₀ U₀ ∧ MapsTo w₀ U₀ D ∧
      (∀ q ∈ U₀, gradient (f q) (w₀ q) = 0 ∧ f q (w₀ q) = 0) ∧
      (∀ q ∈ U₀, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w) ∧
        ‖Ring.inverse (averagedPhaseHessian f w₀ q w)‖ ≤ InvBound) ∧
      ∀ j q, q ∈ U₀ ×ˢ D → ‖iteratedFDeriv ℝ j (Function.uncurry f) q‖ ≤ Aphase j * L^ (j - Rstar) := by
  intro O U₀ D A₀ φ F Fr Z hF hκ hstat hinv hj t ht f w₀
  have htτ : t ∈ Ioo (-2 * τ) (2 * τ) := ⟨by linarith only [hτ, ht.1], by linarith only [hτ, hsrc, ht.2]⟩
  have hK (q : (E × Par) × W) (hq : q ∈ U₀ ×ˢ D) :
      ((t, q.1), q.2) ∈ fullSourceSignedCarrier z ε A₀ O :=
    ⟨⟨⟨by linarith only [hτε, htτ.1], by linarith only [hτε, htτ.2]⟩,
      ⟨subset_closure (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε (subset_closure hq.1.1)),
        ball_subset_closedBall hq.1.2⟩⟩, subset_closure hq.2⟩
  let f₀ := fun (q : E × Par) (w : W) ↦ F ((t, q), w)
  have he : EqOn (Function.uncurry f) (Function.uncurry f₀) (U₀ ×ˢ D) := fun {q} hq ↦
    fullSource_jointPhase_representative_eq_on_carrier ℓ z hε hAp hg hO hcO hKO hδ hδg heg C
      (isCompact_closedBall _ _) φ χ hχ adj (hK q hq)
  have hU₀ := (isOpen_elapsedPhysicalBox z (ε / 2)).prod (isOpen_ball (x := c₀) (ε := 2 * s))
  obtain ⟨hD, hcD, _, _⟩ := retainedOpenIntegrationDomain_geometry z ε hO hcO hKO
  have hs q (hq : q ∈ U₀) w (hw : w ∈ D) : f q =ᶠ[𝓝 w] f₀ q :=
    (show EqOn (f q) (f₀ q) D from fun {v} h ↦ @he (q, v) ⟨hq, h⟩).eventuallyEq_of_mem (hD.mem_nhds hw)
  have hκD : MapsTo w₀ U₀ D := fun q hq ↦ (hstat (t, q) ⟨htτ, hq⟩).1
  have hfs : ContDiffOn ℝ ∞ (Function.uncurry f₀) (U₀ ×ˢ D) :=
    hF.comp (f := fun p : (E × Par) × W ↦ ((t, p.1), p.2))
      ((contDiffOn_const.prodMk contDiffOn_fst).prodMk contDiffOn_snd)
      (fun _ h ↦ ⟨⟨htτ, h.1⟩, h.2⟩)
  have hks : ContDiffOn ℝ ∞ w₀ U₀ :=
    hκ.comp (f := fun q : E × Par ↦ (t, q)) (contDiffOn_const.prodMk contDiffOn_id) (fun _ h ↦ ⟨htτ, h⟩)
  refine ⟨hfs.congr he, hks, hκD, ?_, ?_, ?_⟩
  · intro q hq
    have h := hstat (t, q) ⟨htτ, hq⟩
    exact ⟨(hs q hq _ h.1).gradient_eq.trans h.2.1, (hs q hq _ h.1).eq_of_nhds.trans h.2.2⟩
  · intro q hq w hw
    have hh : averagedPhaseHessian f w₀ q w = averagedPhaseHessian f₀ w₀ q w := by
      apply intervalIntegral.integral_congr
      intro b hb
      exact (hs q hq _ (hcD.add_smul_sub_mem (hκD hq) hw (by simpa using hb))).gradient.fderiv_eq
    rw [hh]
    exact hinv (t, q) ⟨htτ, hq⟩ w (subset_closure hw)
  · intro j q hq
    rw [((he.eventuallyEq_of_mem ((hU₀.prod hD).mem_nhds hq)).iteratedFDeriv ℝ j).eq_of_nhds]
    exact hj j t q (hK q hq)

end JanetCartan.ResponseTransfer.FullSourceEnvelopes
