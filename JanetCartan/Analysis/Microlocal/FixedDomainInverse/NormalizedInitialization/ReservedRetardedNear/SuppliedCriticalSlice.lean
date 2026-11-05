module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.StationarySlice

/-!
# Reserved critical data for either supplied source sign

The returned source incidence is an arbitrary open set with compact closure.
Its original stationary segments retain the whole elapsed interval on the signed
carrier. Transfer the same critical points, zero values, averaged-Hessian inverses
and phase grades to the representative, without selecting a parameter ball or
changing any mask (`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FixedDomainInverse.ReservedRetardedNear
open ResponseTransfer ResponseTransfer.RetainedFactors
open ActualCarriers ActualCarriers.CurrentFullPhase CompatibleResponse FrozenMenu HamiltonPhase
open ConstructedCarrierJets
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open FullSourceStationary FullSourceEnvelopes DirectEvolution
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d + 1)
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
/-- Apply the original stationary certificates on the selector's actual open
incidence domain, which need not be a parameter ball. Its full segment certificate
places every elapsed slice in the SAME signed carrier, so no extra radius
comparison or replacement source neighborhood is required. Both zero critical
value and the original averaged-Hessian bound are retained on the complete
interval, with unchanged phase grades. The supplied source may be the original full
phase or its literal negative; the graph phase is unchanged. Consumer: the `hcritical` input of
`reserved_annularEnvelopeIntegral_of_retained_primitives`
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem full_source_incidence_critical_slice_for_supplied_source
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε aperture g R : ℝ} (hε : 0 < ε) (hAp : 0 < aperture) (hg : 0 < g)
    (hO : IsOpen (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hcO : Convex ℝ (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R))
    (hKO : IsCompact (closure (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)))
    {δ : ℝ} (hδ : 0 < δ) (hδg : δ ≤ g / (1 + ‖ℓ‖))
    {χg : TC → ℝ} (heg : ∀ p ∈ closedBall (z.1, z) (4 * ε), χg =ᶠ[𝓝 p] (fun _ ↦ 1))
    (C : OpenPartialHomeomorph TC TC)
    (V : Set Par) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (source : E → Par → ℝ)
    (χ : E × Par → ℝ) (hχ : ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ closure V, χ q = 1)
    {τ src : ℝ}
    (hElapsed : Icc (0 : ℝ) (3 * src / 4) ⊆ Ioo (-2 * τ) (2 * τ))
    (κ : (ℝ × (E × Par)) → W) (adj : Bool) (InvBound L : ℝ) (Rstar : ℕ) (Aphase : ℕ → ℝ) :
    let O := (retainedOpenAnnularFrequencyCarrier ℓ z.2.2 (ε / 2) aperture g R)
    let U₀ := elapsedPhysicalBox z (ε / 2) ×ˢ V
    let D := retainedOpenIntegrationDomain z ε O
    let A₀ := closure V
    let φ := source
    let F := fullSourceJointPhase adj (curriedPhase ℓ C) φ
    let Fr := fullSourceJointPhase adj (SmoothRepresentative.curriedRepresentative ℓ δ hδ χg (twoTimePhase C)) (fun y c ↦ χ (y, c) * φ y c)
    let Z := Ioo (-2 * τ) (2 * τ) ×ˢ U₀
    ContDiffOn ℝ ∞ F (Z ×ˢ D) → ContDiffOn ℝ ∞ κ Z →
    (∀ p ∈ Z, κ p ∈ D ∧ gradient (fun w ↦ F (p, w)) (κ p) = 0 ∧ F (p, κ p) = 0) →
    (∀ p ∈ Z, ∀ w ∈ closure D,
      let f := fun q w ↦ F ((p.1, q), w)
      IsUnit (averagedPhaseHessian f (fun q ↦ κ (p.1, q)) p.2 w) ∧
        ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ (p.1, q)) p.2 w)‖ ≤ InvBound) →
    (∀ p ∈ Z, ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ a ∈ Icc (0 : ℝ) 1,
      ((u, p.2), κ p + a • (w - κ p)) ∈ fullSourceSignedCarrier z ε A₀ O) →
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
  intro O U₀ D A₀ φ F Fr Z hF hκ hstat hinv hsegments hj t ht f w₀
  have htτ : t ∈ Ioo (-2 * τ) (2 * τ) := hElapsed ht
  have hK (q : (E × Par) × W) (hq : q ∈ U₀ ×ˢ D) :
      ((t, q.1), q.2) ∈ fullSourceSignedCarrier z ε A₀ O := by
    have h := hsegments (t, q.1) ⟨htτ, hq.1⟩ q.2 (subset_closure hq.2)
      t right_mem_uIcc 1 ⟨by norm_num, le_rfl⟩
    simpa only [one_smul, ← add_sub_assoc, add_sub_cancel_left] using h
  let f₀ := fun (q : E × Par) (w : W) ↦ F ((t, q), w)
  have he : EqOn (Function.uncurry f) (Function.uncurry f₀) (U₀ ×ˢ D) := fun {q} hq ↦
    fullSource_jointPhase_representative_eq_on_carrier ℓ z hε hAp hg hO hcO hKO hδ hδg heg C
      hVc φ χ hχ adj (hK q hq)
  have hU₀ := (isOpen_elapsedPhysicalBox z (ε / 2)).prod hV
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

end JanetCartan.FixedDomainInverse.ReservedRetardedNear
