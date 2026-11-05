module

public import JanetCartan.Iteration.PhysicalPrimary.NegativeJointPhase
public import JanetCartan.Iteration.PhysicalPrimary.IncidencePhase
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.IncidenceProfiles
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedRetardedNear.NegativePhaseProfiles

/-!
# Signed source profiles on the same protected incidence carrier

The original smooth source mask is retained. Its negative has the same source
jet profile. The raw joint phase for that source sign is estimated afresh from
its own source bound and the unchanged graph phase, with the same history
reserve. Consumer: the signed reserved retarded near letters of
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary
open ResponseTransfer ResponseTransfer.RetainedFactors
open ActualCarriers ActualCarriers.CurrentFullPhase HamiltonPhase FrozenMenu CompatibleResponse
open ConstructedCarrierJets GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.AlgebraicChart
open FullSourceStationary FullSourceEnvelopes LeadingWave.FullModulation DirectEvolution
variable {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "CW" => CarrierVariables (d+1)

/-- Construct all source and raw-joint reserved profiles for either original
source sign. Both literal adjoint orientations keep the same conic graph.
One source mask and profile constants precede every history and derivative
order; this is an actual application of the original coefficient profiles,
with reserve `Rstar+3` (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_physical_history_signed_incidence_profiles (negative : Bool)
    {Ω : Set E} {x ξ : E} {RQ M : ℝ}
    (c : LocalChart Ω x RQ (cubeStress (d + 1)) ξ M)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hc : LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost)
    {ε aperture g Rad : ℝ} (hε : 0 < ε) (hεroot : ε ≤ c.rootRadius)
    (hεtarget : 4 * ε ≤ c.targetRadius) (hAp : 0 < aperture) (hg : 0 < g)
    (hphysical : closedBall x RQ ⊆ ball 0 T.physicalRadius)
    {A : Set Par} (hAc : IsCompact A)
    (hA : ∀ p ∈ A, p.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar Rstar kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : Rstar + 3 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    let z := ((coordinateSplit c.index x).1, ((coordinateSplit c.index x).2,
      (coordinateSplit c.index ξ).2))
    let O := retainedOpenAnnularFrequencyCarrier c.radialSection z.2.2 (ε / 2) aperture g Rad
    let KP := closure (elapsedPhysicalBox z ε) ×ˢ A
    let K := fullSourceSignedCarrier z ε A O
    let sourcePhase := fun Q ↦ if negative then T.negativeFullSourcePhaseInCoordinates c.index Q
      else T.fullSourcePhaseInCoordinates c.index Q
    IsOpen O → Convex ℝ O → IsCompact (closure O) →
    ∃ χ : E × Par → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ q ∈ KP, χ =ᶠ[𝓝 q] (fun _ ↦ 1)) ∧
    ∃ S : ℝ, 2 ≤ S ∧ ∃ Bprimary Aphase : ℕ → ℝ,
      (∀ j, 0 ≤ Bprimary j) ∧ (∀ j, 0 ≤ Aphase j) ∧ ∀ Q,
      let f := fun q : E × Par ↦ χ q * sourcePhase Q q.1 q.2
      ContDiff ℝ ∞ f ∧ (∀ q ∈ KP, f =ᶠ[𝓝 q] Function.uncurry (sourcePhase Q)) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → SchwartzMap E (Euclidean (embeddingDimension (d + 1))))
        (ell : Fin n → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      Q.1 = extendedProjectedStress ext (RevisedGlobal.finiteMap G.map u) →
      (∀ j q, q ∈ KP →
        ‖iteratedFDeriv ℝ j (fun p : Par × E ↦ f p.swap) q.swap‖ ≤
          Bprimary j * currentCoefficientScale R₀ n ^ (j - Rstar) ∧
        ‖iteratedFDeriv ℝ j (fun y ↦ f (y, q.2)) q.1‖ ≤
          Bprimary j * currentCoefficientScale R₀ n ^ (j - Rstar)) ∧
      ∀ C : OpenPartialHomeomorph TC TC,
        closedBall (z.1, z) c.targetRadius ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m, cNorm (closedBall (z.1, z) c.targetRadius) m (twoTimePhase C) ≤
          c.phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q.1)) →
      ∀ adj : Bool, ∀ j,
        cNorm K j (fullSourceJointPhase adj (curriedPhase c.radialSection C)
          (sourcePhase Q)) ≤
          Aphase j * currentCoefficientScale R₀ n ^ (j - Rstar) ∧
        ∀ t (v : (E × Par) × CW), ((t, v.1), v.2) ∈ K →
          ‖iteratedFDeriv ℝ j (fun w : (E × Par) × CW ↦
            fullSourceJointPhase adj (curriedPhase c.radialSection C)
              (sourcePhase Q) ((t, w.1), w.2)) v‖ ≤
            Aphase j * currentCoefficientScale R₀ n ^ (j - Rstar) := by
  intro z O KP K sourcePhase hO hOc hOK
  have hpositive := exists_physical_history_protected_incidence_profiles T c hc hε hεroot
    hεtarget hAp hg hphysical hAc hA G hr hrR hR ext hextcenter hextradius hBband hStar hreserve horder
    hO hOc hOK
  cases negative
  · exact hpositive
  · obtain ⟨χ,hχ,hcχ,heχ,SP,hSP,BP,_AP,hBP,_hAP,hpositive⟩ := hpositive
    have hprimary := protected_incidence_full_source_domain T c hc hεroot hphysical hA
    have hgeom := fullSourceSignedCarrier_geometry z ε hAc hO hOc hOK
    have hKP : IsCompact KP := by
      have hx := isCompact_closure_retained_physicalBox z (2*ε)
      simp only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] at hx
      exact hx.prod hAc
    have hpos v (hv : v ∈ K) : 0 < c.radialSection (spatialPart v.2.snd) :=
      (fullSourceSignedCarrier_normalizes c.radialSection z hε hAp hg hO hOc hOK false hv).1
    have hmap adj : MapsTo (ConicPhase.normalize c.radialSection ∘ fullSourceGraphPoint adj) K
        (closedBall (z.1,z) c.targetRadius) := fun _ hv ↦
      closedBall_subset_closedBall hεtarget
        (fullSourceSignedCarrier_normalizes c.radialSection z hε hAp hg hO hOc hOK adj hv).2
    have hprofiles adj := exists_physical_history_negative_full_source_joint_phase_profiles T
      c.index adj c.radialSection hgeom.1 (isCompact_closedBall _ _) hKP hpos (hmap adj)
      (fun v hv ↦ (hgeom.2 v hv).1) (fun v hv ↦ (hgeom.2 v hv).2) hprimary G hr hrR hR
      ext hextcenter hextradius hBband hStar hreserve horder (isCompact_closedBall x RQ)
      c.phaseCost c.phaseCost_pos
    choose SF hSF AF hAF hprofile using hprofiles
    let Aphase := fun j ↦ AF false j + AF true j
    have hAFle adj j : AF adj j ≤ Aphase j := by
      cases adj <;> dsimp [Aphase] <;> linarith [hAF false j,hAF true j]
    refine ⟨χ,hχ,hcχ,heχ,max SP (max (SF false) (SF true)),
      hSP.trans (le_max_left _ _),BP,Aphase,hBP,fun j ↦ add_nonneg (hAF false j) (hAF true j),?_⟩
    intro Q f
    obtain ⟨hf,_hef,hp⟩ := hpositive Q
    have he : f = -(fun q : E × Par ↦ χ q * T.fullSourcePhaseInCoordinates c.index Q q.1 q.2) := by
      funext q
      exact mul_neg _ _
    refine ⟨?_,?_,?_⟩
    · rw [he]
      exact hf.neg
    · intro q hq
      filter_upwards [heχ q hq] with p hp
      simp only [f,hp,one_mul]
      rfl
    · intro R₀ hR₀ n u ell hu hQ
      refine ⟨?_,?_⟩
      · intro j q hq
        have hj := (hp R₀ ((le_max_left _ _).trans hR₀) n u ell hu hQ).1 j q hq
        have hn₁ : (fun p : Par × E ↦ f p.swap) =
            -(fun p : Par × E ↦ χ p.swap * T.fullSourcePhaseInCoordinates c.index Q p.swap.1 p.swap.2) := by
          funext p
          rw [he]
          rfl
        have hn₂ : (fun y : E ↦ f (y,q.2)) =
            -(fun y : E ↦ χ (y,q.2) * T.fullSourcePhaseInCoordinates c.index Q y q.2) := by
          funext y
          rw [he]
          rfl
        rw [hn₁,hn₂,iteratedFDeriv_neg_apply,iteratedFDeriv_neg_apply,norm_neg,norm_neg]
        exact hj
      · intro C hbuffer hsmooth hphase adj j
        have hRS : SF adj ≤ R₀ := by
          apply le_trans _ ((le_max_right _ _).trans hR₀)
          cases adj
          · exact le_max_left _ _
          · exact le_max_right _ _
        obtain ⟨hnorm,hjets⟩ := hprofile adj R₀ hRS n u ell hu Q hQ C hbuffer hsmooth hphase j
        have hL : 1 ≤ currentCoefficientScale R₀ n := one_le_currentCoefficientScale
          (by linarith [hSP.trans ((le_max_left _ _).trans hR₀)] : 1 ≤ R₀) n
        have hbound := mul_le_mul_of_nonneg_right (hAFle adj j)
          (pow_nonneg (zero_le_one.trans hL) (j-Rstar))
        exact ⟨hnorm.trans hbound,fun t v hv ↦ (hjets t v hv).trans hbound⟩

end JanetCartan.PhysicalPrimary
