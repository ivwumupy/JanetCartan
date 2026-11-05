module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourcePhase
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.JointProfiles
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.ProtectionCertificates.LocalChart

/-!
# History phase profiles on the selected full-source incidence carrier

The supplied protected chart retains the original physical buffer. Apply the
existing full-source history estimates to its signed carrier, with the original
independent covectors and any compact incidence closure. One representative and
all constants precede the varying coefficients, histories and chart witnesses.
Consumer: the primary and joint phase inputs of the complete elapsed envelopes
(`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open ActualCarriers ActualCarriers.CurrentFullPhase HamiltonPhase FrozenMenu CompatibleResponse
open ConstructedCarrierJets GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.AlgebraicChart
open FullSourceStationary FullSourceEnvelopes LeadingWave.FullModulation DirectEvolution
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "CW" => CarrierVariables (d + 1)

/-- The selected protection certificate supplies the entire original physical
buffer for every independent source covector in the incidence closure.
No newly anchored primary source is introduced
(`app:ch_response:eq:response-exact-phase`). -/
theorem protected_incidence_full_source_domain
    {Ω : Set E} {x ξ : E} {RQ M : ℝ}
    (c : LocalChart Ω x RQ (cubeStress (d + 1)) ξ M)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hc : LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost)
    {ε : ℝ} (hε : ε ≤ c.rootRadius)
    (hphysical : closedBall x RQ ⊆ ball 0 T.physicalRadius)
    {A : Set Par}
    (hA : ∀ p ∈ A, p.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius) :
    let z := ((coordinateSplit c.index x).1, ((coordinateSplit c.index x).2,
      (coordinateSplit c.index ξ).2))
    ∀ q ∈ closure (elapsedPhysicalBox z ε) ×ˢ A,
      ((primaryCoordinateChange c.index).symm q.1, q.2.2) ∈ phaseDomain T := by
  intro z q hq
  obtain ⟨_, _, _, _, _, _, _, _, hroot, _⟩ := hc
  have hp := retained_primary_physical_buffer c.index z hε
    (fun w hw ↦ (hroot w hw).2.1) hq.1
  exact T.full_source_mem_phaseDomain_of_physical_buffer
    (ball_subset_closedBall (hphysical hp)) (hA q.2 hq.2)

/-- Apply the actual history producers to the SAME protected sector and full
incidence closure. One primary representative and one pair of graded constants
precede all coefficients and histories; both original joint phase orientations
retain reserve `Rstar+3` and the independent covector. This discharges the
primary and raw joint-phase profile inputs of the full elapsed envelopes
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_protected_incidence_full_source_history_profiles
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
    {rStar Rstar kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : Rstar + 3 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    let z := ((coordinateSplit c.index x).1, ((coordinateSplit c.index x).2,
      (coordinateSplit c.index ξ).2))
    let O := retainedOpenAnnularFrequencyCarrier c.radialSection z.2.2 (ε / 2) aperture g Rad
    let KP := closure (elapsedPhysicalBox z ε) ×ˢ A
    let K := fullSourceSignedCarrier z ε A O
    IsOpen O → Convex ℝ O → IsCompact (closure O) →
    ∃ χ : E × Par → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ q ∈ KP, χ =ᶠ[𝓝 q] (fun _ ↦ 1)) ∧
    ∃ S : ℝ, 2 ≤ S ∧ ∃ Bprimary Aphase : ℕ → ℝ,
      (∀ j, 0 ≤ Bprimary j) ∧ (∀ j, 0 ≤ Aphase j) ∧ ∀ Q,
      let f := fun q : E × Par ↦ χ q * T.fullSourcePhaseInCoordinates c.index Q q.1 q.2
      ContDiff ℝ ∞ f ∧ (∀ q ∈ KP, f =ᶠ[𝓝 q] Function.uncurry (T.fullSourcePhaseInCoordinates c.index Q)) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
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
          (T.fullSourcePhaseInCoordinates c.index Q)) ≤
          Aphase j * currentCoefficientScale R₀ n ^ (j - Rstar) ∧
        ∀ t (v : (E × Par) × CW), ((t, v.1), v.2) ∈ K →
          ‖iteratedFDeriv ℝ j (fun w : (E × Par) × CW ↦
            fullSourceJointPhase adj (curriedPhase c.radialSection C)
              (T.fullSourcePhaseInCoordinates c.index Q) ((t, w.1), w.2)) v‖ ≤
            Aphase j * currentCoefficientScale R₀ n ^ (j - Rstar) := by
  intro z O KP K hO hOc hOK
  have hprimary := protected_incidence_full_source_domain T c hc hεroot hphysical hA
  have hgeom := fullSourceSignedCarrier_geometry z ε hAc hO hOc hOK
  have hKP : IsCompact KP := by
    have hx := isCompact_closure_retained_physicalBox z (2 * ε)
    simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hx
    exact hx.prod hAc
  obtain ⟨χ, hχ, hcχ, heχ, SP, hSP, BP, hBP, hprimaryProfile⟩ :=
    exists_fullSource_history_phase_representative T c.index hKP hprimary G hr hrR hR
      ext hextcenter hextradius hStar hreserve horder
  have hpos v (hv : v ∈ K) : 0 < c.radialSection (spatialPart v.2.snd) :=
    (fullSourceSignedCarrier_normalizes c.radialSection z hε hAp hg hO hOc hOK false hv).1
  have hmap adj : MapsTo (ConicPhase.normalize c.radialSection ∘ fullSourceGraphPoint adj) K
      (closedBall (z.1, z) c.targetRadius) := fun _ hv ↦
    closedBall_subset_closedBall hεtarget
      (fullSourceSignedCarrier_normalizes c.radialSection z hε hAp hg hO hOc hOK adj hv).2
  have hprofiles adj := T.exists_admissible_history_full_source_joint_phase_profiles
    c.index adj c.radialSection hgeom.1 (isCompact_closedBall _ _) hKP hpos (hmap adj)
    (fun v hv ↦ (hgeom.2 v hv).1) (fun v hv ↦ (hgeom.2 v hv).2) hprimary G hr hrR hR
    ext hextcenter hextradius hStar hreserve horder (isCompact_closedBall x RQ)
    c.phaseCost c.phaseCost_pos
  choose SF hSF AF hAF hprofile using hprofiles
  let Aphase := fun j ↦ AF false j + AF true j
  have hAFle adj j : AF adj j ≤ Aphase j := by
    cases adj <;> dsimp [Aphase] <;> linarith [hAF false j, hAF true j]
  refine ⟨χ, hχ, hcχ, heχ, max SP (max (SF false) (SF true)),
    hSP.trans (le_max_left _ _), BP, Aphase, hBP, fun j ↦ add_nonneg (hAF false j) (hAF true j), ?_⟩
  intro Q f
  obtain ⟨hf, hef, hp⟩ := hprimaryProfile Q
  refine ⟨hf, hef, ?_⟩
  intro R₀ hR₀ n u ell hu hQ
  refine ⟨hp R₀ ((le_max_left _ _).trans hR₀) n u ell hu hQ, ?_⟩
  intro C hbuffer hsmooth hphase adj j
  have hRS : SF adj ≤ R₀ := by
    apply le_trans _ ((le_max_right _ _).trans hR₀)
    cases adj
    · exact le_max_left _ _
    · exact le_max_right _ _
  obtain ⟨hnorm, hjets⟩ := hprofile adj R₀ hRS n u ell hu Q hQ C hbuffer hsmooth hphase j
  have hL : 1 ≤ currentCoefficientScale R₀ n := one_le_currentCoefficientScale
    (by linarith [hSP.trans ((le_max_left _ _).trans hR₀)] : 1 ≤ R₀) n
  have hbound := mul_le_mul_of_nonneg_right (hAFle adj j)
    (pow_nonneg (zero_le_one.trans hL) (j - Rstar))
  exact ⟨hnorm.trans hbound, fun t v hv ↦ (hjets t v hv).trans hbound⟩

end JanetCartan.ResponseTransfer.RetainedFactors
