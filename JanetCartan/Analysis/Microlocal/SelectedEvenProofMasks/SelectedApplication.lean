module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.EvenConclusion
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.Masks

/-!
# Even nested masks on the supplied selected finite family

The finite radial proof cover is constructed for the original selected chart
geometry. Its primitive roots and transported flows come from the SAME local
protection certificates. The even-mask constructor is then instantiated on
that refinement, and the existing conic interior and boundary-collar producers
are applied to those very masks. No solver, source cutoff or inverse is selected
again. Sources: `app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open SelectedSectorProtection
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.UniformAmplitudes
open RegularSector.FiniteAssembly RegularSector.FiniteEvolution RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.Characteristic.EvolutionIntegral
open ProtectedMasks ProtectedMasks.ConicInterior ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TP" => TwoTimePoint (Euclidean d)

/-- The source and comparison geometry fix the physical annulus before
the comparable phase band is specified. The radial refinement and even
masks are then constructed once for that band. This order allows the
original direct-residual carrier to prescribe its undilated section radii
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selectedSector_even_nested_proof_masks_of_coefficient_bound_with_prior_annulus
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hΩ : IsOpen Ω)
    (T speed G : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hc : ∀ p, LocalProtectionCertificate (f.chart p) (T p) (speed p) (G p) (rootCost p))
    (hradii : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    {Ωsource Γ : Set E} (hΓ : IsCompact Γ)
    {r Mglobal c C Lx ε : ℝ}
    (hr : 0 < r) (hMglobal : 0 ≤ Mglobal) (hcgraph : 0 < c) (hCgraph : 0 < C)
    (hLx : 0 ≤ Lx) (hε : 0 < ε)
    (hphysical : closedBall x RQ ⊆ ball 0 (2*r))
    (hΩΓ : Ωsource ⊆ interior Γ)
    (hΩsym : ∀ ξ ∈ Ωsource, -ξ ∈ Ωsource)
    (χ₂ : E → ℝ) (hχ₂ : HasCompactSupport χ₂)
    (hχ₂support : tsupport χ₂ ⊆ ball x f.physicalRadius)
    (hχ₂source : tsupport χ₂ ⊆ ball 0 r)
    {Ksource : Set E} (hKsource : IsCompact Ksource)
    (hsourceFrequency : ∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ interior Ωsource)
    {V : Set (E × E)} (hV : IsOpen V) (hSV : tsupport χ₂ ×ˢ Ksource ⊆ V)
    (hreflectV : physicalCovectorReflection '' (tsupport χ₂ ×ˢ Ksource) ⊆ V)
    (output : E → ℝ) (N : ℕ) :
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z := fun p : J ↦ ((coordinateSplit (i p) x).1,
      ((coordinateSplit (i p) x).2, (coordinateSplit (i p) p.val.val).2))
    let εroot := fun p : J ↦ (f.chart p).coefficientRadius
    let γ := fun p : J ↦ (f.chart p).maskRadius
    EqOn f.inputMask 1 (tsupport χ₂) ∧
    ∃ a > (0 : ℝ), ∃ b > a, ∀ (aPhase bPhase : J → ℝ), (∀ p, 0 < aPhase p) →
    ∃ (n : J → ℕ) (cRad : (j : J) → Fin (n j) → ℝ)
      (hcRad : ∀ j k, 0 < cRad j k)
      (Urad : (j : J) → Fin (n j) → Set (RootState (Euclidean d))),
    ∃ (θ Rbase εcollar δT δI : ℝ) (H Hcollar : ℕ → ℝ)
      (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ),
      0 < θ ∧ 0 < Rbase ∧ 0 < δI ∧ (∀ k, 0 ≤ H k) ∧
      0 < εcollar ∧ 0 < δT ∧ (∀ j, εcollar ≤ γ j) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ εcollar / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ εcollar / 2} ∧
      tsupport (1 - χ) ⊆ {p | εcollar / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ Hcollar k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ Hcollar k) ∧
      ∀ (Q : E → Fin (d+1) → MetricTensor (d+1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2*r)) 3 Q ≤ Mglobal →
      let h := fun p : f.centers ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
      let D := fun p : f.centers ↦ fieldDomain (coordinateSplit (i p)) Ω (ℓ p)
        (z p).2.2 (εroot p)
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph TP TP),
        (∀ p, SelectedProtectionData (f.chart p) (T p) (speed p) (G p) (rootCost p)
          Q (Φ p) (Cphase p)) →
        (∀ p, ContDiffOn ℝ ∞ (h p) (D p)) →
        (∀ p w, w ∈ D p → ∀ t : ℝ, 0 < t →
          h p (w.1, (w.2.1, t • w.2.2)) = t * h p w) →
        (∀ p, (Cphase p : TP → TP) = twoTimeProjection (Φ p)) →
        (∀ p, (Cphase p).source = ball ((z p).1, z p) (f.chart p).sourceRadius) →
        (∀ p, closedBall ((z p).1, z p) (f.chart p).targetRadius ⊆ (Cphase p).target) →
        (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (Cphase p)) (Cphase p).target) →
        (∀ p q, q ∈ (Cphase p).target → HasFDerivAt (twoTimePhase (Cphase p))
          (twoTimePhaseDifferential (h p) (Φ p) (Cphase p) q) q) →
        (∀ p w, w ∈ ball (z p) (f.chart p).sourceRadius →
          twoTimePhase (Cphase p) (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, r ≤ (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ωsource, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ Γ) →
        SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource V Γ output N aPhase bPhase
          n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase := by
  classical
  intro J i ℓ z εroot γ
  let ρ := fun p : J ↦ (f.chart p).rootRadius / 3
  let W := closedBall x RQ
  let S := tsupport χ₂ ×ˢ Ksource
  let Δ := 6 * f.physicalRadius
  refine ⟨selected_source_recut_plateau f χ₂ hχ₂support, ?_⟩
  have hσr (j : J) : (f.chart j).sourceRadius < (f.chart j).rootRadius / 2 := by
    have hsmall := (hc j).2.2.2.2.1
    have hpos := (f.chart j).rootRadius_pos
    linarith
  have hσR (j : J) : (f.chart j).sourceRadius ≤ (f.chart j).rootRadius :=
    (hσr j).le.trans (by linarith [(f.chart j).rootRadius_pos])
  let Splus := physicalSymmetricHull S
  have hS : IsCompact S := hχ₂.isCompact.prod hKsource
  have hSplus : IsCompact Splus := isCompact_physicalSymmetricHull hS
  have hSVplus : Splus ⊆ V := union_subset hSV hreflectV
  have hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ωsource :=
    fun p hp ↦ ⟨hχ₂source hp.1, hsourceFrequency p.2 hp.2⟩
  have hSB : ∀ p ∈ S, p.1 ∈ W := by
    intro p hp
    apply f.physicalBall_coefficientDomain
    exact ball_subset_closedBall ((ball_subset_ball (by linarith [f.physicalRadius_pos]))
      (hχ₂support hp.1))
  have hSBplus : ∀ p ∈ Splus, p.1 ∈ W := by
    rintro p (hp | ⟨q, hq, rfl⟩)
    · exact hSB p hp
    · exact hSB q hq
  obtain ⟨κ, hκ, hκspeed⟩ := exists_selected_common_root_speed f T speed G rootCost hc
  have hΔ : 0 ≤ Δ := mul_nonneg (by norm_num) f.physicalRadius_pos.le
  obtain ⟨a, ha, b, hab, hselect⟩ :=
    exists_uniform_even_nested_physicalDirectLocalizers_with_prior_annulus
      hSplus (physicalSymmetricHull_reflection S) (isCompact_closedBall x RQ) hΓ.isClosed
      hr hMglobal hcgraph hCgraph hLx hκ hΔ hε hSBplus hphysical
      (physicalSymmetricHull_source_geometry hΩsym hsource) hΩΓ hV hSVplus N
  refine ⟨a, ha, b, hab, ?_⟩
  intro aPhase bPhase haPhase
  choose n cRad hcRad zj rj Rj Urad hgeom hradcover using fun j : J ↦
    exists_finite_radial_chart_buffers (ℓ j) (z j) (f.chart j).maskRadius_pos
      (haPhase j) (b := bPhase j) (f.chart j).sourceRadius_pos.le (hσr j) (hσR j)
  let Jrad := (j : J) × Fin (n j)
  obtain ⟨θ, Rbase, H, hθ, hRbase, hH, hconstruct⟩ := hselect
      (fun k : Jrad ↦ (cRad k.1 k.2)⁻¹ • ℓ k.1)
      (fun k : Jrad ↦ cRad k.1 k.2 • (z k.1).2.2)
      (fun k : Jrad ↦ cRad k.1 k.2 * εroot k.1)
      (fun k : Jrad ↦ cRad k.1 k.2 * G k.1)
      (fun k ↦ mul_nonneg (hcRad k.1 k.2).le (hc k.1).2.2.1.le)
  obtain ⟨δI, hδI, hgapI⟩ := exists_uniform_conic_interior_phaseGradientSquare_gap hθ eI
    n ℓ z γ (fun j ↦ (f.chart j).sourceRadius) (fun j ↦ (f.chart j).rootRadius)
    aPhase bPhase cRad hcRad Urad (fun j ↦ (f.chart j).maskRadius_pos) haPhase hσR hradcover
  obtain ⟨εcollar, δT, χ, Hcollar, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, hgapT⟩ := exists_uniform_finiteFamily_rootFlow_collar_of_diagonal
      eT ℓ z (fun _ ↦ x) (fun _ ↦ RQ) ρ T (fun j ↦ (f.chart j).sourceRadius)
      (fun j ↦ (f.chart j).targetRadius / 2) γ (fun j ↦ (f.chart j).phaseCost 2)
      aPhase bPhase hθ hMglobal (fun j ↦ (f.chart j).maskRadius_pos)
      (fun j ↦ (selected_mask_radius_protection_bounds f hradii j).2.1)
      (fun j ↦ (f.chart j).maskRadius_lt_sourceRadius.le)
      (fun j ↦ (f.chart j).phaseCost_pos 2 |>.le) haPhase (Δ := Δ)
  refine ⟨n, cRad, hcRad, Urad, θ, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, hRbase, hδI, hH, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, ?_⟩
  intro Q hQ hQM h D Φ Cphase hd hh hhom hCphase hCsource htarget hsmooth hdiff hdiag
    I g charts hgr hderiv hnorm hcover hbuffer
  have hroot j := selected_root_mask_primitives f j (hc j) Q (Φ j) (Cphase j) (hd j)
  have hD j : IsOpen (D j) := isOpen_fieldDomain _ hΩ _ _ _
  have hradial j := fieldRoot_maskAssembly_radial_invariance _ _ _ _ _ Q _ (hhom j)
  let irad : Jrad → Fin (d+1) := fun k ↦ i k.1
  let hrad : Jrad → Z → ℝ := fun k ↦ h k.1
  let Φrad : Jrad → Z × ℝ → Z :=
    fun k ↦ radialFlow (cRad k.1 k.2) (hcRad k.1 k.2).ne' (Φ k.1)
  let Ur : Jrad → Set Z := fun k ↦ Urad k.1 k.2
  let Kr : Jrad → Set Z := fun k ↦ rootRadialEquiv (cRad k.1 k.2) (hcRad k.1 k.2).ne' ''
    closedBall (z k.1) (f.chart k.1).rootRadius
  have hUK (k : Jrad) : Ur k ⊆ Kr k := (hgeom k.1 k.2).2.2.2.2.2.2.1
  have hKrD (k : Jrad) : Kr k ⊆ D k.1 :=
    radial_image_subset_fieldDomain _ (hcRad k.1 k.2) (hroot k.1).1
  have hprad (k : Jrad) : ∀ v ∈ Ur k ∪ Kr k,
      v.2.2 ∈ closedBall (cRad k.1 k.2 • (z k.1).2.2) (cRad k.1 k.2 * εroot k.1) ∧
      (1 / 2 : ℝ) ≤ ((cRad k.1 k.2)⁻¹ • ℓ k.1) v.2.2 ∧
      |hrad k v| ≤ ((cRad k.1 k.2)⁻¹ • ℓ k.1) v.2.2 * (cRad k.1 k.2 * G k.1) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (union_subset (hUK k) Subset.rfl) hv
    obtain ⟨hfreq, hsection, hvalue⟩ := (hroot k.1).2.2.1 w hw
    refine ⟨radial_frequency_mem_closedBall (hcRad k.1 k.2) hfreq, ?_, ?_⟩
    · simpa only [radial_section_apply] using hsection
    · rw [radial_section_apply]
      change |h k.1 (rootRadialEquiv _ _ w)| ≤ _
      rw [rootRadialEquiv_apply, hhom k.1 w ((hroot k.1).1 hw) _ (hcRad k.1 k.2),
        abs_mul, abs_of_pos (hcRad k.1 k.2)]
      exact (mul_le_mul_of_nonneg_left hvalue (hcRad k.1 k.2).le).trans_eq (by ring)
  have hbrad (k : Jrad) : ∀ v ∈ Ur k ∪ Kr k,
      (coordinateSplit (irad k)).symm (v.1, v.2.1) ∈ W := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (union_subset (hUK k) Subset.rfl) hv
    exact (hroot k.1).2.2.2.1 w hw
  have hfrad (k : Jrad) : ODE.IsSmoothFlowOn (rootHamiltonField (hrad k))
      (zj k.1 k.2) (Rj k.1 k.2) (rj k.1 k.2) (T k.1) (Φrad k) := by
    obtain ⟨_, _, _, _, _, _, _, hclosed, hopen, hrange⟩ := hgeom k.1 k.2
    exact isSmoothFlowOn_radialFlow (hD k.1) (hh k.1) (hradial k.1) (hcRad k.1 k.2)
      (hd k.1).2.1 (hroot k.1).1 hclosed hopen hrange
  obtain ⟨m, heven, hmPlus, hfirstPlus, hsourceShoulder, hreachablePlus, hshoulder, hjet,
    hactual, _, _, _, hunit⟩ := hconstruct Q hQ hQM irad hrad Φrad Ur Kr (fun k ↦ D k.1) W
      (fun k ↦ chartInputMask f k.1) (fun k ↦ endpointOutputMask f k.1 output)
      (fun k ↦ (hgeom k.1 k.2).2.2.2.1)
      (fun _ ↦ (isCompact_closedBall _ _).image (rootRadialEquiv _ _).continuous)
      isClosed_closedBall (fun k ↦ (hUK k).trans (hKrD k)) hKrD
      (hphysical.trans ball_subset_closedBall) (fun k ↦ hD k.1) (fun k ↦ hh k.1)
      (fun k ↦ (hroot k.1).2.1) hprad hbrad
      (fun k v hv ↦ (hκspeed k.1).trans ((hroot k.1).2.2.2.2 v (hKrD k hv)))
      (fun k ↦ zj k.1 k.2) (fun k ↦ Rj k.1 k.2) (fun k ↦ rj k.1 k.2)
      (fun k ↦ T k.1) hfrad
      (fun k ↦ (selected_common_elapsed_lt_evolutionTime f k.1 (hc k.1)).2.2)
      (fun k ↦ (hgeom k.1 k.2).2.2.2.2.1) I g charts hgr hderiv hnorm hcover hbuffer
  let Ractual := physicalDirectRelation irad hrad Φrad Ur Kr W
    (fun k ↦ chartInputMask f k.1) (fun k ↦ endpointOutputMask f k.1 output) Δ
  have hreachSub k : reachableAt Ractual S k ⊆ reachableAt Ractual Splus k := by
    rintro q ⟨p, hp, hc⟩
    exact ⟨p, Or.inl hp, hc⟩
  have hm k : IsBufferedLocalizer (m k) (reachableAt Ractual S k.val)
      (physicalProtectedRegion Γ) :=
    ⟨(hmPlus k).smooth, (hmPlus k).range, (hmPlus k).compactSupport,
      (hmPlus k).support_subset, (hreachSub k.val).trans (hmPlus k).plateau⟩
  have hfirst : IsBufferedLocalizer (m 0) S V :=
    ⟨hfirstPlus.smooth, hfirstPlus.range, hfirstPlus.compactSupport,
      hfirstPlus.support_subset, subset_union_left.trans hfirstPlus.plateau⟩
  have hreachable k : cthickening θ (reachableAt Ractual S k.val) ⊆ interior {p | m k p = 1} :=
    (cthickening_subset_of_subset _ (hreachSub k.val)).trans (hreachablePlus k)
  have htargetγ j : closedBall ((z j).1, z j) (2 * γ j) ⊆ (Cphase j).target := by
    apply (closedBall_subset_closedBall ?_).trans (htarget j)
    have hbound := (selected_mask_radius_protection_bounds f hradii j).2.1
    dsimp [γ] at *
    linarith
  choose Gext hGcont hGsmooth hGhom hGerm using fun j ↦
    ConicPhase.exists_continuous_conicPhase_extension (ℓ j) (Cphase j)
      (isCompact_closedBall _ _) (htargetγ j) (hsmooth j)
  change SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource V Γ output N aPhase bPhase
    n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase
  dsimp only [SelectedSectorEvenNestedMaskConclusion]
  refine ⟨Gext, m, heven, fun j ↦ ⟨hGcont j, hGsmooth j, hGhom j, hGerm j⟩,
    hm, hfirst, hsourceShoulder, hreachable, hshoulder, hjet, hactual, ?_, ?_, ?_, hunit, ?_, ?_⟩
  · exact fun k j ↦ IsBufferedLocalizer.canonicalProofLocalizer (coordinateSplit (i j)) (hm k)
  · intro k j
    exact canonicalProofLocalizer_support_bounds (i j)
      (fun p hp ↦ (hshoulder k (self_subset_cthickening _ hp)).1)
  · intro k j l p
    rw [norm_iteratedFDeriv_canonicalProofLocalizer]
    exact hjet k l _
  · intro k χ₂ χ₃ hcut p hp q hpq
    exact sourceRecutRelation_mem_closed_shoulder_plateau (hactual k) hcut hp hpq
  · intro k j backward Rf hRf x' y' r' p hr' hrγ ht hy hη hin hout
    have hI := hgapI i h Φ Cphase D W Δ hCphase hCsource htargetγ
      (fun j ↦ (hroot j).1) (fun j w hw ↦ (hroot j).2.2.2.1 w hw) hhom hdiff
      (fun j ↦ selected_inverse_complete_segments f j Q (Φ j) (Cphase j) (hd j))
      (m k.castSucc) (m k.succ) (hunit k) j backward Rf hRf x' y' r' p
      hr' hrγ ht hy hη hin hout
    have hQMlocal : cNorm (closedBall x RQ) 3 Q ≤ Mglobal :=
      (cNorm_mono_set_of_contDiffAt (hphysical.trans ball_subset_closedBall)
        (isCompact_closedBall _ _) (fun _ _ ↦ hQ.contDiffAt.of_le (by simp))).trans hQM
    have hthird (r : ℝ) : 3 * (r / 3) = r := by ring
    have hdouble (r : ℝ) : 2 * (r / 2) = r := by ring
    have hT r₁ (hr₁ : r₁ ∈ Icc 0 Δ) (hrε : r₁ ≤ εcollar) :=
      hgapT Q i Φ Cphase (fun _ ↦ hQMlocal)
        (fun j ↦ by simpa only [hdouble] using htarget j) hsmooth
        (fun j ↦ by
          simpa only [ρ, hthird, hdouble] using (hd j).2.2.2.2.2.2.2.2.2.2.2.2.1 2)
        hdiag (m k.castSucc) (m k.succ)
        (fun q hq ↦ hunit k q hq q (Or.inl rfl)) j backward Rf hRf x' y' r₁ p
        hr₁ hrε ht hy hη hin hout
    have hext r₁ (hr₁ : r₁ ∈ Icc 0 Δ) (hrγ₁ : r₁ ≤ γ j) :=
      phaseGradientSquare_normalized_extension_eq eT eI (ℓ j) (Cphase j) (hGerm j)
        hRf backward x' y' (r₁, p)
        (elapsedChartPoint_mem_conic_boundary_buffer (ℓ j) (z j) (f.chart j).maskRadius_pos
          (haPhase j) p ⟨hr₁.1, hrγ₁⟩ ht hy hη)
    have hIext := (hext r' hr' hrγ).1 ▸ hI
    have hText r₁ (hr₁ : r₁ ∈ Icc 0 Δ) (hrε : r₁ ≤ εcollar) :=
      (hext r₁ hr₁ (hrε.trans (hεγ j))).2 ▸ hT r₁ hr₁ hrε
    refine ⟨⟨hI, hT r' hr'⟩, hIext, hText r' hr', ?_, ?_, ?_, ?_⟩
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp (hδI.trans_le hI)
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp
        (hδT.trans_le (hT 0 ⟨le_rfl, hΔ⟩ hεcollar.le))
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp (hδI.trans_le hIext)
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp
        (hδT.trans_le (hText 0 ⟨le_rfl, hΔ⟩ hεcollar.le))

/-- Construct the full even nested-mask conclusion on the SAME supplied
`ActualMaskFamily`. Constants, radial proof cover, collar and derivative
profiles precede the current coefficient/history. The original source is
retained; only the proof carrier also includes its reflection. Symmetry of
`Omega` is supplied by initialized signed protection. The reflected source's
inclusion in the original buffer is necessary, as proved by
`reflected_source_subset_of_even_bufferedLocalizer`; it follows from symmetry
of the actual source cutoff, without replacing that cutoff.

All positive phase gaps and source recuts are derived on the constructed masks
from the original root certificates and phase identities. No mask evenness,
chain protection, derivative gap or real residual estimate is assumed
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selectedSector_even_nested_proof_masks_of_coefficient_bound
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hΩ : IsOpen Ω)
    (T speed G : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hc : ∀ p, LocalProtectionCertificate (f.chart p) (T p) (speed p) (G p) (rootCost p))
    (hradii : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    {Ωsource Γ : Set E} (hΓ : IsCompact Γ)
    {r Mglobal c C Lx ε : ℝ}
    (hr : 0 < r) (hMglobal : 0 ≤ Mglobal) (hcgraph : 0 < c) (hCgraph : 0 < C)
    (hLx : 0 ≤ Lx) (hε : 0 < ε)
    (hphysical : closedBall x RQ ⊆ ball 0 (2*r))
    (hΩΓ : Ωsource ⊆ interior Γ)
    (hΩsym : ∀ ξ ∈ Ωsource, -ξ ∈ Ωsource)
    (χ₂ : E → ℝ) (hχ₂ : HasCompactSupport χ₂)
    (hχ₂support : tsupport χ₂ ⊆ ball x f.physicalRadius)
    (hχ₂source : tsupport χ₂ ⊆ ball 0 r)
    {Ksource : Set E} (hKsource : IsCompact Ksource)
    (hsourceFrequency : ∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ interior Ωsource)
    {V : Set (E × E)} (hV : IsOpen V) (hSV : tsupport χ₂ ×ˢ Ksource ⊆ V)
    (hreflectV : physicalCovectorReflection '' (tsupport χ₂ ×ˢ Ksource) ⊆ V)
    (output : E → ℝ) (N : ℕ)
    (aPhase bPhase : f.centers → ℝ) (haPhase : ∀ p, 0 < aPhase p) :
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z := fun p : J ↦ ((coordinateSplit (i p) x).1,
      ((coordinateSplit (i p) x).2, (coordinateSplit (i p) p.val.val).2))
    let εroot := fun p : J ↦ (f.chart p).coefficientRadius
    let γ := fun p : J ↦ (f.chart p).maskRadius
    EqOn f.inputMask 1 (tsupport χ₂) ∧
    ∃ (n : J → ℕ) (cRad : (j : J) → Fin (n j) → ℝ)
      (hcRad : ∀ j k, 0 < cRad j k)
      (Urad : (j : J) → Fin (n j) → Set (RootState (Euclidean d))),
    ∃ (θ a b Rbase εcollar δT δI : ℝ) (H Hcollar : ℕ → ℝ)
      (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ),
      0 < θ ∧ 0 < a ∧ a < b ∧ 0 < Rbase ∧ 0 < δI ∧ (∀ k, 0 ≤ H k) ∧
      0 < εcollar ∧ 0 < δT ∧ (∀ j, εcollar ≤ γ j) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ εcollar / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ εcollar / 2} ∧
      tsupport (1 - χ) ⊆ {p | εcollar / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ Hcollar k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ Hcollar k) ∧
      ∀ (Q : E → Fin (d+1) → MetricTensor (d+1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2*r)) 3 Q ≤ Mglobal →
      let h := fun p : f.centers ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
      let D := fun p : f.centers ↦ fieldDomain (coordinateSplit (i p)) Ω (ℓ p)
        (z p).2.2 (εroot p)
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph TP TP),
        (∀ p, SelectedProtectionData (f.chart p) (T p) (speed p) (G p) (rootCost p)
          Q (Φ p) (Cphase p)) →
        (∀ p, ContDiffOn ℝ ∞ (h p) (D p)) →
        (∀ p w, w ∈ D p → ∀ t : ℝ, 0 < t →
          h p (w.1, (w.2.1, t • w.2.2)) = t * h p w) →
        (∀ p, (Cphase p : TP → TP) = twoTimeProjection (Φ p)) →
        (∀ p, (Cphase p).source = ball ((z p).1, z p) (f.chart p).sourceRadius) →
        (∀ p, closedBall ((z p).1, z p) (f.chart p).targetRadius ⊆ (Cphase p).target) →
        (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (Cphase p)) (Cphase p).target) →
        (∀ p q, q ∈ (Cphase p).target → HasFDerivAt (twoTimePhase (Cphase p))
          (twoTimePhaseDifferential (h p) (Φ p) (Cphase p) q) q) →
        (∀ p w, w ∈ ball (z p) (f.chart p).sourceRadius →
          twoTimePhase (Cphase p) (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, r ≤ (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ωsource, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ Γ) →
        SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource V Γ output N aPhase bPhase
          n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase := by
  dsimp only
  obtain ⟨hrecut, a, ha, b, hab, h⟩ :=
    exists_selectedSector_even_nested_proof_masks_of_coefficient_bound_with_prior_annulus
      f hΩ T speed G rootCost hc hradii eT eI hΓ hr hMglobal hcgraph hCgraph hLx hε
      hphysical hΩΓ hΩsym χ₂ hχ₂ hχ₂support hχ₂source hKsource hsourceFrequency
      hV hSV hreflectV output N
  obtain ⟨n, cRad, hcRad, Urad, θ, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, hmask⟩ := h aPhase bPhase haPhase
  exact ⟨hrecut, n, cRad, hcRad, Urad, θ, a, b, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, ha, hab, hmask⟩

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
