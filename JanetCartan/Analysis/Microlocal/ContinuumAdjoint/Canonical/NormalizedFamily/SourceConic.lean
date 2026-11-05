module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourcePhase
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.UniformConic.Geometry

/-!
# Uniform conic inverse geometry for the actual source reference

The normalized Hamilton profiles supply the finite position reserve of the
literal canonical inverse and its original Jacobian. The retained incidence
geometry supplies the common balls, inverse gap and supported output shell.
All masks and constants precede the source scale. The phase-agreement radius
can be chosen after the outer geometry, so the global phase and the original
conic masks can be retained together.

Consumer: `UniformEndpoint.exists_uniform_scalarTransportCarrierAdjoint_periodic_raw_bound`,
in particular its `PrimitiveJetGeometry`, closed-image and output-domain inputs
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-Psi`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalConic CanonicalCarrier NormalizedFlowProfiles
open PhaseExtension NormalInputs DerivativeKernels ModifiedNormalSymbol
open ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct the finite normalized inverse jets and the closed supported image
for every admitted witness of the SAME actual source frame. The only varying
map is `sourceDilation H.map σ`; no unnormalized normal-pairing gap or operator
estimate is assumed. The normalized frame producer supplies admission and
closeness, and the normalized Hamilton producer supplies the position reserve
`2 * (n + 1) + 2`.

The outer radii precede the positive phase radius, and the smaller masks, the
buffered inverse and its constants precede `σ`. Thus the separately constructed
global phase can keep its own agreement radius on this very chart. The original
`normalChart`, `normalJetRescaling`, high-frequency threshold one and carrier
support are unchanged (`app:ch_background:prop:bg-adjoint`, `bg-Psi`,
`bg-jacobian`, `bg-full-complex-amplitude`, `bg-normalized`). -/
theorem exists_source_normalChart_geometry (H : FlatReference n)
    {c C : ℝ} (hP : P.IsValid c C) (hbounded : Bornology.IsBounded U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hcenterE : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E)
    {cap : ℝ} (hcap : 0 < cap) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r > (0 : ℝ), ∃ a > (0 : ℝ),
      6 * a < cap ∧ 6 * a ≤ r ∧ 6 * a < T.family.radius ∧
      4 * a < T.physicalRadius ∧ 4 * a < 1 / 2 ∧
      coefficientDomain z₀ r (6 * a) ⊆ E ∩ extensionDomain T ∧
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
      (∀ σ ∈ Ioc (0 : ℝ) σ₀,
        ∃ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold},
          Q.1 = ProjectedStressFrame.projectedStress (sourceDilation H.map σ)) ∧
    ∀ aPhase : ℝ, 0 < aPhase →
    ∃ rMask > (0 : ℝ), rMask < r ∧
    ∃ aMask > (0 : ℝ), aMask < a ∧ aMask < aPhase ∧ aMask ≤ rMask ∧
    ∃ B > (0 : ℝ), ∃ cJ > (0 : ℝ), ∃ b > (0 : ℝ),
    ∃ V L : Set (ℝ × Euclidean (n - 1)),
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Q.1 = ProjectedStressFrame.projectedStress (sourceDilation H.map σ) →
      let g := normalChart T Q z₀ ηb r (6 * a) aPhase
      let J := normalSupport T z₀ ηb rMask aMask
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) ∧
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G ∧
      (∀ p ∈ physicalParameterSet z₀ (6 * a),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) ∧
      PrimitiveJetGeometry g (normalJetRescaling T Q z₀ ηb r (6 * a) aPhase)
        (2 * (n + 1)) 1 B (cJ / ‖ηb‖) J
        (Prod.snd '' (carrierSupport z₀ (r := aMask))) ∧
      J ⊆ g.inputDomain ∧ IsClosed (g.push '' J) ∧ g.push '' J ⊆ g.outputDomain := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ extensionDomain T := by
    refine ⟨mem_ball_self T.physicalRadius_pos, ?_⟩
    change carrierParameters (spectatorCenter z₀, z₀ 0) ∈ parameterInterior (3 * P.radius / 2)
    rw [carrierParameters_spectatorCenter]
    exact fun i ↦ (hz₀ i).trans (by linarith [hP.1])
  obtain ⟨cap₀, hcap₀, hbuffers⟩ := exists_canonical_coefficient_buffers T hP hz₀ hk hinc
    (extensionDomain T) (extensionDomain_open T) hcenter
  obtain ⟨r, hr, a, ha, hacap, hdomain, har, haR, hcell, hcarrier,
    ρ, hρ, hρcap, hinput, τ, hτ, r', hr', hrr, hrρ, a', ha', haa, har', haρ,
    δ, hδ, cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, hactual⟩ :=
    UniformConic.exists_actual_refined_supported_geometry_in_open_before_geometry T
      (N := embeddingDimension n) hP hz₀ hk hinc hd
      (lt_min hcap₀ (lt_min hcap T.physicalRadius_pos))
      (E ∩ extensionDomain T) (hE.inter (extensionDomain_open T)) ⟨hcenterE, hcenter⟩
  obtain ⟨W, K, Vphase, Lphase, I, D, ε, hW, hK, hballW, hWK, hKdom,
    hVp, hLp, hLVp, hI, hinterval, hIT, hsegI, hseg, hDcar, hDreg, hDom,
    hfoot, hsupport, hε, hη, hJac⟩ :=
    hbuffers hr hρ (hρcap.trans_le (min_le_left _ _)) hinput
  have hphaseDomain : Vphase ⊆ extensionDomain T := fun _ hp ↦ (hDom hp).1
  have hLO : Lphase ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    have h := hphaseDomain (hLVp hp)
    exact ⟨h.1, fun i ↦ (h.2 i).trans (by linarith [hP.1])⟩
  obtain ⟨s₁, hs₁, hs₁1, Bpos, hBpos, hpos⟩ :=
    exists_source_transportPosition_bounds T H hP hbounded hphysical hLp hLO
  obtain ⟨s₂, hs₂, _, _, _, Qs, hQs, hsource, hreg, _⟩ :=
    exists_admitted_source_frame_profiles T H hbounded hphysical hδ
  let σ₀ := min s₁ s₂
  have hcap₁ {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) s₁ :=
    ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hcap₂ {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) s₂ :=
    ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  refine ⟨r, hr, a, ha,
    hacap.trans_le ((min_le_right _ _).trans (min_le_left _ _)), har, haR,
    by linarith [hacap.trans_le ((min_le_right _ _).trans (min_le_right _ _))],
    hcell, hdomain, hcarrier, σ₀, lt_min hs₁ hs₂, (min_le_left _ _).trans hs₁1,
    (fun σ hσ ↦ ⟨Qs σ (hcap₂ hσ), hQs σ (hcap₂ hσ)⟩), ?_⟩
  intro aPhase hphase
  obtain ⟨rMask, hrMask, hrrMask, hrMaskρ, aMask, haMask, haaMask, hphaseMask,
    harMask, haMaskρ⟩ := exists_normalSupport_radii hr' ha' hphase hρ
  obtain ⟨B, hB, hjets⟩ := exists_normalChart_primitiveJetGeometry T
    (aOuter := 6 * a) (aPhase := aPhase) hηb hr hρ hrMask haMask haMaskρ
    hrMaskρ hW hballW hK hWK hVp hLp hLVp hI hIT hsegI hseg
    (augmentedReferenceEquiv T hP hz₀ hinc hd)
    (frozenAugmentedChart T (augmentedInputCenter T (z₀ := z₀) (k := k)))
    hτ (norm_pos_iff.mpr hk) hε hη (hBpos (2 * (n + 1) + 2)).le
  refine ⟨rMask, hrMask, hrrMask.trans_le hrr, aMask, haMask,
    haaMask.trans_le haa, hphaseMask, harMask, B, hB, cJ, hcJ, b, hb,
    V, L, hV, hVc, hLc, hLV, ?_⟩
  intro σ hσ Q hQ
  have hclose : cNorm
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (ProjectedStressFrame.projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) < δ := by
    rw [← hQs σ (hcap₂ hσ)]
    apply (cNorm_mono_set_of_contDiffAt (hphysical.trans subset_closure)
      hbounded.isCompact_closure ?_).trans_lt (hsource σ (hcap₂ hσ)).2.2
    intro x hx
    exact ((hreg σ (hcap₂ hσ) x hx).sub contDiffAt_const).of_le (by simp)
  have hlow : cNorm
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (ProjectedStressFrame.projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) <
      T.family.threshold := by rw [← hQ]; exact Q.2.2
  have hgeometry := hactual (sourceDilation H.map σ)
    (contDiff_sourceDilation H.contDiff).contDiffOn
    (hsource σ (hcap₂ hσ)).1 (hsource σ (hcap₂ hσ)).2.1 hlow hclose
  simp only [← hQ] at hgeometry
  obtain ⟨hf, hslice, hInv, htrans, houtput, hrange, hgap, hbuffer, hshell, hupper⟩ := hgeometry
  have har₀ : a ≤ r := by linarith
  have hJ := normalSupport_subset_inputDomain T Q (z₀ := z₀) hηb hr ha har₀
    (hrrMask.le.trans hrr) (haaMask.le.trans haa) hphaseMask
  have hshell' : ∀ x : ContinuumNormalReduction.TransportSymbol.Variables n,
      ‖x.2.2‖ = ‖k‖ → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb rMask aMask) → (x, v) ∈ closedBall
          (frozenAugmentedChart T (augmentedInputCenter T (z₀ := z₀) (k := k))) τ := by
    intro x hx v hv
    exact hshell x hx v (closure_mono (image_mono
      (conicMaskSupport_mono z₀ ηb hrrMask.le haaMask.le)) hv)
  exact ⟨hf, hInv, htrans,
    hjets Q ((transportPosition_contDiffOn_extensionDomain T hP Q).mono hphaseDomain)
      (hpos σ (hcap₁ hσ) Q hQ _) hf hcJ hInv hV hLV
      htrans houtput hrange hgap hshell' hJ,
    hJ, normalSupport_image_isClosed T Q hηb hr ha har₀
      (hrrMask.le.trans hrr) (haaMask.le.trans haa) hphaseMask hInv htrans hf hV hLV,
    normalSupport_image_subset_outputDomain T Q hηb hr ha har₀
      (hrrMask.le.trans hrr) (haaMask.le.trans haa) hphaseMask⟩

end JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
