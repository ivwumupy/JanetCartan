module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedMeasuredSource.FrozenGap
public import JanetCartan.Iteration.PhysicalSeed.AngularFrozenUnits
public meta import JanetCartan.Iteration.PhysicalSeed.AngularTemplates

/-!
# Retain both caps through the same original FrozenGap construction

Replay the genuine original continuation on the one stronger selected tuple.
The additional angular certificate is retained, never recovered from a forgotten
weak choice. Consumer: the same original source inverse and
`PhysicalSampling.exists_original_scalar_sampling_bounds`
(`new:sec:order-of-choices`, `app:ch_background:prop:bg-inverse`).
-/

set_option warningAsError true
set_option maxRecDepth 4000
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalSeed.AngularFrozenGap
open ContinuumRow ContinuumRow.NormalizedSelection
open ContinuumNormal.SourceDensityLimitRealization
open ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open FullPhaseCharts ActualPhase ActualComparison
open CarrierVariation.FamilyInputs PositiveReference ProjectedStressFrame
open PositiveReference.FlowConstruction RetainedRowGeometry
open NullTransport ActualFlow FlowAmplitude CarrierSobolev GeometricProfile
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.PhaseExtension CommonMeasurement
open NormalizedBackground.SourceGeometry Pseudodifferential AmplitudeBound PeriodicLocalL2


declare_angular_retained exists_frozen_gap_with_angular_cap
  from JanetCartan.ContinuumRow.NormalizedSelection.exists_finite_prescribed_measured_frozen_gap
  before b retaining
    (∀ i, angularWidth (ηb i) (r' i) ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) := by
  classical
  have selectedResult := JanetCartan.PhysicalSeed.AngularFrozenUnits.exists_frozen_units_with_angular_cap hD hn H hUH hbounded T I Ω hΩ
    zCell ρc Rc M τlead row col hKΩ hpatchStrong hM hτeq hΩscale
    hRc hτ hτR hbuffer hphysical c₀ htrans R V hR hRphysical hRU hV hVP hflow
    L Mforward hL hMforward hforward hRtime hlabel hcover hcap aExtra
  choose cell hcell centers εcover hεcover hcover' hdomain hgram
    t r a r' a' ht hr ha hr' ha' hlocal hηb htnorm hdir hExtraCap
    hgeometry hmask hAngularExtraCap b hb hbcell hbH hbhalf hba hsampling
    δ hδ Dc p₀ q₀ ρ τ W Bi It A ε gap Qc Ωi βphase cJphase Vphase Lphase Gphase hconic
    χinitial rMeasure hrMeasure hMeasureCell hrb hrH hrhalf hra
    χcoeff hχcoeff hχrange hχcompact hχsupport hχplateau
    σ₀ hσ₀ hσ₀1 coeff Cimage Cbound Lbound hCimage hCbound hLbound
    hcoeff hzero hformula hjets hmeasured hcorrected
    Cnorm Cpdo hCnorm hCpdo Bhigh hBhigh densityCap hdensityCap hcapMeasured hcap8
    current hcurrent hcarriers hunit hnormal using selectedResult
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let family := fun i : ι ↦ T i.1.1.1.1 i.2
  let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let ηb := fun i : ι ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint
    (t i • i.1.1.1.2)
  let selected := fun i : ι ↦ cell i.1.1 i.2
  let seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
  let rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
  let coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
  have hP (i : ι) := (hD.2.2.2.2.1 i.1.1.1.1 i.2).1
  choose _δcov hδcov hcovector using fun i : ι ↦
    exists_uniform_seed_carrierGradient_zero (family i) (hP i)
  obtain ⟨e, he, hei⟩ := Pi.exists_forall_pos_add_lt hδcov
  obtain ⟨stressCap, hstressCap, _, hadmit⟩ := SourceMatching.exists_joint_stress_scale_interval H hbounded he
  let anchor := min densityCap stressCap / 2
  have hanchor : anchor ∈ Ioc (0 : ℝ) densityCap :=
    ⟨half_pos (lt_min hdensityCap hstressCap),
      (half_le_self (le_min hdensityCap.le hstressCap.le)).trans (min_le_left _ _)⟩
  have hanchorStress : anchor ≤ stressCap :=
    (half_le_self (le_min hdensityCap.le hstressCap.le)).trans (min_le_right _ _)
  have hanchor1 : anchor ≤ 1 := hanchor.2.trans (hcap8.trans (by norm_num))
  obtain ⟨hiA, hrankA, hframe, hsmall⟩ := hadmit anchor hanchor.1 hanchorStress
  let QA := projectedStress (sourceDilation H.map anchor)
  have hQA : ContDiffOn ℝ ∞ QA U := fun x hx ↦ (hframe x (subset_closure hx)).contDiffWithinAt
  have hlow (i : ι) : cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
      (QA - fun _ ↦ cubeStress n) < (family i).family.threshold := by
    simpa only [(current anchor hanchor i).frame_eq] using (current anchor hanchor i).Q.2.2
  let Qanchor := fun i : ι ↦ (⟨QA, hQA, hlow i⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (family i).family.threshold})
  have hQanchor (i : ι) : Qanchor i = (current anchor hanchor i).Q :=
    Subtype.ext (current anchor hanchor i).frame_eq.symm
  have hQAzero : QA 0 = cubeStress n := NormalizedFrozenGap.projectedStress_sourceDilation_origin H hanchor.1
  have hproject : QA 0 = projectedStress H.map 0 :=
    hQAzero.trans (funext (projectedStress_flatReference_zero H)).symm
  have hcov (i : ι) (w : Euclidean 3) (hw : w ∈ parameterCube (D.patches i.1.1.1.1 i.2).radius) :
      (family i).carrierGradient (Qanchor i) 0 w = (D.patches i.1.1.1.1 i.2).toFun w := by
    apply hcovector i (Qanchor i) _ hQAzero w hw
    have hsmallCell : cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
        (QA - fun _ ↦ cubeStress n) < e :=
      (cNorm_mono_set_of_contDiffAt ((hphysical i.1.1.1.1 i.2).trans subset_closure)
        hbounded.isCompact_closure (fun x hx ↦ ((hframe x hx).sub contDiffAt_const).of_le (by simp))).trans_lt hsmall
    exact hsmallCell.trans (by simpa only [zero_add] using hei i)
  have hconicProjection := fun i ↦ (hconic i).2.2.2.2
  choose _hρ _hτi _hW _hKiW _hBi _hWBi _hBiDom _hDc _hfoot _hsupport _hIt _hIIt
    _hsegT _hseg _hend _hε _hfreq _hgap _hQc _hΩi _hQcΩi _hQradius _hne _hscale hselectedJoint using hconicProjection
  have hselected := fun i F hF hi hrank hlow hsmall ↦
    (hselectedJoint i F hF hi hrank hlow hsmall).2
  have hkernel (i : ι) : RetainedSpectralGeometry (family i) (Qanchor i) (z i) (ηb i) (r i) (a i) := by
    obtain ⟨_, _, _, _, _, _, hsmallCell, _⟩ := hcurrent anchor hanchor i
    have hsmallQA : cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
        (QA - fun _ ↦ cubeStress n) < δ := by
      simpa only [(current anchor hanchor i).frame_eq] using hsmallCell
    exact (hselected i (sourceDilation H.map anchor) (contDiff_sourceDilation H.contDiff).contDiffOn
      hiA hrankA (hlow i) hsmallQA).1.1
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUH hx)
  have hcol (j : centers) (q : Euclidean n) (hq : q ∈ ball j.1.1.2 (εcover j))
      (l : Fin (D.patchCount j.1.1.1)) :
      carrierNullvector (family ⟨j, l⟩) (Qanchor ⟨j, l⟩) (coli ⟨j, l⟩)
        (0, D.roots j.1.1.1 l q) ≠ 0 := by
    let i : ι := ⟨j, l⟩
    let w := D.roots j.1.1.1 l q
    have hw : w ∈ parameterCube (D.patches j.1.1.1 l).radius :=
      fun m ↦ (((hD.2.2.2.2.1 j.1.1.1 l).2.2.1 q (hdomain j hq)).1 m).le
    have hDc := (seed i).small_subset
      ((outputCylinder_spec (hRc i.1.1.1.1 i.2 (selected i))
        (hτ i.1.1.1.1 i.2 (selected i))).2
          (hflow i.1.1.1.1 i.2 (selected i) (hmask j q hq l).1))
    have hcoef := (seed i).domain_coefficients hDc
    change (coordinates (adaptedCoordinates (family i).data.adapted)).symm
      (coordinates (adaptedCoordinates (family i).data.adapted) (0, parameter (w 0, spectatorCenter w))) ∈ Ω i.1.1.1.1 i.2 (selected i) at hcoef
    simp only [ContinuousLinearEquiv.symm_apply_apply, parameter_apply, carrierParameters_spectatorCenter] at hcoef
    have he := SourceMatching.current_carrierNullvector_source_dilation (family i) (seed i).Q (Qanchor i)
      H.contDiff hrank (hphysical i.1.1.1.1 i.2) (seed i).frame_eq
      (htrans i.1.1.1.1 i.2 (selected i)) hanchor.1 hanchor1 rfl (coli i)
      (mem_ball_self (family i).physicalRadius_pos)
      (fun k ↦ (hw k).trans (by linarith only [(hP i).1]))
    simp only [smul_zero] at he
    rw [he]
    exact ((seed i).null_spec _ hcoef).1
  have hnull (j : centers) (q : Euclidean n) (hq : q ∈ ball j.1.1.2 (εcover j))
      (l : Fin (D.patchCount j.1.1.1)) :
      pencil (projectedStress H.map 0) ((family ⟨j, l⟩).carrierGradient (Qanchor ⟨j, l⟩) 0 (D.roots j.1.1.1 l q)) *ᵥ
        (fun k ↦ carrierNullvector (family ⟨j, l⟩) (Qanchor ⟨j, l⟩) (coli ⟨j, l⟩)
          (0, D.roots j.1.1.1 l q) k) = 0 := by
    rw [← hproject]
    exact NormalizedFrozenGap.seed_carrierNullvector_null_of_patch (family ⟨j, l⟩) (Qanchor ⟨j, l⟩)
      (hP ⟨j, l⟩) hQAzero (coli ⟨j, l⟩)
      (fun k ↦ (((hD.2.2.2.2.1 j.1.1.1 l).2.2.1 q (hdomain j hq)).1 k).le)
      (hcov ⟨j, l⟩ _ (fun k ↦ (((hD.2.2.2.2.1 j.1.1.1 l).2.2.1 q (hdomain j hq)).1 k).le))
  have hi : IsImmersionOn H.map (H.domain.chart n) := isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1)
    (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ H.inducedMetric_eq_one x)
  have h0 : (0 : Euclidean n) ∈ H.domain.chart n :=
    mem_ball_self (H.domain.coreRadius_pos.trans H.domain.coreRadius_lt_chartRadius)
  obtain ⟨γ, hγ, Vunit, htest, hadj, hgapUnit⟩ := exists_retained_frozen_row_gap hD T centers QA hQA hlow H.map
    rowi coli (fun i ↦ (seed i).forward) (fun i ↦ (seed i).inverse)
    ηb r a r' a' hηb hr ha hr' ha' (fun i ↦ (hgeometry i).2.2.1) (fun i ↦ (hgeometry i).2.2.2.1)
    hn εcover hcover' hdomain hgram (fun i ↦ (hgeometry i).2.2.2.2.1) hQAzero hproject
    (H.contDiff.contDiffAt.of_le (by simp)) (hi 0 h0) (H.fullNormalRank 0 h0)
    (fun j q hq l ↦ hcov ⟨j,l⟩ _ (fun k ↦ (((hD.2.2.2.2.1 j.1.1.1 l).2.2.1 q (hdomain j hq)).1 k).le))
    (fun j q hq l ↦ (hmask j q hq l).2) hnull hcol hkernel hlocal
    (fun i ↦ by
      have hh := hunit anchor hanchor i
      rw [← hQanchor i] at hh
      exact hh)
  have heq (i : ι) := normalized_zero_kernel_and_integrals_eq_of_source_frame
    (family i) (seed i).Q (Qanchor i) H.contDiff hrank (hphysical i.1.1.1.1 i.2)
    (seed i).frame_eq (htrans i.1.1.1.1 i.2 (selected i)) hanchor.1 hanchor1 rfl
    (rowi i) (coli i) (seed i).forward (seed i).inverse (fun _ ↦ 1) (ha' i) (hlocal i)
    (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
    FixedCutoffs.highFrequency (fun w θ hw k ↦ by
      have hm := angularMask_nonzero (z i) (NormedSpace.normalize (ηb i)) (ha' i)
        (angularWidth_spec (hηb i) (hr' i)).1 hw
      have hp := (hsampling i).2.1 ⟨ball_subset_closedBall hm.1, ball_subset_closedBall hm.2.1⟩
      exact (hp k).trans (by linarith only [(hP i).1]))
  have hseedGap : InitializedFrozenSeedGap family (fun i ↦ (seed i).Q) H.map rowi coli
      (fun i ↦ (seed i).forward) (fun i ↦ (seed i).inverse) z ηb r' a' hr' ha' hlocal hηb
      (fun i ↦ zCell i.1.1.1.1 i.2 (selected i)) (fun i ↦ L i.1.1.1.1 i.2 (selected i)) := by
    refine ⟨γ, hγ, Vunit, ?_, ?_, ?_⟩
    · intro i f
      rw [← (heq i).2.1]
      exact htest i f
    · intro i w
      rw [← (heq i).2.2]
      exact hadj i w
    · intro μ hμ hμcell hμa Wunit _frozenImage
      obtain ⟨rInner, hrInner, hInnerCell, hrμ, hlocalGap, hglobalPos, hglobal, hext⟩ :=
        hgapUnit μ hμ hμcell hμa
      rw [hproject] at hlocalGap hglobalPos hglobal
      refine ⟨rInner, hrInner, hInnerCell, hrμ, hlocalGap, hglobalPos, hglobal, hext, ?_⟩
      intro v hv hden
      have hweights (i : ι) := exists_sqrt_labelWeight_on_original_density_product (family i) (seed i)
        (hRc i.1.1.1.1 i.2 (selected i)) (hτ i.1.1.1.1 i.2 (selected i))
        (hL i.1.1.1.1 i.2 (selected i)) (ha' i) (hgeometry i).2.2.2.1 (hkernel i).1
        (hgeometry i).2.1 (hflow i.1.1.1.1 i.2 (selected i))
        (hlabel i.1.1.1.1 i.2 (selected i)) (v i) (hv i) (hden i)
      choose β hβ _hcompact _hnonneg hβbound hβeq hlabelExact hlower using hweights
      let Mβ := fun i ↦ FrozenModel.InitialMultiplier.labelMultiplier (n := n) (β i) (hβ i).continuous (hβbound i)
      let Vinitial := fun i ↦ Vunit i ∘L Mβ i
      have hang (i : ι) : ∀ w ∉ carrierSupport (z i) (r := a' i), ∀ θ,
          angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
            (angularWidth_spec (hηb i) (hr' i)).1 w θ = 0 :=
        fun w hw θ ↦ angularMask_zero_outside (z i) (NormedSpace.normalize (ηb i))
          (ha' i) (angularWidth_spec (hηb i) (hr' i)).1 hw θ
      have hunitTest i f := (heq i).2.1 ▸ htest i f
      have hunitAdj i w := (heq i).2.2 ▸ (hadj i w).2
      have hcompare i := FrozenModel.InitialMultiplier.labelMultiplier_real_adjoint_comparison
        (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
        (fun q ↦ Real.sqrt (1 + v i q)) (ha' i) (hlocal i) _ FixedCutoffs.highFrequency
        (hang i) (β i) (hβ i).continuous (hβbound i) (hβeq i) (hlower i) (Vunit i) (hunitAdj i)
      have hchannels i (w : OutputL2 n) :
          (1 / 16 : ℝ) * ‖(realQuadratureChannel (Wunit i)).adjoint w‖ ^ 2 ≤
          ‖(realQuadratureChannel (restrictCarrier (FixedCutoffs.periodic hμ hμcell 1) (Vinitial i))).adjoint w‖ ^ 2 := by
        change (1 / 16 : ℝ) * ‖(carrierChannel _).adjoint w‖ ^ 2 ≤ ‖(carrierChannel _).adjoint w‖ ^ 2
        simp only [Wunit, carrierChannel_restrictCarrier, ContinuousLinearMap.adjoint_comp,
          cutoffMultiplier_adjoint, ContinuousLinearMap.comp_apply]
        exact hcompare i (cutoffMultiplier (FixedCutoffs.periodic hμ hμcell 1) w)
      refine ⟨β, hβ, hβbound, ?_,
        (FrozenModel.InitialMultiplier.supported_physicalRow_gap_of_initial_comparison _ _ _ hchannels
          (half_pos hγ) hlocalGap).2,
        (FrozenModel.InitialMultiplier.augmentedNormal_gap_of_initial_comparison _ _ _ hchannels
          (innerCutoff hrInner hInnerCell) hglobalPos hglobal).2⟩
      intro i
      refine ⟨hβeq i, hlabelExact i,
        FrozenModel.InitialMultiplier.labelMultiplier_norm_le (β i) (hβ i).continuous (by norm_num) (hβbound i),
        FrozenModel.InitialMultiplier.labelMultiplier_adjoint (β i) (hβ i).continuous (hβbound i), ?_, ?_,
        FrozenModel.InitialMultiplier.labelMultiplier_complex_normal (β i) (hβ i).continuous (hβbound i) (Vunit i),
        FrozenModel.InitialMultiplier.labelMultiplier_real_normal (β i) (hβ i).continuous (hβbound i) (Vunit i)⟩
      · exact FrozenModel.InitialMultiplier.labelMultiplier_test_action
          (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
          (fun q ↦ Real.sqrt (1 + v i q)) (ha' i) (hlocal i) _ FixedCutoffs.highFrequency
          (hang i) (β i) (hβ i) (hβbound i) (hβeq i) (Vunit i) (hunitTest i)
      · intro w
        exact ⟨FrozenModel.InitialMultiplier.labelMultiplier_adjoint_memLp
            (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
            (fun q ↦ Real.sqrt (1 + v i q)) (ha' i) (hlocal i) _ FixedCutoffs.highFrequency
            (hang i) (β i) (hβ i).continuous (hβbound i) (hβeq i) (Vunit i) (hunitAdj i) w,
          FrozenModel.InitialMultiplier.labelMultiplier_adjoint_action
            (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
            (fun q ↦ Real.sqrt (1 + v i q)) (ha' i) (hlocal i) _ FixedCutoffs.highFrequency
            (hang i) (β i) (hβ i).continuous (hβbound i) (hβeq i) (Vunit i) (hunitAdj i) w⟩
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, hAngularExtraCap, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, Dc, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi, βphase, cJphase, Vphase, Lphase, Gphase, hconic,
    χinitial, rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    σ₀, hσ₀, hσ₀1, coeff, Cimage, Cbound, Lbound, hCimage, hCbound, hLbound,
    hcoeff, hzero, hformula, hjets, hmeasured, hcorrected,
    Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh, densityCap, hdensityCap,
    hcapMeasured, hcap8, current, hcurrent, hcarriers, hunit,
    hseedGap, hnormal⟩

end JanetCartan.PhysicalSeed.AngularFrozenGap
