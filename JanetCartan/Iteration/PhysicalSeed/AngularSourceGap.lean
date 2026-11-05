module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedMeasuredSource.SourceGap
public import JanetCartan.Iteration.PhysicalSeed.AngularZeroGap
public meta import JanetCartan.Iteration.PhysicalSeed.AngularTemplates

/-!
# Retain both caps through the same original SourceGap construction

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
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalSeed.AngularSourceGap
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



declare_angular_retained exists_source_gap_with_angular_cap
  from JanetCartan.ContinuumRow.NormalizedSelection.exists_finite_prescribed_measured_source_gap
  before b retaining
    (∀ i, angularWidth (ηb i) (r' i) ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) := by
  classical
  have selectedResult := JanetCartan.PhysicalSeed.AngularZeroGap.exists_zero_gap_with_angular_cap hD hn H hUH hbounded T I Ω hΩ
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
    current hcurrent hcarriers hunit hseedGap hzeroGap hnormal using selectedResult
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let family := fun i : ι ↦ T i.1.1.1.1 i.2
  let _z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let _ηb := fun i : ι ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint
    (t i • i.1.1.1.2)
  let selected := fun i : ι ↦ cell i.1.1 i.2
  let _seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
  let _rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
  let _coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
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
    hseedGap, ?_⟩
  refine ⟨?_, hnormal⟩
  obtain ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG, hzeroCoercive⟩ := hzeroGap
  let G := NormalAugmentation.globalGap g Mlimit
  let κ := min g G
  have hκ : 0 < κ := lt_min hg hG
  obtain ⟨_Ccompare, _Bsource, _Mzero, _hCcompare, _hBsource, _hMzero, hcompare⟩ := hnormal
  obtain ⟨capCarrier, hcapCarrier, hcapCarrierSource, _hcapCarrierOne, hcompare⟩ := hcompare κ hκ
  obtain ⟨_Bimage, _hBimage, himageTolerance⟩ :=
    ActualConstruction.exists_supplied_measurement_imageNormal_threshold
      H hrMeasure hMeasureCell hrhalf χcoeff hχcoeff hχsupport hχplateau (coeff 0) hzero
  obtain ⟨capImage, hcapImage, hcapImageOne, himageError⟩ :=
    himageTolerance (κ / 4) (by positivity)
  let cap := min capCarrier capImage
  have hcap : 0 < cap := lt_min hcapCarrier hcapImage
  have hcapSource : cap ≤ densityCap := (min_le_left _ _).trans hcapCarrierSource
  have hcapMeasured' : cap ≤ σ₀ := hcapSource.trans hcapMeasured
  let χ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 1
  let χsrc := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 2
  let image₀ := FrozenImageComparison.fixedPeriodicChannel hrMeasure hMeasureCell
    (FrozenCoercivity.frozenImageArrays (projectedStress H.map 0))
  refine ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG,
    cap, hcap, hcapSource, hcapMeasured', (min_le_right _ _).trans hcapImageOne, ?_⟩
  intro v hv hpos hinterval hvnorm
  obtain ⟨Vzero, hzeroActions, hzeroBound, hzeroLocal, hzeroGlobal, hzeroAdjoint, hexterior⟩ :=
    hzeroCoercive v hv hpos hinterval hvnorm
  refine ⟨Vzero, hzeroActions, hzeroBound, hzeroLocal, hzeroGlobal, hzeroAdjoint, hexterior, ?_⟩
  intro σ hσ
  have hσCarrier : σ ∈ Ioc (0 : ℝ) capCarrier := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hσImage : σ ∈ Ioc (0 : ℝ) capImage := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hσMeasured : σ ∈ Ioc (0 : ℝ) σ₀ := ⟨hσ.1, hσ.2.trans hcapMeasured'⟩
  obtain ⟨_hsmall, _hb, _hs, _hB, Vop, huniq, _hVbound, hreal, _hsum, _hmeas,
      Vcmp, _hVcmp, hcmpActions, _hsumCmp, hmeasCmp⟩ :=
    hcompare σ hσCarrier v hv hpos hinterval hvnorm
  have hVcmp : Vcmp = Vzero := funext fun i ↦
    (hzeroActions i).2.2 (Vcmp i) (hcmpActions i).1
  have hcarrier := hmeasCmp χ (FixedCutoffs.periodic_norm_le_one hrMeasure hMeasureCell 1)
  rw [hVcmp] at hcarrier
  let imageCurrent := imageChannel (coeff σ) χ χsrc
  let Wcurrent := fun i ↦ restrictCarrier χ (Vop i)
  let Wzero := fun i ↦ restrictCarrier χ (Vzero i)
  have himage : ‖NormalPerturbation.normal imageCurrent - NormalPerturbation.normal image₀‖ ≤ κ / 4 := by
    have heq : projectedStress H.map 0 = cubeStress n :=
      funext (projectedStress_flatReference_zero H)
    dsimp only [image₀]
    rw [heq]
    exact (himageError σ hσImage (coeff σ) (hformula σ hσMeasured)).2.2.le
  let Acurrent := physicalRow imageCurrent Wcurrent
  let Azero := physicalRow image₀ Wzero
  have hcomparison : ‖NormalPerturbation.normal Acurrent - NormalPerturbation.normal Azero‖ ≤ κ / 2 := by
    dsimp only [Acurrent, Azero, NormalPerturbation.normal]
    rw [physicalRow_normal, physicalRow_normal, add_sub_add_comm, ← Finset.sum_sub_distrib]
    exact ((norm_add_le _ _).trans (add_le_add himage hcarrier)).trans (by linarith)
  have hcurrentBound : ‖Acurrent‖ ≤ Real.sqrt (Mlimit ^ 2 + κ / 2) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    have hnorm := norm_le_norm_add_norm_sub
      (NormalPerturbation.normal Azero) (NormalPerturbation.normal Acurrent)
    rw [NormalPerturbation.norm_normal, NormalPerturbation.norm_normal] at hnorm
    rw [norm_sub_rev (NormalPerturbation.normal Azero) (NormalPerturbation.normal Acurrent)] at hnorm
    have hsq : ‖Azero‖ ^ 2 ≤ Mlimit ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzeroBound 2
    linarith only [hnorm, hcomparison, hsq]
  have hlocal (w : OutputL2 n)
      (hw : ∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) :
      g / 2 * ‖w‖ ^ 2 ≤ ‖Acurrent.adjoint w‖ ^ 2 := by
    have hgapNormal : ∀ f ∈ {f : OutputL2 n | ∀ᵐ x ∂volume,
        x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → f x = 0},
        g * ‖f‖ ^ 2 ≤ RCLike.re (inner ℝ (NormalPerturbation.normal Azero f) f) := by
      intro f hf
      apply (hzeroLocal f hf).trans_eq
      simpa only [ContinuousLinearMap.adjoint_adjoint, NormalPerturbation.normal] using
        Azero.adjoint.apply_norm_sq_eq_inner_adjoint_left f
    have h := NormalPerturbation.quadratic_lower_bound_of_norm_sub_le
      (NormalPerturbation.normal Azero) (NormalPerturbation.normal Acurrent)
      {f | ∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → f x = 0}
      (g := g) (ε := g / 2) hgapNormal
      (hcomparison.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))) w hw
    have heq := Acurrent.adjoint.apply_norm_sq_eq_inner_adjoint_left w
    simp only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real,
      ContinuousLinearMap.comp_apply] at heq
    change (g - g / 2) * ‖w‖ ^ 2 ≤ inner ℝ (Acurrent (Acurrent.adjoint w)) w at h
    rw [← heq] at h
    convert h using 1
    ring
  have haugmented : ‖augmentedNormal imageCurrent Wcurrent (innerCutoff hrInner hInnerCell) -
      augmentedNormal image₀ Wzero (innerCutoff hrInner hInnerCell)‖ ≤ κ / 2 := by
    have heq : augmentedNormal imageCurrent Wcurrent (innerCutoff hrInner hInnerCell) -
        augmentedNormal image₀ Wzero (innerCutoff hrInner hInnerCell) =
        NormalPerturbation.normal Acurrent - NormalPerturbation.normal Azero := by
      rw [augmentedNormal_eq_sum, augmentedNormal_eq_sum]
      simp only [NormalPerturbation.normal, Acurrent, Azero, physicalRow_normal]
      abel
    rw [heq]
    exact hcomparison
  have hcurrentGlobal (w : OutputL2 n) : G / 2 * ‖w‖ ^ 2 ≤
      inner ℝ (augmentedNormal imageCurrent Wcurrent (innerCutoff hrInner hInnerCell) w) w :=
    augmented_half_gap_of_normal_comparison imageCurrent image₀ Wcurrent Wzero
      (innerCutoff hrInner hInnerCell) univ (fun f _ ↦ hzeroGlobal f) haugmented
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) w (mem_univ w)
  refine ⟨Vop, huniq, fun i ↦ ⟨(hreal i).1, (hreal i).2.1⟩,
    hcurrentBound, hlocal, hcurrentGlobal, ?_⟩
  intro w
  have heq := (augmentedRow imageCurrent Wcurrent
    (innerCutoff hrInner hInnerCell)).adjoint.apply_norm_sq_eq_inner_adjoint_left w
  apply (hcurrentGlobal w).trans_eq
  simpa only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real, augmentedNormal] using heq.symm

end JanetCartan.PhysicalSeed.AngularSourceGap
