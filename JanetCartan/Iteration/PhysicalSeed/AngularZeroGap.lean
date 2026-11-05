module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedMeasuredSource.ZeroGap
public import JanetCartan.Iteration.PhysicalSeed.AngularFrozenGap
public meta import JanetCartan.Iteration.PhysicalSeed.AngularTemplates

/-!
# Retain both caps through the same original ZeroGap construction

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
namespace JanetCartan.PhysicalSeed.AngularZeroGap
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



declare_angular_retained exists_zero_gap_with_angular_cap
  from JanetCartan.ContinuumRow.NormalizedSelection.exists_finite_prescribed_measured_zero_gap
  before b retaining
    (∀ i, angularWidth (ηb i) (r' i) ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) := by
  classical
  have selectedResult := JanetCartan.PhysicalSeed.AngularFrozenGap.exists_frozen_gap_with_angular_cap hD hn H hUH hbounded T I Ω hΩ
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
    current hcurrent hcarriers hunit hseedGap hnormal using selectedResult
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
  have hconicProjection := fun i ↦ (hconic i).2.2.2.2
  choose hρ hτi hW hKiW hBi hWBi hBiDom hDc hfoot hsupport hIt hIIt
    hsegT hseg _hend hε hfreq hgap _hQc _hΩi _hQcΩi _hQradius _hne _hscale hselectedJoint using hconicProjection
  have hselected := fun i F hF hi hrank hlow hsmall ↦
    (hselectedJoint i F hF hi hrank hlow hsmall).2
  let anchor := densityCap / 2
  have hanchor : anchor ∈ Ioc (0 : ℝ) densityCap :=
    ⟨half_pos hdensityCap, half_le_self hdensityCap.le⟩
  have hanchor1 : anchor ≤ 1 := hanchor.2.trans (hcap8.trans (by norm_num))
  let ca := current anchor hanchor
  choose _sourceFlow _hsourceFlow _hsourceForward _hsourceInverse hiSource hrankSource hsmallSource
    _hsourceMatching using fun i : ι ↦ hcurrent anchor hanchor i
  have hF : ContDiffOn ℝ ∞ (sourceDilation H.map anchor) U :=
    (contDiff_sourceDilation H.contDiff).contDiffOn
  have hlow (i : ι) : cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
      (projectedStress (sourceDilation H.map anchor) - fun _ ↦ cubeStress n) < (family i).family.threshold := by
    simpa only [(current anchor hanchor i).frame_eq] using (current anchor hanchor i).Q.2.2
  have hs (i : ι) : cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
      (projectedStress (sourceDilation H.map anchor) - fun _ ↦ cubeStress n) < δ := by
    simpa only [(current anchor hanchor i).frame_eq] using hsmallSource i
  have hgeom := fun i : ι ↦ hselected i (sourceDilation H.map anchor) hF
    (hiSource i) (hrankSource i) (hlow i) (hs i)
  have hQ (i : ι) : (⟨projectedStress (sourceDilation H.map anchor),
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF (hiSource i) (hrankSource i)), hlow i⟩ :
      {QF : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ QF U ∧
        cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
          (QF - fun _ ↦ cubeStress n) < (family i).family.threshold}) = (ca i).Q :=
    Subtype.ext (ca i).frame_eq.symm
  have hi : IsImmersionOn H.map U := isImmersionOn_of_isIsometricOn
    (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ H.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUH hx)
  have hzeroCell (i : ι) := by
    have hg := hgeom i
    dsimp only at hg
    rw [hQ i] at hg
    obtain ⟨hbase, _hcur, hfrozen⟩ := hg
    obtain ⟨hspectral, hout, hrange, _hhalfCurrent, _hJcurrent, _hbufferCurrent, hshell, _hupper⟩ := hbase
    obtain ⟨hc, _hs, _hrange, _hnormalized, _heq, hhalf, hJ, _hJs, _hJeq, _hinj,
      _hscale, _hmask, hpunct⟩ := hfrozen
    exact NormalizedNormalLimit.exists_retained_seed_zero_density_realization_of_source
      (hP i) (family i) (hΩ i.1.1.1.1 i.2 (selected i)) (hKΩ i.1.1.1.1 i.2 (selected i))
      (hpatchStrong i.1.1.1.1 i.2 (selected i)) (hRc i.1.1.1.1 i.2 (selected i))
      (hτ i.1.1.1.1 i.2 (selected i)) (hτR i.1.1.1.1 i.2 (selected i))
      (hbuffer i.1.1.1.1 i.2 (selected i)) H.contDiff hi hrank (hphysical i.1.1.1.1 i.2)
      (seed i) (htrans i.1.1.1.1 i.2 (selected i)) (fun x _ ↦ H.inducedMetric_eq_one x)
      (hL i.1.1.1.1 i.2 (selected i)) (hMforward i.1.1.1.1 i.2 (selected i))
      (hR i.1.1.1.1 i.2 (selected i)) (hforward i.1.1.1.1 i.2 (selected i))
      (hRphysical i.1.1.1.1 i.2 (selected i)) (hRU i.1.1.1.1 i.2 (selected i))
      (hRtime i.1.1.1.1 i.2 (selected i)) (hV i.1.1.1.1 i.2 (selected i))
      (hVP i.1.1.1.1 i.2 (selected i)) (hflow i.1.1.1.1 i.2 (selected i))
      (hlabel i.1.1.1.1 i.2 (selected i)) (Dc i) ((hDc i).trans inter_subset_left)
      (hηb i) (hr i) (hr' i) (ha' i) (hgeometry i).2.2.1 (hgeometry i).2.2.2.1
      (hgeometry i).2.2.2.2.1 (hlocal i) (hgeometry i).2.1
      (ca i).Q hanchor.1 hanchor1 (ca i).frame_eq hspectral (p₀ i) (q₀ i)
      (hρ i) (hτi i) (hW i) (hKiW i) (hBi i) (hWBi i) (hBiDom i)
      hout hrange hshell (hIt i) (hIIt i) (hsegT i) (hseg i) (A i) (hgap i) (hε i)
      (fun p hp ↦ hfreq i p (hWBi i (hKiW i hp))) (hfoot i)
      hhalf (fun p hp ↦ hJ p (hWBi i (hKiW i hp))) (hsupport i) hc hpunct
  choose _Mzero _hMzero Bzero hBzero hzeroDensity using hzeroCell
  let Bbudget : ι → NNReal := fun i ↦ ⟨Bzero i, (hBzero i).le⟩
  have hfreezing := ActualConstruction.exists_initialized_source_density_limit_coercivity
    (by omega : 0 < n) family (fun i ↦ (seed i).Q) H.map rowi coli
    (fun i ↦ (seed i).forward) (fun i ↦ (seed i).inverse) z ηb r' a'
    hr' ha' hlocal hηb (fun i ↦ zCell i.1.1.1.1 i.2 (selected i))
    (fun i ↦ L i.1.1.1.1 i.2 (selected i)) hseedGap hrMeasure hMeasureCell hra
    (fun i ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (family i))
      (normalizedTransportPosition (family i) (seed i).Q 0))
    (fun i ↦ frozenSymbolInverse (family i) (seed i).Q (z i) (ηb i) (r i) (6*a i))
    Ωi (fun i ↦ closedBall (spectatorCenter (z i)) (a' i / 2)) Bbudget
  obtain ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG, hcoercive⟩ := hfreezing
  have hzeroGap :
      let image := FrozenImageComparison.fixedPeriodicChannel hrMeasure hMeasureCell
          (FrozenCoercivity.frozenImageArrays (projectedStress H.map 0))
      ∃ g > (0 : ℝ), ∃ (rInner : ℝ) (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2),
      ∃ Mlimit ≥ (0 : ℝ), rInner ≤ rMeasure ∧
        0 < NormalAugmentation.globalGap g Mlimit ∧
        ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
        (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i)) (L i.1.1.1.1 i.2 (selected i) / 4))) →
        (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i)) (L i.1.1.1.1 i.2 (selected i) / 4) → 0 < 1 + v i q) →
        (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i)) (L i.1.1.1.1 i.2 (selected i) / 8) →
          1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i)) (L i.1.1.1.1 i.2 (selected i) / 8)) (2 * (n + 1) + 14) (v i) ≤ 1) →
        ∃ Vzero : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ i,
            (∀ f : carrierInitialTestSpace n,
              Vzero i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (SourceDensityLimitRealization.weightNormal
              (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
                (fun _ ↦ 1) (ha' i) (hlocal i)
                (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
                FixedCutoffs.highFrequency 0)
              (fun p ↦ Real.sqrt (1 + v i (sourceDensityFootpointExtension (family i) (seed i).inverse (0, p))))) f.val) ∧
            (∀ f : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (SourceDensityLimitRealization.weightNormal
              (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
                (fun _ ↦ 1) (ha' i) (hlocal i)
                (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
                FixedCutoffs.highFrequency 0)
              (fun p ↦ Real.sqrt (1 + v i (sourceDensityFootpointExtension (family i) (seed i).inverse (0, p))))) f) 2 (carrierMeasure n) ∧
              (Vzero i).adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral (SourceDensityLimitRealization.weightNormal
              (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
                (fun _ ↦ 1) (ha' i) (hlocal i)
                (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
                FixedCutoffs.highFrequency 0)
              (fun p ↦ Real.sqrt (1 + v i (sourceDensityFootpointExtension (family i) (seed i).inverse (0, p))))) f) ∧
            (∀ Wzero : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
              (∀ f : carrierInitialTestSpace n,
                Wzero (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (SourceDensityLimitRealization.weightNormal
              (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
                (fun _ ↦ 1) (ha' i) (hlocal i)
                (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
                FixedCutoffs.highFrequency 0)
              (fun p ↦ Real.sqrt (1 + v i (sourceDensityFootpointExtension (family i) (seed i).inverse (0, p))))) f.val) →
                Wzero = Vzero i)) ∧
          let Wzero := fun i ↦ restrictCarrier (FixedCutoffs.periodic hrMeasure hMeasureCell 1) (Vzero i)
          ‖physicalRow image Wzero‖ ≤ Mlimit ∧
          (∀ w : OutputL2 n,
            (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
            g * ‖w‖ ^ 2 ≤ ‖(physicalRow image Wzero).adjoint w‖ ^ 2) ∧
          (∀ w : OutputL2 n, NormalAugmentation.globalGap g Mlimit * ‖w‖ ^ 2 ≤
            inner ℝ (augmentedNormal image Wzero (innerCutoff hrInner hInnerCell) w) w) ∧
          (∀ w : OutputL2 n, NormalAugmentation.globalGap g Mlimit * ‖w‖ ^ 2 ≤
            ‖(augmentedRow image Wzero (innerCutoff hrInner hInnerCell)).adjoint w‖ ^ 2) ∧
          (∀ w : OutputL2 n, ∀ᵐ x ∂volume,
            centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
              exteriorChannel (innerCutoff hrInner hInnerCell) w x = 0) := by
    refine ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG, ?_⟩
    intro v hv hpos hinterval hvnorm
    choose hb hA _hs Vop hreal using fun i t ↦ hzeroDensity i (v i) (hv i) (hpos i) (hinterval i) (hvnorm i) t
    obtain ⟨Vfrozen, hfrozen, htransfer⟩ := hcoercive v hv hinterval
    let Vactual := fun i ↦ Vop i true
    have hfrozenEq (i : ι) : Vfrozen i = Vop i false :=
      (hreal i false).2.2.2.2.2.1 rfl (Vfrozen i) (hfrozen i).1
    have hconclusion := htransfer hb hA Vactual (fun i t ↦ by
      cases t
      · simp only
        rw [hfrozenEq i]
        exact (hreal i false).2.2.2.2.2.2.1
      · simp only [↓reduceIte]
        exact (hreal i true).2.2.2.2.2.2.1)
    refine ⟨Vactual, ?_, hconclusion⟩
    intro i
    exact ⟨(hreal i true).2.2.1, (hreal i true).2.2.2.1, (hreal i true).2.2.2.2.1⟩
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
  exact ⟨hzeroGap, hnormal⟩

end JanetCartan.PhysicalSeed.AngularZeroGap
