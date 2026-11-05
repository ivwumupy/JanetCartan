module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RawCappedInitialization.MeasuredSelection
public import JanetCartan.Iteration.PhysicalSeed.AngularSelection
public meta import JanetCartan.Iteration.PhysicalSeed.AngularTemplates

/-!
# Retain both caps through the same original Measured construction

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
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSeed.AngularMeasured
open ContinuumRow ContinuumRow.NormalizedSelection
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol FullPhaseCharts ActualPhase ActualComparison
open CarrierVariation.FamilyInputs PositiveReference ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude CarrierSobolev GeometricProfile
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.PhaseExtension CommonMeasurement


declare_angular_retained exists_measured_row_with_angular_cap
  from JanetCartan.ContinuumRow.NormalizedSelection.exists_finite_measured_incidence_row_with_corrected_rawAdjoints
  before b retaining
    (∀ i, angularWidth (ηb i) (r' i) ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) := by
  classical
  obtain ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, hAngularExtraCap, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, hconic, huncorrected, sCorrected, hsCorrected, _hsCorrected1, hcorrected⟩ :=
    JanetCartan.PhysicalSeed.AngularSelection.exists_corrected_row_with_angular_cap hD H hUH hbounded T I Ω hΩ
      zCell ρc Rc M τlead row col hKΩ hpatchStrong hM hτeq hΩscale hRc hτ hτR hbuffer hphysical
      c₀ htrans R V hR hRphysical hRU hV hVP hflow L Mforward hL hMforward hforward hRtime hlabel
      hcover hcap aExtra
  obtain ⟨χinitial, Craw, Lraw, hCraw, _hLraw, sRaw, hsRaw, _hsRaw1, hraw⟩ := huncorrected
  choose χcorrected _hchartCorrected CrawCorrected _LrawCorrected hCrawCorrected _hLrawCorrected hrawCorrected
    using hcorrected
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let family := fun i : ι ↦ T i.1.1.1.1 i.2
  let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let ηb := fun i : ι ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint
    (t i • i.1.1.1.2)
  let selected := fun i : ι ↦ cell i.1.1 i.2
  let seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
  let rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
  let coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
  let width := fun i : ι ↦ angularWidth (ηb i) (r' i)
  have hwidth (i : ι) : 0 < width i := (angularWidth_spec (hηb i) (hr' i)).1
  obtain ⟨rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    sImage, hsImage, hsImage1, coeff, Cimage, hCimage, hcoeff, hzero, hformula,
    hjets, hmeasured⟩ := exists_common_measured_normalized_data H family
      (fun i ↦ Ω i.1.1.1.1 i.2 (selected i))
      (fun i ↦ closedBall ((0 : Euclidean n), zCell i.1.1.1.1 i.2 (selected i))
        (ρc i.1.1.1.1 i.2 (selected i)))
      (fun i ↦ ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i)))
      (fun i ↦ Rc i.1.1.1.1 i.2 (selected i)) (fun i ↦ M i.1.1.1.1 i.2 (selected i))
      (fun i ↦ τlead i.1.1.1.1 i.2 (selected i)) rowi coli seed (fun _ _ ↦ 1)
      a' ha' hlocal z (fun i ↦ NormedSpace.normalize (ηb i)) width hwidth hb
      (H.domain.coreRadius_pos.trans H.domain.coreRadius_lt_chartRadius)
  let χ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 1
  let χsrc := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 2
  let ψ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 0
  obtain ⟨Cbound, Lbound, hCbound, hLbound, hrow⟩ := exists_uniform_measured_row_bounds
    H χ χsrc ψ (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 1)
    (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 2)
    (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 0)
    Cimage (fun m ↦ (hCimage m).le) Craw hCraw z
    (fun i ↦ NormedSpace.normalize (ηb i)) ha' hwidth χinitial
  let Kin := fun i : ι ↦ closedBall
    ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i))
    (L i.1.1.1.1 i.2 (selected i) / 8)
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, hAngularExtraCap, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, hconic, χinitial, rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    min sRaw (min sImage sCorrected), lt_min hsRaw (lt_min hsImage hsCorrected),
    ((min_le_right _ _).trans (min_le_left _ _)).trans hsImage1,
    coeff, Cimage, Cbound, Lbound, hCimage, hCbound, hLbound, hcoeff, hzero,
    (fun σ hσ ↦ hformula σ ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩),
    (fun m σ hσ ↦ hjets m σ ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩), ?_⟩
  intro χ χsrc ψ selected seed rowi coli angular
  refine ⟨?_, ?_⟩
  · intro σ hσ d e
    have hσRaw : σ ∈ Ioc (0 : ℝ) sRaw := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
    have hσImage : σ ∈ Ioc (0 : ℝ) sImage := ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    choose hplateau _hkernel Vop hrep _hunique hlocalRaw _hrealMem _hrealBound _hdensity using
      fun i ↦ (hraw i).2 σ hσRaw
    obtain ⟨hnorm, htest, hadj, hnormal⟩ := hmeasured.2 σ Vop
    have hArep (i : ι) (w : ComplexOutputL2 n) :
        (restrictCarrier χ (Vop i)).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w :=
      (hadj i (fun v ↦ ⟨(memLp_congr_ae (hrep i v)).mp (Lp.memLp ((Vop i).adjoint v)), hrep i v⟩) w).2
    have hUunique (i : ι) (B : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (hB : ∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) :
        B = restrictCarrier χ (Vop i) := by
      have he := DerivativeKernels.literalCarrierAdjointOperator_unique (e i)
        B.adjoint (restrictCarrier χ (Vop i)).adjoint hB (hArep i)
      simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg ContinuousLinearMap.adjoint he
    refine ⟨?_, Vop, hrep, hnorm, hArep, hUunique, htest, hnormal, ?_⟩
    · intro i p hp
      apply hplateau i
      exact NormalizedMeasurement.source_product_subset_original_supportedChart (z i) hrMeasure (hra i) hp
    · intro selectedCoeff hselected B hB
      have hcoeffEq : selectedCoeff = coeff σ := by
        funext j
        apply ContinuousMap.ext
        intro x
        exact (hselected j x).trans (hformula σ hσImage j x).symm
      have hBEq : B = fun i ↦ restrictCarrier χ (Vop i) := funext fun i ↦ hUunique i (B i) (hB i)
      subst selectedCoeff B
      exact hrow (coeff σ) (hcoeff σ) (fun m j x ↦ (hjets m σ hσImage j x).2)
        d Vop hrep hlocalRaw
  · intro ψcorrected hψcorrected
    obtain ⟨Ccorrected, Lcorrected, hCcorrected, hLcorrected, hrowCorrected⟩ :=
      exists_uniform_measured_density_row_bounds H χ χsrc ψcorrected
        (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 1)
        (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 2) hψcorrected
        Cimage (fun m ↦ (hCimage m).le) CrawCorrected hCrawCorrected Kin z
        (fun i ↦ NormedSpace.normalize (ηb i)) ha' hwidth χinitial
    refine ⟨Ccorrected, Lcorrected, hCcorrected, hLcorrected, ?_⟩
    intro σ hσ vDensity hvDensity hinterval hlow Hhigh d e
    have hσCorrected : σ ∈ Ioc (0 : ℝ) sCorrected :=
      ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    have hσImage : σ ∈ Ioc (0 : ℝ) sImage :=
      ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    choose _hplateau Vop hrep _hunique hlocalRaw _hrealMem _hrealBound _hdensity using
      fun i ↦ hrawCorrected i σ hσCorrected (vDensity i) (hvDensity i) (hinterval i) (hlow i)
    have hArep (i : ι) (w : ComplexOutputL2 n) :
        (restrictCarrier χ (Vop i)).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w := by
      have hs := NormalizedMeasurement.supplied_carrier_common_measurement (d i)
        hrMeasure (ha' i) hMeasureCell (hlocal i) (hra i) rfl (fun _ _ ↦ rfl) rfl
      exact ((hs.2.2.2.2.2.2.2.2 (Vop i)).2.2
        (fun w ↦ ⟨(memLp_congr_ae (hrep i w)).mp (Lp.memLp ((Vop i).adjoint w)), hrep i w⟩) w).2
    have hUunique (i : ι) (B : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (hB : ∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) :
        B = restrictCarrier χ (Vop i) := by
      have he := DerivativeKernels.literalCarrierAdjointOperator_unique (e i)
        B.adjoint (restrictCarrier χ (Vop i)).adjoint hB (hArep i)
      simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg ContinuousLinearMap.adjoint he
    refine ⟨Vop, hrep, hArep, hUunique, ?_⟩
    intro selectedCoeff hselected B hB
    have hcoeffEq : selectedCoeff = coeff σ := by
      funext j
      apply ContinuousMap.ext
      intro x
      exact (hselected j x).trans (hformula σ hσImage j x).symm
    have hBEq : B = fun i ↦ restrictCarrier χ (Vop i) := funext fun i ↦ hUunique i (B i) (hB i)
    subst selectedCoeff B
    exact hrowCorrected (coeff σ) (hcoeff σ) (fun m j x ↦ (hjets m σ hσImage j x).2)
      (fun i ↦ PositiveBackground.densityOnInitialLabels (vDensity i)) d Vop hrep hlocalRaw

end JanetCartan.PhysicalSeed.AngularMeasured
