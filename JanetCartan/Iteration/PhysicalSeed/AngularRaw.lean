module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedMeasuredSource.Raw
public import JanetCartan.Iteration.PhysicalSeed.AngularSourceInverse
public meta import JanetCartan.Iteration.PhysicalSeed.AngularTemplates

/-!
# Both caps retained in the same actual prescribed source inverse

All original scalar, raw, cut, uncut, inverse and exterior continuations belong
to this one stronger tuple. The angular certificate is appended at the prefix
tail, preserving every old exposed fact and the 21-argument initializer API.
Consumer: `PhysicalSampling.exists_original_scalar_sampling_bounds`
(`new:sec:order-of-choices`, `app:ch_background:prop:bg-inverse`).
-/

set_option warningAsError true
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalSeed.AngularRaw
open ContinuumInverse
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



declare_angular_retained exists_source_raw_inverse_with_angular_cap
  from JanetCartan.ContinuumInverse.exists_finite_prescribed_measured_source_raw_inverse
  before targetGap retaining
    (∀ i, angularWidth (ηb i) (r' i) ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) := by
  classical
  have selectedResult := JanetCartan.PhysicalSeed.AngularSourceInverse.exists_source_inverse_with_angular_cap hD hn H hUH hbounded T I Ω hΩ
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
    current hcurrent hcarriers hunit hseedGap hsourceGap hnormal using selectedResult
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let family := fun i : ι ↦ T i.1.1.1.1 i.2
  let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let ηb := fun i : ι ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint
    (t i • i.1.1.1.2)
  let selected := fun i : ι ↦ cell i.1.1 i.2
  let seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
  let rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
  let coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, Dc, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi, βphase, cJphase, Vphase, Lphase, Gphase, hconic,
    χinitial, rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    σ₀, hσ₀, hσ₀1, coeff, Cimage, Cbound, Lbound, hCimage, hCbound, hLbound,
    hcoeff, hzero, hformula, hjets, hmeasured, hcorrected,
    Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh, densityCap, hdensityCap,
    hcapMeasured, hcap8, current, hcurrent, hcarriers, hunit,
    hseedGap, ?_⟩
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG,
      sourceCap, hsourceCap, hcapSource, hcapMeasured', hcapOne, Cell, hCell, hsource⟩ := hsourceGap
    let ψ := innerCutoff (n := n) hrInner hInnerCell
    let γsource := NormalAugmentation.globalGap g Mlimit / 2
    have hγsource : 0 < γsource := half_pos hG
    obtain ⟨Kraw, hKraw, hinner⟩ := exists_augmented_raw_bounds_with_supplied_exterior
      (ι := ι) ψ (innerCutoff_smooth hrInner hInnerCell) Cbound hCbound
    obtain ⟨Ltrade, hLtrade, htrade⟩ := exists_densityFamily_gradeNorm_bounds
      z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
      (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) χinitial
    obtain ⟨Kpositive, _Lpositive, hKpositive, _hLpositive, hpositive⟩ :=
      hcorrected ψ (innerCutoff_smooth hrInner hInnerCell)
    let β := bootstrapConstant γsource Cell
    let Cfull := fun s ↦ β s + Kraw s * (β s + γsource⁻¹)
    let Dfull := fun s ↦ Ltrade s * Cfull (s + 1)
    let Cpositive := fun s ↦ β s + Kpositive s * (β s + γsource⁻¹)
    let Dpositive := fun s ↦ Ltrade s * Cpositive (s + 1)
    have hβ (s : ℕ) : 0 ≤ β s := bootstrapConstant_nonneg hγsource hCell s
    have hCfull (s : ℕ) : 0 ≤ Cfull s := add_nonneg (hβ s)
      (mul_nonneg (hKraw s) (add_nonneg (hβ s) (inv_nonneg.mpr hγsource.le)))
    have hDfull (s : ℕ) : 0 ≤ Dfull s := mul_nonneg (hLtrade s) (hCfull (s + 1))
    have hCpositive (s : ℕ) : 0 ≤ Cpositive s := add_nonneg (hβ s)
      (mul_nonneg (hKpositive s) (add_nonneg (hβ s) (inv_nonneg.mpr hγsource.le)))
    have hDpositive (s : ℕ) : 0 ≤ Dpositive s :=
      mul_nonneg (hLtrade s) (hCpositive (s + 1))
    refine ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG,
      sourceCap, hsourceCap, hcapSource, hcapMeasured', hcapOne,
      Cell, Kraw, Cfull, Dfull, Kpositive, Cpositive, Dpositive,
      hCell, hKraw, hCfull, hDfull, hKpositive, hCpositive, hDpositive, ?_⟩
    intro v hv hpos hinterval hvnorm
    obtain ⟨Vzero, hzeroActions, hzeroBound, hzeroLocal, hzeroGlobal, hzeroAdjoint, hexterior, hsourceDensity⟩ :=
      hsource v hv hpos hinterval hvnorm
    refine ⟨Vzero, hzeroActions, hzeroBound, hzeroLocal, hzeroGlobal, hzeroAdjoint, hexterior, ?_⟩
    intro σ hσ cσ e
    have hσdensity : σ ∈ Ioc (0 : ℝ) densityCap := ⟨hσ.1, hσ.2.trans hcapSource⟩
    have hσmeasured : σ ∈ Ioc (0 : ℝ) σ₀ := ⟨hσ.1, hσ.2.trans hcapMeasured'⟩
    obtain ⟨Vop, huniq, hactions, hnorm, hsourceLocal, hnormalGap, hgapRow, hinverse⟩ := hsourceDensity σ hσ
    refine ⟨Vop, huniq, hactions, hnorm, hsourceLocal, hnormalGap, hgapRow, ?_⟩
    intro Arow _Erow Q₀
    obtain ⟨hEinv, hSelf, hleft, hright, hnorminv, hrightid, hphysicalInverse, hreg, hstep, hest⟩ := hinverse
    refine ⟨hEinv, hSelf, hleft, hright, hnorminv, hrightid, hphysicalInverse, ?_⟩
    intro S densityProfile
    refine ⟨hreg, hstep, hest, ?_, ?_⟩
    · intro _hvzero
      subst v
      obtain ⟨_hsupport, _hb, _hlow, Vanalytic, hanalytic, hmatching⟩ :=
        hcarriers σ hσdensity (fun _ _ ↦ 0) hv hpos hinterval hvnorm
      have _hopEq : Vanalytic = Vop := huniq Vanalytic (fun i ↦ (hanalytic i).2.2.1)
      subst Vanalytic
      obtain ⟨_hplateau, Vmeasured, _hmeasrep, _hmeasnorm, hmeasrep,
        _hmeasuniq, _hmeastest, _hmeasnormal, hrawMeasured⟩ := hmeasured σ hσmeasured
      let χ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 1
      have hmeasEq : (fun i ↦ restrictCarrier χ (Vmeasured i)) =
          (fun i ↦ restrictCarrier χ (Vop i)) := by
        funext i
        exact (((hmatching i).2.2.2.2.2.2.2 hrMeasure hMeasureCell (hra i)).2.2.2 rfl
          (restrictCarrier χ (Vmeasured i)) (hmeasrep i)).1
      obtain ⟨hrawOuter, _hdensityOuter⟩ := hrawMeasured (coeff σ) (hformula σ hσmeasured)
        (fun i ↦ restrictCarrier χ (Vmeasured i)) hmeasrep
      rw [hmeasEq] at hrawOuter
      have hrawInner := hinner
        (imageChannel (coeff σ) χ (FixedCutoffs.periodic hrMeasure hMeasureCell 2))
        (fun i ↦ restrictCarrier χ (Vop i)) (FixedCutoffs.periodic hrMeasure hMeasureCell 0)
        hrawOuter
      have hzeroNorm (K : Set (Euclidean (n - 1) × Euclidean 3)) (p : ℕ) :
          cNorm K p (fun _ ↦ (0 : ℝ)) = 0 := cNorm_zero K p
      have hinv (s : ℕ) (f : OutputL2 n) (hf : f ∈ S.level s) :
          Q₀ f ∈ S.level s ∧ S.gradeNorm s (Q₀ f) ≤ β s * (S.gradeNorm s f + ‖f‖) := by
        simpa only [densityProfile, hzeroNorm, Finset.sum_const_zero, add_zero, one_mul]
          using hest s f hf
      have hfull (s : ℕ) (f : OutputL2 n) (hf : f ∈ S.level s) :
          CoerciveInverse.rightInverse Arow f ∈ augmentedInputLevel n ι s ∧
          S.gradeNorm s (Q₀ f) + (augmentedInputSobolevScale n ι).gradeNorm s
              (CoerciveInverse.rightInverse Arow f) ≤ Cfull s * (S.gradeNorm s f + ‖f‖) := by
        have hi := hinv s f hf
        refine ⟨(hrawInner s _ hi.1).1, ?_⟩
        simpa only [one_mul] using inverse_add_rightInverse_gradeNorm_le S
          (augmentedInputSobolevScale n ι) Arow hγsource hgapRow (hKraw s) zero_le_one
          hi.1 (by simpa only [one_mul] using hi.2)
          (fun w hw ↦ by simpa only [one_mul] using (hrawInner s w hw).2)
      refine ⟨hrawInner, hfull, ?_⟩
      intro s f hf raw
      have hfullNext := hfull (s + 1) f hf
      obtain ⟨hrawOne, hmem, huncut, hcut⟩ := htrade s raw hfullNext.1
      have hrawBound : (augmentedInputSobolevScale n ι).gradeNorm (s + 1) raw ≤
          Cfull (s + 1) * (S.gradeNorm (s + 1) f + ‖f‖) := by
        have hn := S.gradeNorm_nonneg (s + 1) (Q₀ f)
        linarith only [hfullNext.2, hn]
      refine ⟨hrawOne, hmem, huncut.trans ?_, hcut.trans ?_⟩ <;>
        simpa only [Dfull, mul_assoc] using mul_le_mul_of_nonneg_left hrawBound (hLtrade s)

    · intro vDensity hvDensity hDensityInterval hlabels highSize _dCorrected
      have hlowDensity (i : ι) : cNorm
          (closedBall ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i))
            (L i.1.1.1.1 i.2 (selected i) / 8)) (2 * (n + 1) + 14)
              (PositiveBackground.densityOnInitialLabels (vDensity i)) ≤ 1 := by
        rw [← hlabels i]
        exact hvnorm i
      obtain ⟨_Vcorrected, _hLocalCorrected, _hMeasuredCorrected, _hUniqueCorrected,
        hrawCorrected⟩ := hpositive σ hσmeasured vDensity hvDensity hDensityInterval hlowDensity
      let χ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 1
      let angular := fun i ↦ angularMask (z i) (NormedSpace.normalize (ηb i))
        (ha' i) (angularWidth_spec (hηb i) (hr' i)).1
      let measuredSource := fun i ↦ data (family i) (cσ i).Q (sourceDilation H.map σ)
        (rowi i) (coli i) (cσ i).forward (cσ i).inverse
          (fun q ↦ positiveDensityAmplitude σ (v i q)) hrMeasure hMeasureCell
          (angular i) FixedCutoffs.highFrequency
      let correctedSource := fun i ↦ CorrectedPositiveInverse.correctedCarrierData
        (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
          (seed i).forward (seed i).inverse (fun _ ↦ 1) hrMeasure hMeasureCell
          (angular i) FixedCutoffs.highFrequency σ) (vDensity i)
      have hsourceTest (i : ι) (f : carrierInitialTestSpace n) :
          restrictCarrier χ (Vop i) (carrierInitialTestToLp f) =ᵐ[volume]
            carrierTestIntegral (measuredSource i) f.val := by
        have hm := NormalizedMeasurement.supplied_carrier_common_measurement (e i)
          hrMeasure (ha' i) hMeasureCell (hlocal i) (hra i) rfl (fun _ _ ↦ rfl) rfl
        exact (((hm.2.2.2.2.2.2.2.2 (Vop i)).2.1 (hactions i).1).1 f)
      have hsourceMeasured (i : ι) (w : ComplexOutputL2 n) :
          (restrictCarrier χ (Vop i)).adjoint w =ᵐ[carrierMeasure n]
            carrierAdjointIntegral (measuredSource i) w := by
        have hm := NormalizedMeasurement.supplied_carrier_common_measurement (e i)
          hrMeasure (ha' i) hMeasureCell (hlocal i) (hra i) rfl (fun _ _ ↦ rfl) rfl
        exact ((hm.2.2.2.2.2.2.2.2 (Vop i)).2.2 (hactions i).2 w).2
      have hflowMeasured (i : ι) : MapsTo (densityCoordinates (family i))
          (closedBall (0 : Euclidean n) (4 * rMeasure) ×ˢ carrierSupport (z i) (r := a' i))
          (outputCylinder ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i))
            (Rc i.1.1.1.1 i.2 (selected i)) (τlead i.1.1.1.1 i.2 (selected i))) := by
        obtain ⟨_horigin, _hcompact, _hcone, _hρ, _hτ, _hW, _hKiW, _hBi, _hWBi,
          _hBiDom, hDc, _hfoot, hsupport, _⟩ := (hconic i).2
        rintro ⟨x, z'⟩ ⟨hx, hz⟩
        apply hflow i.1.1.1.1 i.2 (selected i)
        apply hDc.trans inter_subset_left
        apply (Dc i).field.ball_subset
        apply hsupport
        refine ⟨?_, hz⟩
        have hx₂ : x ∈ closedBall (0 : Euclidean n) (2 * a' i) :=
          closedBall_subset_closedBall (by linarith [hra i]) hx
        have hp : x ∈ interior {y | FixedCutoffs.physical (ha' i) 1 y = 1} := by
          apply FixedCutoffs.physical_plateau (ha' i) 1
          simpa only [Fin.val_one, Nat.cast_one, one_add_one_eq_two] using hx₂
        have hxone : FixedCutoffs.physical (ha' i) 1 x = 1 :=
          interior_subset (s := {y : Euclidean n | FixedCutoffs.physical (ha' i) 1 y = 1}) hp
        apply subset_tsupport
        change FixedCutoffs.physical (ha' i) 1 x ≠ 0
        rw [hxone]
        exact one_ne_zero
      have hkernelMatch (i : ι) :
          carrierTestIntegral (measuredSource i) = carrierTestIntegral (correctedSource i) ∧
          carrierAdjointIntegral (measuredSource i) = carrierAdjointIntegral (correctedSource i) := by
        obtain ⟨_, _, _, _, _, hrankσ, _, _⟩ := hcurrent σ hσdensity i
        dsimp only [measuredSource, correctedSource]
        rw [hlabels i]
        exact (PositiveBackground.retained_source_positiveScalar_kernel_and_integrals
          (family i) (hD.2.2.2.2.1 i.1.1.1.1 i.2).1
          (hΩ i.1.1.1.1 i.2 (selected i)) (hKΩ i.1.1.1.1 i.2 (selected i))
          (hpatchStrong i.1.1.1.1 i.2 (selected i))
          (hRc i.1.1.1.1 i.2 (selected i)) (hτ i.1.1.1.1 i.2 (selected i))
          (hτR i.1.1.1.1 i.2 (selected i)) (hbuffer i.1.1.1.1 i.2 (selected i))
          H.contDiff (fun x hx ↦ H.fullNormalRank x (hUH hx))
          (hphysical i.1.1.1.1 i.2) (seed i) (htrans i.1.1.1.1 i.2 (selected i))
          (fun x _ ↦ H.inducedMetric_eq_one x) hσ.1 (hσ.2.trans hcapOne) (cσ i) hrankσ
          hrMeasure hMeasureCell (z i) (NormedSpace.normalize (ηb i)) (ha' i)
          (angularWidth_spec (hηb i) (hr' i)).1 (hflowMeasured i)
          FixedCutoffs.highFrequency (vDensity i)
          (fun p ↦ le_trans (by norm_num) (hDensityInterval i p).1)).2
      have hcorrectedTest (i : ι) (f : carrierInitialTestSpace n) :
          restrictCarrier χ (Vop i) (carrierInitialTestToLp f) =ᵐ[volume]
            carrierTestIntegral (correctedSource i) f.val := by
        rw [← (hkernelMatch i).1]
        exact hsourceTest i f
      have hcorrectedRep (i : ι) (w : ComplexOutputL2 n) :
          (restrictCarrier χ (Vop i)).adjoint w =ᵐ[carrierMeasure n]
            carrierAdjointIntegral (correctedSource i) w := by
        rw [← (hkernelMatch i).2]
        exact hsourceMeasured i w
      obtain ⟨hrawPositive, _hdensityPositive⟩ :=
        hrawCorrected (coeff σ) (hformula σ hσmeasured)
          (fun i ↦ restrictCarrier χ (Vop i)) hcorrectedRep
      have hrawInner : ∀ s w, w ∈ S.level s →
          Arow.adjoint w ∈ augmentedInputLevel n ι s ∧
          (augmentedInputSobolevScale n ι).gradeNorm s (Arow.adjoint w) ≤
            Kpositive s * (S.gradeNorm s w + highSize s * ‖w‖) := by
        intro s w hw
        have hw' : w ∈ periodicSobolevLevel n (Euclidean n) s := by
          simpa only [S, periodicSobolevScale] using hw
        simpa only [Arow, S, ψ, χ, ι, highSize, densityProfile, hlabels, Nat.add_assoc]
          using hrawPositive s w hw'
      have hinv (s : ℕ) (f : OutputL2 n) (hf : f ∈ S.level s) :
          Q₀ f ∈ S.level s ∧ S.gradeNorm s (Q₀ f) ≤
            β s * (S.gradeNorm s f + highSize s * ‖f‖) := hest s f hf
      have hsize (s : ℕ) : 0 ≤ highSize s :=
        add_nonneg zero_le_one (Finset.sum_nonneg fun i _ ↦ cNorm_nonneg _ _ _)
      have hfull (s : ℕ) (f : OutputL2 n) (hf : f ∈ S.level s) :
          CoerciveInverse.rightInverse Arow f ∈ augmentedInputLevel n ι s ∧
          S.gradeNorm s (Q₀ f) + (augmentedInputSobolevScale n ι).gradeNorm s
              (CoerciveInverse.rightInverse Arow f) ≤
            Cpositive s * (S.gradeNorm s f + highSize s * ‖f‖) := by
        have hi := hinv s f hf
        refine ⟨(hrawInner s _ hi.1).1, ?_⟩
        exact inverse_add_rightInverse_gradeNorm_le S (augmentedInputSobolevScale n ι) Arow
          hγsource hgapRow (hKpositive s) (hsize s) hi.1 hi.2
          (fun w hw ↦ (hrawInner s w hw).2)
      refine ⟨fun i ↦ ⟨hcorrectedTest i, hcorrectedRep i⟩, hrawInner, hfull, ?_⟩
      intro s f hf raw
      have hfullNext := hfull (s + 1) f hf
      obtain ⟨hrawOne, hmem, huncut, hcut⟩ := htrade s raw hfullNext.1
      have hrawBound : (augmentedInputSobolevScale n ι).gradeNorm (s + 1) raw ≤
          Cpositive (s + 1) * (S.gradeNorm (s + 1) f + highSize (s + 1) * ‖f‖) := by
        have hnorm := S.gradeNorm_nonneg (s + 1) (Q₀ f)
        linarith only [hfullNext.2, hnorm]
      refine ⟨hrawOne, hmem, huncut.trans ?_, hcut.trans ?_⟩ <;>
        simpa only [Dpositive, mul_assoc] using mul_le_mul_of_nonneg_left hrawBound (hLtrade s)
  · obtain ⟨Ccompare, Bsource, Mzero, hCcompare, hBsource, hMzero, hnormal⟩ := hnormal
    exact ⟨Ccompare, Bsource, Mzero, hCcompare, hBsource, hMzero, hAngularExtraCap, hnormal⟩

end JanetCartan.PhysicalSeed.AngularRaw
