module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourceRawAdjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.FiniteAdjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AuxiliaryAdjoints
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.InputEstimates
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.MeasuredData

/-!
# The actual normalized finite adjoint on one common measurement chart

Construct the local adjoints from the supplied retained seed charts, choose
one common measurement radius, and construct the image coefficients from the
same flat reference. The real finite row and its image/exterior slots have
uniform all-order raw estimates. The original density multipliers give both
initial-space estimates for this very augmented adjoint. No raw estimate or
coercivity is an input.

Consumers: `PositiveBackground.SourceInverse.hrawReg/hraw` and normalized
`ContinuumInverse` assembly (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:prop:bg-normalized`, `app:ch_background:eq:bg-density-adjoint`).
The retained finite selection supplies its own seed and fixed masks. Contracted
null-flow charts are needed only to identify the current physical carrier;
the normalized adjoint estimates are constructed directly from the seed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts.ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierSobolev DensityMultiplier
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference
open ContinuumNormal.FrozenModel
open NullTransport ActualFlow FlowAmplitude PhaseExtension
open PeriodicSobolevSpace ContinuumCommutator.ImageChannel.Differential

/-- On prescribed physical, angular, coefficient, initial-space and exterior cutoffs,
construct the same normalized finite adjoint and its full raw/density bounds.
The support caps are chosen first; any prescribed submasks within those caps
are then retained literally. The original finite index type, seed charts,
minor and ODE cylinders are unchanged. Coefficient arrays are constructed on
the supplied `χcoeff`. The bounds hold for every selected coefficient array
with that exact geometric formula and every selected carrier with the same
literal normalized adjoint. Their equality to the constructed operators is
proved by the coefficient formula and literal adjoint uniqueness.
All constants precede `σ`; no raw estimate or coercivity is assumed.
The normalized seed kernel is estimated without assuming the existence of a
contracted null-flow chart. For any such chart, the retained ODE uniqueness
theorem separately proves its literal kernel equality.

The returned initial plateau works for every allowed submask. The density
estimate also permits any other prescribed smooth initial cutoff, so the
original selection's cutoff need not be reselected. The supplied smooth
exterior cutoff is independent of the source and measurement radius. Consumers:
`PositiveBackground.SourceInverse.hrawReg/hraw` and normalized
`ContinuumInverse` assembly (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-density-adjoint`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_source_augmentedAdjoint_for_prescribed_masks
    {n : ℕ} {ι : Type*} [Fintype ι] (H : FlatReference n)
    {P : ι → Patch n} {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : ι → Set (Euclidean n × Euclidean 3)} (hΩ : ∀ i, IsOpen (Ω i))
    {zCell : ι → Euclidean 3} {ρ Rc M τ : ι → ℝ} {row col : ι → Fin n}
    (hKΩ : ∀ i, closedBall ((0 : Euclidean n), zCell i) (ρ i) ⊆ Ω i)
    (hpatch : ∀ i, Ω i ⊆ ball 0 (T i).physicalRadius ×ˢ parameterCube (2 * (P i).radius))
    (hRc : ∀ i, 0 < Rc i) (hτ : ∀ i, 0 < τ i) (hτR : ∀ i, τ i ≤ Rc i / 16)
    (hbuffer : ∀ i, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i))
      (closedBall ((0 : Euclidean n), zCell i) (ρ i)))
    (hphysical : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (seed : (i : ι) → FlowConstruction.Chart (T i) (Ω i)
      (closedBall ((0 : Euclidean n), zCell i) (ρ i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (M i) (τ i) (row i) (col i) H.map)
    (htrans : ∀ i, ∀ q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU (seed i).Q.1 (seed i).Q.2.1).hp q,
        (T i).data.adapted.normal⟫_ℝ ≠ 0)
    {R : ι → ℝ} {V : ι → Set CarrierParameter} (hR : ∀ i, 0 < R i)
    (hRphysical : ∀ i, R i ≤ (T i).physicalRadius)
    (hRU : ∀ i, ball (0 : Euclidean n) (R i) ⊆ U)
    (hV : ∀ i, IsOpen (V i))
    (hVP : ∀ i, V i ⊆ parameter ⁻¹' parameterInterior (3 * (P i).radius / 2))
    (hflow : ∀ i, MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) (R i) ×ˢ V i)
      (FlowConstruction.outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τ i)))
    {z₀ : ι → Euclidean 3} (hz₀ : ∀ i, z₀ i ∈ parameterInterior (P i).radius)
    (hzV : ∀ i, (z₀ i 0, spectatorCenter (z₀ i)) ∈ V i)
    {k : ι → Euclidean n} (hk : ∀ i, k i ≠ 0)
    (hinc : ∀ i, incidence (k i) ((P i).toFun (z₀ i)) = 0)
    (hd : ∀ i, fderiv ℝ (fun z ↦ incidence (k i) ((P i).toFun z)) (z₀ i)
      (EuclideanSpace.single 0 1) ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) :
    let θ := fun i ↦ NormedSpace.normalize
      ((T i).data.adapted.embedding.toContinuousLinearMap.adjoint (k i))
    ∃ aMax bMax : ι → ℝ,
      (∀ i, 0 < aMax i) ∧ (∀ i, 0 < bMax i) ∧ (∀ i, aMax i < cap) ∧
    ∃ χplateau : ι → ContDiffBump (0 : CarrierVariable n),
    ∀ a b : ι → ℝ, ∀ ha : ∀ i, 0 < a i, ∀ hb : ∀ i, 0 < b i,
      (∀ i, a i ≤ aMax i) → (∀ i, b i ≤ bMax i) →
    ∀ r : ℝ, ∀ hr : 0 < r, ∀ hcell : 4 * r < 1 / 2,
      6 * r < 1 / 2 → (∀ i, 6 * r < a i) →
    ∀ χcoeff : Euclidean n → ℝ, ContDiff ℝ ∞ χcoeff →
      tsupport χcoeff ⊆ ball 0 (5 * r) →
      closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1} →
    ∀ χinitial : ι → ContDiffBump (0 : CarrierVariable n),
    ∀ ψ : C(Torus n, ℝ), IsSmoothPeriodic ψ →
      (∀ i, supportedChart (n := n) (z₀ i) (a i) ⊆
        ball (0 : Euclidean n) (R i) ×ˢ V i) ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ (coeff : ℝ → GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
      (Cbound Lbound : ℕ → ℝ),
      (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      (∀ σ j, IsSmoothPeriodic (coeff σ j)) ∧
      (∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ j x,
        coeff σ j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
          GeometricProfile.geometricReducedCoefficients (sourceDilation H.map σ)
            (AmplitudeBound.centeredTorusRepresentative x) j) ∧
    let χ := FixedCutoffs.periodic (n := n) hr hcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hr hcell 2
    ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      let e := fun i ↦ normalizedCarrierData (T i) (seed i).Q H.map
        (row i) (col i) (seed i).forward (seed i).inverse (fun _ ↦ 1) hr hcell
        (angularMask (z₀ i) (θ i) (ha i) (hb i)) FixedCutoffs.highFrequency σ
      (∀ i, MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.2, normalizedTransportPosition (T i) (seed i).Q σ p))
        (closedBall 0 (6 * r) ×ˢ carrierSupport (z₀ i) (r := a i))
        (interior {q | χplateau i q = 1})) ∧
      (∀ current : (i : ι) → FlowConstruction.Chart (T i) (Ω i)
        (closedBall ((0 : Euclidean n), zCell i) (ρ i))
        ((0 : Euclidean (n - 1)), zCell i) (Rc i) (M i) (τ i) (row i) (col i)
        (sourceDilation H.map σ),
        ∀ i, carrierKernel (data (T i) (current i).Q (sourceDilation H.map σ)
          (row i) (col i) (current i).forward (current i).inverse (fun _ ↦ σ) hr hcell
          (angularMask (z₀ i) (θ i) (ha i) (hb i)) FixedCutoffs.highFrequency) =
          carrierKernel (e i)) ∧
      ∃ A : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i w, (A i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
        (∀ i, ∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) → B = A i) ∧
        ∀ selectedCoeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
          (∀ j x, selectedCoeff j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
            GeometricProfile.geometricReducedCoefficients (sourceDilation H.map σ)
              (AmplitudeBound.centeredTorusRepresentative x) j) →
        ∀ B : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ i w, (B i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) →
        let rowOp := augmentedRow (imageChannel selectedCoeff χ χsrc) B ψ
        (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
          rowOp.adjoint w ∈ augmentedInputLevel n ι s ∧
          (augmentedInputSobolevScale n ι).gradeNorm s (rowOp.adjoint w) ≤
            Cbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + ‖w‖)) ∧
        ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
          let u := rowOp.adjoint w
          ∃ hf : ∀ i, MemRawSobolev 1 (u.fst.snd i),
            (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
              (densityUncut (z₀ i) (θ i) (ha i) (hb i) (u.fst.snd i) (hf i))) ∧
              MemPhysicalSobolev s (physicalComplexifyL2
              (density (z₀ i) (θ i) (ha i) (hb i) (χinitial i) (u.fst.snd i) (hf i)))) ∧
            densityUncutFamilySize z₀ θ ha hb s u ≤
              Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖) ∧
            densityFamilySize z₀ θ ha hb χinitial s u ≤
              Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖) := by
  classical
  let θ := fun i ↦ NormedSpace.normalize
    ((T i).data.adapted.embedding.toContinuousLinearMap.adjoint (k i))
  choose aMax bMax haMax hbMax haMaxCap χplateau si hsi _hsi1 hsubmasks using
    fun i ↦ exists_normalized_seed_rawAdjoint_for_submasks H (hP i) (T i) hUH hbounded (hΩ i)
      (hKΩ i) (hpatch i) (hRc i) (hτ i) (hτR i) (hbuffer i) (hphysical i) (seed i)
      (htrans i) (hR i) (hRphysical i) (hRU i) (hV i) (hVP i) (hflow i)
      (hz₀ i) (hzV i) (hk i) (hinc i) (hd i) hcap
  refine ⟨aMax, bMax, haMax, hbMax, haMaxCap, χplateau, ?_⟩
  intro a b ha hb haSub hbSub r hr hcell hrhalf hra χcoeff hχcoeff hχsupport hχplateau χinitial ψ hψ
  choose hlocal hMaskE Craw _Llocal hCraw _hLlocal hrawLocal using
    fun i ↦ hsubmasks i (a i) (b i) (ha i) (hb i) (haSub i) (hbSub i)
  refine ⟨hMaskE, ?_⟩
  obtain ⟨sLocal, hsLocal, hsLocali⟩ := Pi.exists_forall_pos_add_lt hsi
  obtain ⟨sImage, hsImage, hsImage1, coeff₀, coeff', _hformula₀,
    hcoeff₀, _hcoeffAgree₀, hformula, hcoeff', _hcoeffAgree, hjets',
    _himageFormula, _himageAction, _himageAdjoint⟩ :=
    RetainedAssembly.NormalizedImage.exists_normalized_image_coefficients H
      (by positivity : 0 < 4 * r) (by linarith : 4 * r < 5 * r)
      (by linarith : 5 * r < 6 * r) hrhalf hχcoeff hχsupport hχplateau
  choose Pimage hPimage _hjets₀ hjets using hjets'
  have hsmooth := FixedCutoffs.periodic_smooth (n := n) hr hcell
  let χ := FixedCutoffs.periodic (n := n) hr hcell 1
  let χsrc := FixedCutoffs.periodic (n := n) hr hcell 2
  let coeff := fun σ ↦ if hσ : σ ∈ Ioc (0 : ℝ) sImage then coeff' σ hσ else coeff₀
  have hcoeff (σ) (j) : IsSmoothPeriodic (coeff σ j) := by
    dsimp only [coeff]
    split_ifs with hσ
    · exact hcoeff' σ hσ j
    · exact hcoeff₀ j
  have heqcoeff σ (hσ : σ ∈ Ioc (0 : ℝ) sImage) : coeff σ = coeff' σ hσ := dite_eq_left hσ
  obtain ⟨Caux, hCaux, haux⟩ := AuxiliaryAdjoints.exists_auxiliaryAdjoints_profile
    χ χsrc ψ (hsmooth 1) (hsmooth 2) hψ
    (add_nonneg (hPimage 0).le (hPimage 1).le) Pimage (fun m ↦ (hPimage m).le)
  let Kcut (s : ℕ) := 1 + ‖cutoffSobolev χ (hsmooth 1) s‖ + ‖cutoffMultiplier (n := n) χ‖
  have hKcut (s : ℕ) : 0 ≤ Kcut s := by dsimp [Kcut]; positivity
  let Ccarrier (s : ℕ) := (∑ i, 2 * Craw i s) * Kcut s
  have hCcarrier (s : ℕ) : 0 ≤ Ccarrier s :=
    mul_nonneg (Finset.sum_nonneg fun i _ ↦ mul_nonneg (by norm_num) (hCraw i s)) (hKcut s)
  let Cbound := fun s ↦ Ccarrier s + Caux s
  have hCbound (s : ℕ) : 0 ≤ Cbound s := add_nonneg (hCcarrier s) (hCaux s).le
  obtain ⟨L, hL, hdensity⟩ := exists_densityFamily_gradeNorm_bounds z₀ θ ha hb χinitial
  let σ₀ := min sLocal sImage
  have hcapImage {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) sImage :=
    ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hcapLocal {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) (i : ι) : σ ∈ Ioc (0 : ℝ) (si i) :=
    ⟨hσ.1, (hσ.2.trans (min_le_left _ _)).trans (by simpa using (hsLocali i).le)⟩
  refine ⟨σ₀, lt_min hsLocal hsImage, (min_le_right _ _).trans hsImage1,
    coeff, Cbound, (fun s ↦ L s * Cbound (s + 1)), hCbound,
    (fun s ↦ mul_nonneg (hL s) (hCbound (s + 1))), hcoeff, ?_, ?_⟩
  · intro σ hσ j x
    rw [heqcoeff σ (hcapImage hσ)]
    exact hformula σ (hcapImage hσ) j x
  · intro _ _ σ hσ
    choose hplateau hkernel Ulocal hrep _hunique _hcomplex hrealMem hrealBound _hlocalDensity using
      fun i ↦ hrawLocal i σ (hcapLocal hσ i)
    refine ⟨fun i ↦ NormalizedMeasurement.initial_buffer_on_common_source
      (z₀ i) hr (hra i) _ _ (hplateau i), ?_⟩
    let dlocal := fun i ↦ normalizedCarrierData (T i) (seed i).Q H.map
      (row i) (col i) (seed i).forward (seed i).inverse (fun _ ↦ 1) (ha i) (hlocal i)
      (angularMask (z₀ i) (θ i) (ha i) (hb i)) FixedCutoffs.highFrequency σ
    let e := fun i ↦ normalizedCarrierData (T i) (seed i).Q H.map
      (row i) (col i) (seed i).forward (seed i).inverse (fun _ ↦ 1) hr hcell
      (angularMask (z₀ i) (θ i) (ha i) (hb i)) FixedCutoffs.highFrequency σ
    have hcommonKernel
        (current : (i : ι) → FlowConstruction.Chart (T i) (Ω i)
          (closedBall ((0 : Euclidean n), zCell i) (ρ i))
          ((0 : Euclidean (n - 1)), zCell i) (Rc i) (M i) (τ i) (row i) (col i)
          (sourceDilation H.map σ)) (i : ι) :
        carrierKernel (data (T i) (current i).Q (sourceDilation H.map σ)
          (row i) (col i) (current i).forward (current i).inverse (fun _ ↦ σ) hr hcell
          (angularMask (z₀ i) (θ i) (ha i) (hb i)) FixedCutoffs.highFrequency) =
          carrierKernel (e i) := by
      let dcurrent := data (T i) (current i).Q (sourceDilation H.map σ)
        (row i) (col i) (current i).forward (current i).inverse (fun _ ↦ σ) (ha i) (hlocal i)
        (angularMask (z₀ i) (θ i) (ha i) (hb i)) FixedCutoffs.highFrequency
      have hs := NormalizedMeasurement.supplied_carrier_common_measurement dcurrent
        hr (ha i) hcell (hlocal i) (hra i) rfl (fun _ _ ↦ rfl) rfl
      have hn := NormalizedSelection.normalizedCarrierData_common_measurement
        (T i) (seed i).Q H.map (row i) (col i) (seed i).forward (seed i).inverse
        (fun _ ↦ 1) hr (ha i) hcell (hlocal i)
        (angularMask (z₀ i) (θ i) (ha i) (hb i)) FixedCutoffs.highFrequency σ (hra i)
      funext x u
      exact (hs.2.2.2.2.2.2.2.1 x u).trans
        ((congrArg (fun v ↦ χ x • v) (congrFun (congrFun (hkernel i (current i)) x) u)).trans
          (hn.1 x u).symm)
    let A := fun i ↦ CommonMeasurement.restrictCarrier χ (Ulocal i)
    have hArep (i : ι) (w : ComplexOutputL2 n) :
        (A i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w := by
      have hs := NormalizedMeasurement.supplied_carrier_common_measurement (dlocal i)
        hr (ha i) hcell (hlocal i) (hra i) rfl (fun _ _ ↦ rfl) rfl
      exact ((hs.2.2.2.2.2.2.2.2 (Ulocal i)).2.2
        (fun w ↦ ⟨(memLp_congr_ae (hrep i w)).mp (Lp.memLp ((Ulocal i).adjoint w)),
          hrep i w⟩) w).2
    let rowOp := augmentedRow (imageChannel (coeff σ) χ χsrc) A ψ
    have hfamily (s : ℕ) (v : PeriodicSobolevSpace n (Euclidean n) s) :
        ∃ u : CarrierFamilySobolevSpace n ι s,
          carrierFamilyToL2 s u = (carrierRow A).adjoint (toL2 s v) ∧
          ‖u‖ ≤ Ccarrier s * (‖v‖ + ‖toL2 s v‖) := by
      let w := cutoffSobolev χ (hsmooth 1) s v
      have heq (i : ι) : (carrierChannel (A i)).adjoint (toL2 s v) =
          (carrierChannel (Ulocal i)).adjoint (toL2 s w) := by
        rw [toL2_cutoffSobolev, CommonMeasurement.carrierChannel_restrictCarrier,
          ContinuousLinearMap.adjoint_comp, cutoffMultiplier_adjoint]
        rfl
      let u : CarrierFamilySobolevSpace n ι s := WithLp.toLp 2 (fun i ↦
        RawSobolevSpace.ofRawL2 s ((carrierChannel (Ulocal i)).adjoint (toL2 s w))
          (hrealMem i s w))
      refine ⟨u, ?_, ?_⟩
      · rw [carrierRow_adjoint_apply]
        apply PiLp.ext
        intro i
        exact (RawSobolevSpace.toRawL2_ofRawL2 s _ _).trans (heq i).symm
      · have he (i : ι) : ‖u i‖ = rawSobolevNorm s
            ((carrierChannel (Ulocal i)).adjoint (toL2 s w)) := by
          rw [RawSobolevSpace.norm_eq, RawSobolevSpace.toRawL2_ofRawL2]
        have hw : ‖w‖ ≤ Kcut s * ‖v‖ :=
          ((cutoffSobolev χ (hsmooth 1) s).le_opNorm v).trans
            (mul_le_mul_of_nonneg_right
              (by dsimp [Kcut]; linarith [norm_nonneg (cutoffMultiplier (n := n) χ)])
              (norm_nonneg v))
        have hw₀ : ‖toL2 s w‖ ≤ Kcut s * ‖toL2 s v‖ := by
          rw [toL2_cutoffSobolev]
          exact ((cutoffMultiplier χ).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right
              (by dsimp [Kcut]; linarith [norm_nonneg (cutoffSobolev χ (hsmooth 1) s)])
              (norm_nonneg _))
        have hsum : 0 ≤ ∑ i, 2 * Craw i s :=
          Finset.sum_nonneg fun i _ ↦ mul_nonneg (by norm_num) (hCraw i s)
        calc
          ‖u‖ ≤ ∑ i, ‖u i‖ := carrierFamily_norm_le_sum s u
          _ ≤ ∑ i, (2 * Craw i s) * (‖w‖ + ‖toL2 s w‖) :=
            Finset.sum_le_sum fun i _ ↦ (he i).trans_le (hrealBound i s w)
          _ = (∑ i, 2 * Craw i s) * (‖w‖ + ‖toL2 s w‖) := (Finset.sum_mul ..).symm
          _ ≤ (∑ i, 2 * Craw i s) * (Kcut s * ‖v‖ + Kcut s * ‖toL2 s v‖) := by gcongr
          _ = _ := by dsimp [Ccarrier]; ring
    have hauxiliary (s : ℕ) (v : PeriodicSobolevSpace n (Euclidean n) s) :
        ∃ vi ve : PeriodicSobolevSpace n (Euclidean n) s,
          toL2 s vi = (imageChannel (coeff σ) χ χsrc).adjoint (toL2 s v) ∧
          toL2 s ve = (exteriorChannel ψ).adjoint (toL2 s v) ∧
          ‖vi‖ + ‖ve‖ ≤ Caux s * (‖v‖ + ‖toL2 s v‖) := by
      have hlow : ∀ j m, m ≤ 1 → ∀ x,
          ‖iteratedFDeriv ℝ m (periodicLift (coeff σ j)) x‖ ≤ Pimage 0 + Pimage 1 := by
        intro j m hm x
        rw [heqcoeff σ (hcapImage hσ)]
        apply ((hjets m σ (hcapImage hσ) j x).2).trans
        have hm' : m = 0 ∨ m = 1 := by omega
        rcases hm' with rfl | rfl <;> linarith [(hPimage 0).le, (hPimage 1).le]
      have hhigh : ∀ j m x,
          ‖iteratedFDeriv ℝ m (periodicLift (coeff σ j)) x‖ ≤ Pimage m * (1 + 0) := by
        intro j m x
        rw [heqcoeff σ (hcapImage hσ)]
        simpa only [add_zero, mul_one] using (hjets m σ (hcapImage hσ) j x).2
      simpa only [add_zero, one_mul] using
        (haux (coeff σ) (hcoeff σ) (fun _ ↦ 0) (fun _ ↦ le_rfl) monotone_const hlow hhigh s v)
    have hgrade (s : ℕ) (w : OutputL2 n) (hw : w ∈ periodicSobolevLevel n (Euclidean n) s) :
        rowOp.adjoint w ∈ augmentedInputLevel n ι s ∧
        (augmentedInputSobolevScale n ι).gradeNorm s (rowOp.adjoint w) ≤
          Cbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + ‖w‖) := by
      suffices hlift : ∀ v : PeriodicSobolevSpace n (Euclidean n) s,
          ∃ u : AugmentedInputSobolevSpace n ι s,
            augmentedInputToL2 s u = rowOp.adjoint (toL2 s v) ∧
            ‖u‖ ≤ Cbound s * (‖v‖ + 1 * ‖toL2 s v‖) by
        obtain ⟨hm, hbnd⟩ := augmentedAdjoint_gradeNorm_of_lifts rowOp s (Cbound s) 1 hlift w hw
        exact ⟨hm, by simpa only [one_mul] using hbnd⟩
      intro v
      obtain ⟨uc, huc, hbc⟩ := hfamily s v
      obtain ⟨vi, ve, hvi, hve, hba⟩ := hauxiliary s v
      let u : AugmentedInputSobolevSpace n ι s := WithLp.toLp 2 (WithLp.toLp 2 (vi, uc), ve)
      refine ⟨u, ?_, ?_⟩
      · rw [augmentedInputToL2_apply, physicalInputToL2_apply,
          augmentedRow_adjoint_apply, physicalRow_adjoint_apply]
        change WithLp.toLp 2 (WithLp.toLp 2 (toL2 s vi, carrierFamilyToL2 s uc), toL2 s ve) = _
        rw [hvi, hve, huc, exteriorChannel_adjoint]
      · have hsq : ‖u‖ ^ 2 = ‖vi‖ ^ 2 + ‖uc‖ ^ 2 + ‖ve‖ ^ 2 := by
          rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
          rfl
        have hnorm : ‖u‖ ≤ ‖vi‖ + ‖ve‖ + ‖uc‖ := by
          nlinarith [norm_nonneg u, norm_nonneg vi, norm_nonneg ve, norm_nonneg uc,
            mul_nonneg (norm_nonneg vi) (norm_nonneg ve),
            mul_nonneg (norm_nonneg vi) (norm_nonneg uc),
            mul_nonneg (norm_nonneg ve) (norm_nonneg uc)]
        calc
          _ ≤ ‖vi‖ + ‖ve‖ + ‖uc‖ := hnorm
          _ ≤ Caux s * (‖v‖ + ‖toL2 s v‖) + Ccarrier s * (‖v‖ + ‖toL2 s v‖) :=
            add_le_add hba hbc
          _ = _ := by dsimp [Cbound]; ring
    have hunique (i : ι) (B : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (hB : ∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) : B = A i := by
      have he := DerivativeKernels.literalCarrierAdjointOperator_unique (e i)
        B.adjoint (A i).adjoint hB (hArep i)
      simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg ContinuousLinearMap.adjoint he
    refine ⟨hcommonKernel, A, hArep, hunique, ?_⟩
    intro selectedCoeff hselectedCoeff B hB
    have hcoeffEq : selectedCoeff = coeff σ := by
      funext j
      apply ContinuousMap.ext
      intro x
      rw [hselectedCoeff j x, heqcoeff σ (hcapImage hσ)]
      exact (hformula σ (hcapImage hσ) j x).symm
    have hBEq : B = A := by
      funext i
      apply hunique i (B i)
      exact hB i
    subst selectedCoeff B
    refine ⟨hgrade, ?_⟩
    intro s w hw
    obtain ⟨hf, hmem, huncut, hcut⟩ := hdensity s _ (hgrade (s + 1) w hw).1
    refine ⟨hf, hmem, ?_, ?_⟩
    · exact (huncut.trans (mul_le_mul_of_nonneg_left (hgrade (s + 1) w hw).2 (hL s))).trans_eq
        (mul_assoc _ _ _).symm
    · exact (hcut.trans (mul_le_mul_of_nonneg_left (hgrade (s + 1) w hw).2 (hL s))).trans_eq
        (mul_assoc _ _ _).symm

/-- Construct all slots of the actual normalized augmented adjoint, including
its full raw Sobolev membership and both initial-density bounds. All masks,
initial cutoffs, source cap and constants precede `σ` and the supplied current
charts. The actual image coefficients come from the SAME `H`; the carrier
operators are constructed by `exists_retained_source_rawAdjoint` and then
restricted to the common physical measurement chart. Original angular masks,
carrier labels, source scalar `σ`, measure, Fourier factors and half-order
weights are retained. Literal adjoint uniqueness identifies every bounded
realization of these data, without identifying independent geometric choices.

The only family inputs are primitive retained charts and their geometric
buffers, supplied by normalized selection and normalized flow construction.
No `hrawReg`, `hraw`, normal gap or inverse is assumed
(`app:ch_background:prop:bg-adjoint`, `bg-density-adjoint`, `bg-normalized`). -/
theorem exists_retained_source_augmentedAdjoint
    {n : ℕ} {ι : Type*} [Fintype ι] (H : FlatReference n)
    {P : ι → Patch n} {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : ι → Set (Euclidean n × Euclidean 3)} (hΩ : ∀ i, IsOpen (Ω i))
    {zCell : ι → Euclidean 3} {ρ Rc M τ : ι → ℝ} {row col : ι → Fin n}
    (hKΩ : ∀ i, closedBall ((0 : Euclidean n), zCell i) (ρ i) ⊆ Ω i)
    (hpatch : ∀ i, Ω i ⊆ ball 0 (T i).physicalRadius ×ˢ parameterCube (2 * (P i).radius))
    (hRc : ∀ i, 0 < Rc i) (hτ : ∀ i, 0 < τ i) (hτR : ∀ i, τ i ≤ Rc i / 16)
    (hbuffer : ∀ i, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i))
      (closedBall ((0 : Euclidean n), zCell i) (ρ i)))
    (hphysical : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (seed : (i : ι) → FlowConstruction.Chart (T i) (Ω i)
      (closedBall ((0 : Euclidean n), zCell i) (ρ i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (M i) (τ i) (row i) (col i) H.map)
    (htrans : ∀ i, ∀ q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU (seed i).Q.1 (seed i).Q.2.1).hp q,
        (T i).data.adapted.normal⟫_ℝ ≠ 0)
    {R : ι → ℝ} {V : ι → Set CarrierParameter} (hR : ∀ i, 0 < R i)
    (hRphysical : ∀ i, R i ≤ (T i).physicalRadius)
    (hRU : ∀ i, ball (0 : Euclidean n) (R i) ⊆ U)
    (hV : ∀ i, IsOpen (V i))
    (hVP : ∀ i, V i ⊆ parameter ⁻¹' parameterInterior (3 * (P i).radius / 2))
    (hflow : ∀ i, MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) (R i) ×ˢ V i)
      (FlowConstruction.outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τ i)))
    {z₀ : ι → Euclidean 3} (hz₀ : ∀ i, z₀ i ∈ parameterInterior (P i).radius)
    (hzV : ∀ i, (z₀ i 0, spectatorCenter (z₀ i)) ∈ V i)
    {k : ι → Euclidean n} (hk : ∀ i, k i ≠ 0)
    (hinc : ∀ i, incidence (k i) ((P i).toFun (z₀ i)) = 0)
    (hd : ∀ i, fderiv ℝ (fun z ↦ incidence (k i) ((P i).toFun z)) (z₀ i)
      (EuclideanSpace.single 0 1) ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) :
    let θ := fun i ↦ NormedSpace.normalize
      ((T i).data.adapted.embedding.toContinuousLinearMap.adjoint (k i))
    ∃ a b : ι → ℝ, ∃ ha : ∀ i, 0 < a i, ∃ hb : ∀ i, 0 < b i,
    ∃ χinitial : ι → ContDiffBump (0 : CarrierVariable n),
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hcell : 4 * r < 1 / 2,
      6 * r < cap ∧ (∀ i, 6 * r < a i) ∧
    ∃ χcoeff : Euclidean n → ℝ,
      ContDiff ℝ ∞ χcoeff ∧ HasCompactSupport χcoeff ∧
      tsupport χcoeff ⊆ ball 0 (5 * r) ∧
      closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1} ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ (coeff : ℝ → GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
      (Cbound Lbound : ℕ → ℝ),
      (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      (∀ σ j, IsSmoothPeriodic (coeff σ j)) ∧
      (∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ j x,
        coeff σ j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
          GeometricProfile.geometricReducedCoefficients (sourceDilation H.map σ)
            (AmplitudeBound.centeredTorusRepresentative x) j) ∧
    let χ := FixedCutoffs.periodic (n := n) hr hcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hr hcell 2
    let ψ := FixedCutoffs.periodic (n := n) hr hcell 0
    ∀ σ ∈ Ioc (0 : ℝ) σ₀,
    ∀ current : (i : ι) → FlowConstruction.Chart (T i) (Ω i)
      (closedBall ((0 : Euclidean n), zCell i) (ρ i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (M i) (τ i) (row i) (col i)
      (sourceDilation H.map σ),
      (∀ i, MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.2, transportPosition (T i) (current i).Q p))
        (closedBall 0 (6 * r) ×ˢ carrierSupport (z₀ i) (r := a i))
        (interior {q | χinitial i q = 1})) ∧
      let d := fun i ↦ data (T i) (current i).Q (sourceDilation H.map σ)
        (row i) (col i) (current i).forward (current i).inverse (fun _ ↦ σ) hr hcell
        (angularMask (z₀ i) (θ i) (ha i) (hb i)) FixedCutoffs.highFrequency
      let e := fun i ↦ normalizedCarrierData (T i) (seed i).Q H.map
        (row i) (col i) (seed i).forward (seed i).inverse (fun _ ↦ 1) hr hcell
        (angularMask (z₀ i) (θ i) (ha i) (hb i)) FixedCutoffs.highFrequency σ
      (∀ i, carrierKernel (d i) = carrierKernel (e i)) ∧
      ∃ A : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i w, (A i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) ∧
        (∀ i, ∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) → B = A i) ∧
        let rowOp := augmentedRow (imageChannel (coeff σ) χ χsrc) A ψ
        (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
          rowOp.adjoint w ∈ augmentedInputLevel n ι s ∧
          (augmentedInputSobolevScale n ι).gradeNorm s (rowOp.adjoint w) ≤
            Cbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + ‖w‖)) ∧
        ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
          let u := rowOp.adjoint w
          ∃ hf : ∀ i, MemRawSobolev 1 (u.fst.snd i),
            (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
              (densityUncut (z₀ i) (θ i) (ha i) (hb i) (u.fst.snd i) (hf i))) ∧
              MemPhysicalSobolev s (physicalComplexifyL2
              (density (z₀ i) (θ i) (ha i) (hb i) (χinitial i) (u.fst.snd i) (hf i)))) ∧
            densityUncutFamilySize z₀ θ ha hb s u ≤
              Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖) ∧
            densityFamilySize z₀ θ ha hb χinitial s u ≤
              Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖) := by
  classical
  obtain ⟨a, b, ha, hb, _hacap, χinitial, hprescribed⟩ :=
    exists_retained_source_augmentedAdjoint_for_prescribed_masks H hP T hUH hbounded hΩ
      hKΩ hpatch hRc hτ hτR hbuffer hphysical seed htrans hR hRphysical hRU hV hVP hflow
      hz₀ hzV hk hinc hd hcap
  obtain ⟨r, hr, hcell, hrcap, _hrcap', hrhalf, hra, χcoeff, hχcoeff,
    _hχrange, hχcompact, hχsupport, hχplateau, _hsource, _hlocal, _hmul⟩ :=
    NormalizedMeasurement.exists_measurement_cutoffs_before_scale (n := n) a ha hcap hcap
  obtain ⟨hMaskE, σ₀, hσ₀, hσ₁, coeff, Cbound, Lbound, hCbound, hLbound, hcoeff, hformula, hrow⟩ :=
    hprescribed a b ha hb (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)
      r hr hcell hrhalf hra χcoeff hχcoeff hχsupport hχplateau χinitial
      (FixedCutoffs.periodic hr hcell 0) (FixedCutoffs.periodic_smooth hr hcell 0)
  refine ⟨a, b, ha, hb, χinitial, r, hr, hcell, hrcap, hra,
    χcoeff, hχcoeff, hχcompact, hχsupport, hχplateau,
    σ₀, hσ₀, hσ₁, coeff, Cbound, Lbound, hCbound, hLbound, hcoeff, hformula, ?_⟩
  intro χ χsrc ψ σ hσ current
  obtain ⟨hplateau, hkernel, A, hArep, hunique, hselected⟩ := hrow σ hσ
  refine ⟨?_, hkernel current, A, ?_, ?_, hselected (coeff σ) (hformula σ hσ) A hArep⟩
  · intro i p hp
    have hpLocal : p ∈ supportedChart (n := n) (z₀ i) (a i) := by
      exact ⟨closedBall_subset_closedBall (by linarith [hra i]) hp.1, hp.2⟩
    have hpE := hMaskE i hpLocal
    have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUH hx)
    have hposition := (SourceMatching.current_transportPosition_source_dilation_on_patch
      (T i) (seed i).Q (current i).Q H.contDiff hrank (hphysical i) (seed i).frame_eq
      (htrans i) hσ.1 (hσ.2.trans hσ₁) (current i).frame_eq).1
    have heq := hposition ⟨ball_subset_ball (hRphysical i) hpE.1,
      fun j ↦ (hVP i hpE.2 j).trans (by linarith [(hP i).1])⟩
    change (p.2, transportPosition (T i) (current i).Q p) ∈
      interior {q | χinitial i q = 1}
    rw [heq]
    exact hplateau i hp
  · intro i w
    rw [carrierAdjointIntegral_congr_kernel (hkernel current i)]
    exact hArep i w
  · intro i B hB
    apply hunique i B
    intro w
    rw [← carrierAdjointIntegral_congr_kernel (hkernel current i)]
    exact hB w

end JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
