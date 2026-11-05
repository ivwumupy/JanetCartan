module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.FootpointCutoff
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.UniformEndpoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.ScalarTransport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.LocalConstruction

/-!
# Actual local canonical adjoint

The local positive transport, global phase extension, amplitude profiles and
supported conic geometry are instantiated together, on nested fixed buffers.
The resulting operator represents the ORIGINAL canonical kernel on the original
Haar and Lebesgue measures. One operator works at every integer Sobolev order.

This proves uniform local existence and regularity in
`app:ch_background:prop:bg-adjoint`. Every operator constant is chosen before
the immersion and initial scalar. Matching the SAME finite real row and its
initialized history and scalar family remains a separate obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow DerivativeKernels ModifiedNormalSymbol PhaseExtension AmplitudeProfiles
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude ProjectedStressFrame CarrierSobolev
open Pseudodifferential

variable {n N : ℕ}

/-- Nesting the complete supported chart also nests all original mask supports.
This is used to make phase agreement hold throughout the smaller working conic
domain, not merely at its nonzero amplitudes (`app:ch_background:eq:bg-Psi`). -/
theorem supportedChart_mono (z₀ : Euclidean 3) {a b : ℝ} (hab : a ≤ b) :
    supportedChart (n := n) z₀ a ⊆ supportedChart z₀ b := by
  rintro p ⟨hx, hs, hv⟩
  exact ⟨closedBall_subset_closedBall (by linarith) hx,
    closedBall_subset_closedBall (by linarith) hs,
    closedBall_subset_closedBall (by linarith) hv⟩

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct the literal local carrier adjoint from primitive immersion and
initial-scalar data. The minor, flow radius, original masks and frame threshold
precede the varying immersion. All phase, amplitude, normal and flow premises
of the scalar-transport endpoint are discharged by their actual producers.
The original scalar norm domain is unchanged and the derivative reserve is
`2*(n+1)+13`, independent of the order, including zero.

One operator represents the literal Haar adjoint and preserves every full raw
Sobolev level in all carrier and initial coordinates. All constants precede the
immersion, its flow and the original initial scalar. The finite real-row
assembly and its common history instantiation remain with the parent.
Consumer: the uniform local estimate in `app:ch_background:prop:bg-adjoint`.
-/
theorem exists_projected_uniform_local_carrierAdjoint (hn : 2 ≤ n)
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M κmet κ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ)
    (Minit : ℝ) :
    ∃ row col : Fin n, ∃ R a b δ : ℝ,
      0 < R ∧ ∃ ha : 0 < a, ∃ hcell : 4*a < 1/2, ∃ hb : 0 < b,
      0 < δ ∧ ∃ χy : ContDiffBump (0 : CarrierVariable n), ∃ Cbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K (2*(n+1)+13) F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        MapsTo (fun p : Euclidean n × CarrierParameter ↦
          (p.2, CanonicalCarrier.transportPosition T Q p))
          (supportedChart z₀ a) (interior {q | χy q = 1}) ∧
        ∃ Φ Y : ℝ × (Euclidean (n-1) × Euclidean 3) → Euclidean (n-1) × Euclidean 3,
          ∀ initial : Euclidean (n-1) × Euclidean 3 → ℝ,
            ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n-1)), z₀) (R/4)) →
            cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8)) (2*(n+1)) initial ≤ Minit →
            let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
            let d := CanonicalCarrier.data T Q F row col Φ Y initial ha hcell
              (CanonicalConic.angularMask z₀ (NormedSpace.normalize ηb) ha hb)
              FixedCutoffs.highFrequency
            ∃ A : ComplexOutputL2 n →L[ℂ] CarrierL2 n,
              (∀ v, A v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v) ∧
              ∀ s : ℕ, ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
                  MemRawSobolev s (A (PeriodicSobolevSpace.toL2 s v)) ∧
                  rawSobolevNorm s (A (PeriodicSobolevSpace.toL2 s v)) ≤
                    Cbound s * (‖v‖ +
                      (1 + cNorm K (s+2*(n+1)+13) F +
                        cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8))
                          (s+2*(n+1)+13) initial) * ‖PeriodicSobolevSpace.toL2 s v‖) := by
  have hzCube : z₀ ∈ parameterCube P.radius := fun i ↦ (hz₀ i).le
  obtain ⟨row, col, ρ, R, η, τ, g, Aflow, Hflow, hρ, hR, hη, hτ, _hg,
    hAflow, hHflow, hbuffer, hτR, hactual⟩ :=
    exists_projected_local_positive_amplitude (N := N) hn hP T hK hKU hball M
      hκmet hκ z₀ hzCube
  obtain ⟨capAmp, hcapAmp, hamp⟩ := exists_canonical_amplitude_profiles T hP hK hKU
    hball z₀ hzCube hρ hR hτ hτR hbuffer Aflow Hflow hAflow hHflow hM hκmet hκ Minit
  obtain ⟨r₀, hr₀, hbox⟩ := ActualComparison.exists_box_radius T hP hz₀
  obtain ⟨aPhase, χPhase, δPhase, haPhase, _haPhaseR, _haPhaseCap, _hphys,
    _hχ, _hχrange, _hχcompact, _hχsupport, _hχone, hδPhase, hphaseProfiles⟩ :=
    exists_projected_supported_phase_inputs T (N := N) hP z₀ hr₀ hcapAmp
      (hbox r₀ hr₀ le_rfl).2.2 hK hKU hball M hκmet hκ
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨r, hr, a, ha, hacap, _har, _haR, hphysical, hcell, hcarrier,
    rMask, hrMask, _hrr, aMask, haMask, haa, _harMask, δNormal, hδNormal,
    Bnormal, _hBnormal, cJ, _hcJ, hnormalInputs⟩ :=
    NormalInputs.exists_projected_normalInputs T hP hz₀ hk hinc hd hK hKU hball
      hM hκmet hκ (lt_min haPhase hcapAmp)
  have haPhase' : a < aPhase := by linarith [hacap.trans_le (min_le_left ..)]
  have haAmp : aMask < capAmp := by
    linarith [hacap.trans_le (min_le_right ..)]
  have hcellMask : 4*aMask < 1/2 := by linarith
  let b := CanonicalConic.angularWidth ηb rMask
  have hb : 0 < b := (CanonicalConic.angularWidth_spec hηb hrMask).1
  obtain ⟨χy, hχy⟩ := exists_projected_initialCutoff T hP ha
    (by linarith : a ≤ r) hphysical hcarrier hK hKU hball M hκmet hκ
  have hboxMask : closedBall (0 : Euclidean n) (4*aMask) ⊆
      DifferentialChart.chartBox (4*aMask) := by
    intro x hx j
    exact (PiLp.norm_apply_le x j).trans (mem_closedBall_zero_iff.mp hx)
  choose B₀ D₀ hB₀ hD₀ hphase using fun s ↦ hphaseProfiles s
  choose C₀ A₀ F₀ W P₀ N₀ hC₀ hA₀ hF₀ hW hP₀ hN₀ hAmplitude using
    fun s ↦ hamp haMask haAmp hcellMask (NormedSpace.normalize ηb) hb s
  choose Cbound hCbound hbound using fun s ↦
    UniformEndpoint.exists_uniform_scalarTransportCarrierAdjoint_periodic_raw_bound
      (N := N) (FixedCutoffs.physical haMask 1)
      (FixedCutoffs.closedBall_four_subset_cell hcellMask) hcellMask hboxMask
      (fun x hx ↦ FixedCutoffs.physical_eq_zero_outside_four haMask 1 hx)
      1 Bnormal (cJ / ‖ηb‖) (NormalInputs.normalSupport T z₀ ηb rMask aMask)
      (closedBall (0 : Euclidean n) (4*aMask))
      (CanonicalConic.carrierSupport z₀ (r := aMask))
      (CanonicalConic.closedDirections ηb rMask)
      (isCompact_closedBall _ _) (CanonicalConic.carrierSupport_compact z₀)
      (CanonicalConic.closedDirections_compact ηb rMask) (by omega)
      (fun _ h ↦ mem_sphere_zero_iff_norm.mp h.1)
      (W s) (P₀ s) (N₀ s) (A₀ s) (B₀ s) (F₀ s) (C₀ s) (D₀ s)
      (hW s) (hC₀ s) (hP₀ s) (hN₀ s) (hA₀ s) (hB₀ s) (hF₀ s) (hD₀ s) s
  refine ⟨row, col, R, aMask, b, min η (min δPhase δNormal), hR, haMask,
    hcellMask, hb, lt_min hη (lt_min hδPhase hδNormal), χy, Cbound, hCbound, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  have hF4 : cNorm K 4 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  obtain ⟨hlow, Dflow, Φ, Y, hDflow, hsmall, hbig, hgeom, _hΦlocal, _hYlocal,
    hΦD, hYD, hinit, hYΦ, hinv, hcarrier, hYcarrier, hode, hnull, hcoeff,
    hflow, hreg, hΦ, hY, _hbuffer', _hτR', _hdenom, hscalar⟩ :=
    hactual F hF hi hrank hF4 hmet hnormal (hclose.trans_le (min_le_left ..))
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hsmallNorm : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q.1 - fun _ ↦ cubeStress n) ≤ cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) :=
    cNorm_mono_set_of_contDiffAt hball hK (fun x hx ↦
      ((Q.2.1.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp))
  obtain ⟨hα, hαnormal, _⟩ := hscalar (fun _ ↦ 1) contDiffOn_const (by intro p hp; norm_num)
  obtain ⟨_hn', hg, _hX, _hZ, _hΩ, _hΩunit, hrAmplitude, he, hei, hdom, hf,
    hD, hΨ, hinj, hInv, hphaseNormal, hJ, _hJdomain, hclosed, himage, _⟩ :=
    hnormalInputs F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM) hmet hnormal hlow
      (hsmallNorm.trans_lt (hclose.trans_le ((min_le_right ..).trans (min_le_right ..))))
  refine ⟨hlow, (hχy F hF hi hrank hF4 hmet hnormal hlow).mono_left
    (supportedChart_mono z₀ haa.le), Φ, Y, ?_⟩
  intro initial hinitial hIlow
  dsimp only
  let d₀ := CanonicalCarrier.data T Q F row col Φ Y initial haMask hcellMask
    (CanonicalConic.angularMask z₀ (NormedSpace.normalize ηb) haMask hb) FixedCutoffs.highFrequency
  have horder (s : ℕ) : ∃ A : ComplexOutputL2 n →L[ℂ] CarrierL2 n,
        (∀ v, A v =ᵐ[carrierMeasure n] carrierAdjointIntegral d₀ v) ∧
        ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A (PeriodicSobolevSpace.toL2 s v)) ∧
          rawSobolevNorm s (A (PeriodicSobolevSpace.toL2 s v)) ≤
            Cbound s * (‖v‖ + (1 + cNorm K (s+2*(n+1)+13) F +
              cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8))
                (s+2*(n+1)+13) initial) * ‖PeriodicSobolevSpace.toL2 s v‖) := by
    obtain ⟨hYext, _hcompact, hagree, _hgap, hΦext, hgraph, hL, hV,
      hphaseL, hphaseV, _hformulas, hgraphProfile, hfieldProfile⟩ :=
      hphase s F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM) hmet hnormal hlow
        (hsmallNorm.trans_lt (hclose.trans_le ((min_le_right ..).trans (min_le_left ..))))
    let Yext := affineExtension (frozenSpatialReference T (z₀ 0, spectatorCenter z₀))
      χPhase (CanonicalCarrier.transportPosition T Q)
    have hagreeA : EqOn Yext (CanonicalCarrier.transportPosition T Q) (supportedChart z₀ a) :=
      fun p hp ↦ (hagree p (supportedChart_mono z₀ haPhase'.le hp)).eq_of_nhds
    have hagreeMask : EqOn Yext (CanonicalCarrier.transportPosition T Q)
        (supportedChart z₀ aMask) := hagreeA.mono (supportedChart_mono z₀ haa.le)
    obtain ⟨hkernel, hH, hscalarSmooth, _hflowReal, hflowSmooth, _hν,
      hgeometry, hmask, hAmplitudeSmooth, hsupp, hgeomProfile, hscalarProfile,
      hflowProfile, hfrequency⟩ :=
      hAmplitude s Q F row col Dflow Φ Y initial rfl hF hi hrank hFM hmet hnormal
        hDflow hsmall hbig hgeom hΦD hYD hinit hYΦ hinv hcarrier hYcarrier hode hnull
        hcoeff hflow hreg hΦ hY hα hαnormal hinitial hIlow Yext hYext hagreeMask
    let rInitial := extendedInitialScalar z₀ hR initial
    let flow := extendedFlowFactor T Q F row col Φ Y z₀ haMask
    let ν := extendedGeometricNormal T Q F col z₀ haMask
    let d := scalarTransportData d₀ Yext rInitial flow ν
    let H := 1 + cNorm K (s+2*(n+1)+13) F +
      cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8)) (s+2*(n+1)+13) initial
    have hhigh : 1 + cNorm K (s+2*(n+1)+5) F ≤ H := by
      have hh := cNorm_mono_order (s := K) (f := F)
        (by omega : s+2*(n+1)+5 ≤ s+2*(n+1)+13)
      dsimp [H]
      linarith [cNorm_nonneg (closedBall ((0 : Euclidean (n-1)), z₀) (R/8))
        (s+2*(n+1)+13) initial]
    have hbound' := hbound s d rfl (fun _ _ ↦ rfl)
      (fun x _ ↦ FixedCutoffs.periodic_apply haMask hcellMask 1 x)
      ν rInitial flow (fun z x ↦ scalarTransportData_normalField d₀ Yext rInitial flow ν x z)
      hgeometry hmask hscalarSmooth hflowSmooth hgraph hΦext
      _ _ hg (fun j ↦ hrAmplitude _ (hAmplitudeSmooth j)) hsupp
      (initialField Yext) (carrierField Yext) hL hV he hei hdom hf hD hΨ hinj hInv
      (hphaseNormal Yext hagreeA) hJ hclosed himage
      (fun z x η h _ ↦ hphaseL z x η h) (fun z x η h _ ↦ hphaseV z x η h)
    obtain ⟨hUopen, hunit, hangular⟩ := adjointAngularGraph_neighborhood (n := n)
    obtain ⟨A, hrep, hraw⟩ := hbound' H hH {0}ᶜ hUopen hunit hangular
      (fun R' _ p _ ↦ (scaled_halfOrderRadialFactor_contDiff R').contDiffAt)
      (fun R' hR' p hp i _ ↦ (hfrequency R' hR' p hp).1 i)
      hgeomProfile (fun R' hR' p hp i _ ↦ (hfrequency R' hR' p hp).2.1 i)
      (fun R' hR' p hp i hi _ ↦ (hfrequency R' hR' p hp).2.2 i hi)
      hscalarProfile
      (fun p i hi hi' ↦ (hgraphProfile p i hi hi').trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith [cNorm_nonneg K (s+2*(n+1)+5) F])
            hhigh (by positivity)) (hB₀ s i)))
      hflowProfile
      (fun ds hds p _ e he j i hi ↦ (hfieldProfile ds hds p e he j i hi).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith [cNorm_nonneg K (s+2*(n+1)+5) F])
            hhigh (by positivity)) (hD₀ s ds i)))
    refine ⟨A, ?_, hraw⟩
    intro v
    exact (hrep v).trans (Filter.Eventually.of_forall fun u ↦
      congrFun (congrFun (carrierAdjointIntegral_congr_kernel hkernel) v) u)
  obtain ⟨A, hrep, _⟩ := horder 0
  refine ⟨A, hrep, ?_⟩
  intro s
  obtain ⟨As, hAs, hb⟩ := horder s
  have heq := literalCarrierAdjointOperator_unique d₀ As A hAs hrep
  simpa only [heq] using hb

/-- The original local-existence interface follows from the uniform construction.
One literal adjoint works at every order, with the original scalar domain and
fixed reserve (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_projected_local_carrierAdjoint (hn : 2 ≤ n)
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M κmet κ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ)
    (Minit : ℝ) :
    ∃ row col : Fin n, ∃ R a b δ : ℝ,
      0 < R ∧ ∃ ha : 0 < a, ∃ hcell : 4*a < 1/2, ∃ hb : 0 < b,
      0 < δ ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K (2*(n+1)+13) F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∃ Φ Y : ℝ × (Euclidean (n-1) × Euclidean 3) → Euclidean (n-1) × Euclidean 3,
          ∀ initial : Euclidean (n-1) × Euclidean 3 → ℝ,
            ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n-1)), z₀) (R/4)) →
            cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8)) (2*(n+1)) initial ≤ Minit →
            let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
            let d := CanonicalCarrier.data T Q F row col Φ Y initial ha hcell
              (CanonicalConic.angularMask z₀ (NormedSpace.normalize ηb) ha hb)
              FixedCutoffs.highFrequency
            ∃ A : ComplexOutputL2 n →L[ℂ] CarrierL2 n,
              (∀ v, A v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v) ∧
              ∀ s : ℕ, ∃ C ≥ (0 : ℝ),
                ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
                  MemRawSobolev s (A (PeriodicSobolevSpace.toL2 s v)) ∧
                  rawSobolevNorm s (A (PeriodicSobolevSpace.toL2 s v)) ≤
                    C * (‖v‖ +
                      (1 + cNorm K (s+2*(n+1)+13) F +
                        cNorm (closedBall ((0 : Euclidean (n-1)), z₀) (R/8))
                          (s+2*(n+1)+13) initial) * ‖PeriodicSobolevSpace.toL2 s v‖) := by
  obtain ⟨row, col, R, a, b, δ, hR, ha, hcell, hb, hδ, _χy, Cbound, hCbound, hactual⟩ :=
    exists_projected_uniform_local_carrierAdjoint T hn hP hz₀ hk hinc hd hK hKU hball
      hM hκmet hκ Minit
  refine ⟨row, col, R, a, b, δ, hR, ha, hcell, hb, hδ, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, _hχy, Φ, Y, hscalar⟩ := hactual F hF hi hrank hFM hmet hnormal hclose
  refine ⟨hlow, Φ, Y, ?_⟩
  intro initial hinitial hIlow
  obtain ⟨A, hrep, hraw⟩ := hscalar initial hinitial hIlow
  exact ⟨A, hrep, fun s ↦ ⟨Cbound s, hCbound s, hraw s⟩⟩

end JanetCartan.ContinuumAdjoint.Canonical
