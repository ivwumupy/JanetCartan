module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedCellAdjoint.Profiles
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedLeading.PhaseInputs
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.LocalAdjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Support

/-!
# Generic-current raw adjoints on prescribed masks

Choose only the extra physical cap for the full-normal and phase profiles.
The original incidence selector imposes this cap before choosing its masks.
The raw estimate then applies to the supplied normal chart and literal carrier
adjoint. No second incidence or mask selection occurs.

The geometric premises below are the conclusions of the supplied normal-chart
application of `NormalInputs.exists_projected_normalChart_primitiveJetGeometry`
and its support and phase lemmas. Their actual use on the selected row remains
part of the common construction. The full-leading bounds are supplied by its
original retained leading-history continuation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse
open ContinuumAdjoint ContinuumRow
open ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.RetainedCellAdjoint
open ContinuumRow DerivativeKernels ModifiedNormalSymbol PhaseExtension AmplitudeProfiles
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude ProjectedStressFrame CarrierSobolev
open LeadingPrimitive LeadingWave.FullModulation Pseudodifferential RetainedLeading
open ContinuumRow.TransportKernel AmplitudeBound CanonicalCarrier CanonicalConic

private theorem raw_unit_profile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E) (i : ℕ) {H : ℝ} (hH : 1 ≤ H) (e : ℝ) (he : 0 ≤ e) :
    ‖iteratedFDeriv ℝ i (fun _ : E ↦ (1 : ℂ)) p‖ ≤ 1 * H ^ e := by
  have hb : 1 ≤ H ^ e := Real.one_le_rpow hH he
  cases i with
  | zero => simpa using hb
  | succ i =>
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, one_mul]
    exact Real.rpow_nonneg (zero_le_one.trans hH) _

/-- A cap for the actual generic-current raw adjoint on every subsequently
supplied mask. The full-normal and phase profiles are constructed from the
original leading estimates and fixed immersion budget. The remaining normal
chart fields are the explicit output of the supplied conic geometry producer.
The estimate has one high norm at shift `2*(n+1)+14`, and applies by literal
adjoint uniqueness to the already supplied carrier operator
(`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-derivative-trade`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_generic_current_rawAdjoint_cap {n N : ℕ} (hn : 0 < n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3))
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hJ : IsCompact J)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hgraph : MapsTo (carrierGraph T) E J)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (hcenter : chartCenter z₀ ∈ E) :
    ∃ aCap > (0 : ℝ), ∃ aPhase > (0 : ℝ), aCap < aPhase ∧ ∃ δ > (0 : ℝ),
    ∀ {aMask : ℝ} (haMask : 0 < aMask) (hcellMask : 4 * aMask < 1 / 2), aMask ≤ aCap →
    ∀ {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0) {rMask : ℝ} (hrMask : 0 < rMask),
    ∀ (Bfull : ℕ → ℝ), (∀ j, 0 < Bfull j) →
    ∀ {MF Mr κmet κ : ℝ}, 0 ≤ MF → 0 ≤ Mr → 0 < κmet → 0 < κ →
    ∀ Bnormal cJet : ℝ,
    ∃ Cbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧
    ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
      (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K (2 * (n + 1) + 14) F ≤ MF →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    ∀ (row col : Fin n)
      (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
      (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
      (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
      (Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T → J ⊆ O →
      MapsTo (carrierGraph T) E O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) E Vcomp →
      ContDiffOn ℝ ∞
        (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) O →
      (∀ q ∈ Vcomp,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T Q F row col φ y initial w) →
      cNorm Kinitial (2 * (n + 1) + 14) initial ≤ Mr →
      (∀ j, cNorm J j (fullNormal T Q F row col Φ Y initial) ≤
        Bfull j * (1 + cNorm K (j + 14) F + cNorm Kinitial (j + 14) initial)) →
    let X := closedBall (0 : Euclidean n) (4 * aMask)
    let Z := carrierSupport z₀ (r := aMask)
    let Ω := closedDirections ηb rMask
    let Jnormal := NormalInputs.normalSupport T z₀ ηb rMask aMask
    ∀ (g : ModifiedNormalSymbol.Chart n) (σJet : JetRescaling g),
      PrimitiveJetGeometry g σJet (2 * (n + 1)) 1 Bnormal cJet Jnormal (Prod.snd '' Z) →
      (∀ amplitude : AdjointAmplitude n,
        ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦ amplitude p.1 p.2.1 p.2.2) →
        PrimitiveRegularity g amplitude (fun _ ↦ 1)) →
      MeasurePreserving g.coordinates volume (volume.prod volume) →
      Continuous g.coordinates.symm →
      (∀ x y v w,
        ((chartCarrierVariable g.coordinates v w).1, x,
          (chartCarrierVariable g.coordinates v w).2) ∈ adjointConicBuffer X Z Ω 1 →
        ((chartCarrierVariable g.coordinates v w).1, y,
          (chartCarrierVariable g.coordinates v w).2) ∈ adjointConicBuffer X Z Ω 1 →
        w ∈ g.domain x y v) →
      ContinuousOn g.push g.inputDomain →
      (∀ x y v, MeasurableSet (g.domain x y v)) →
      (∀ x y v w, w ∈ g.domain x y v →
        HasFDerivWithinAt (g.forward x y v) (g.jacobian x y v w) (g.domain x y v) w) →
      (∀ x y v, InjOn (g.forward x y v) (g.domain x y v)) →
      (∀ x y v w, w ∈ g.domain x y v → g.inverse x y v (g.forward x y v w) = w) →
      (∀ Yext : Euclidean n × CarrierParameter → Euclidean (n - 1),
        EqOn Yext (transportPosition T Q) (supportedChart z₀ aPhase) →
        ∀ x y v w, w ∈ g.domain x y v →
          phase Yext (chartCarrierVariable g.coordinates v w).1 x
              (chartCarrierVariable g.coordinates v w).2 -
            phase Yext (chartCarrierVariable g.coordinates v w).1 y
              (chartCarrierVariable g.coordinates v w).2 =
            inner ℝ (x - y) (g.forward x y v w)) →
      (∀ p ∈ g.inputDomain,
        ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω 1 →
        ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω 1 →
        p ∈ Jnormal) →
      IsClosed (g.push '' Jnormal) → g.push '' Jnormal ⊆ g.outputDomain →
    let d := data T Q F row col φ y initial haMask hcellMask
      (angularMask z₀ (NormedSpace.normalize ηb) haMask (angularWidth_spec hηb hrMask).1)
      FixedCutoffs.highFrequency
    ∀ Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ w, Vop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) →
      ∀ s : ℕ, ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
        MemRawSobolev s (Vop.adjoint (PeriodicSobolevSpace.toL2 s v)) ∧
        rawSobolevNorm s (Vop.adjoint (PeriodicSobolevSpace.toL2 s v)) ≤
          Cbound s * (‖v‖ + (1 + cNorm K (s + 2 * (n + 1) + 14) F +
            cNorm Kinitial (s + 2 * (n + 1) + 14) initial) *
              ‖PeriodicSobolevSpace.toL2 s v‖) := by
  obtain ⟨capNormal, hcapNormal, hprofiles⟩ := exists_retained_cell_normal_profiles T (N := N)
    hP hK hKU hball Kinitial hJ E hE hgraph z₀ (fun i ↦ (hz₀ i).le) hcenter
  obtain ⟨r₀, hr₀, hbox⟩ := ActualComparison.exists_box_radius T hP hz₀
  obtain ⟨aPhase, χPhase, δPhase, haPhase, _haPhaseR, _haPhaseCap, _hphys,
    _hχ, _hχrange, _hχcompact, _hχsupport, _hχone, hδPhase, hphaseProfiles⟩ :=
    exists_projected_supported_phase_inputs_before_budgets T (N := N) hP z₀ hr₀ zero_lt_one
      (hbox r₀ hr₀ le_rfl).2.2 hK hKU hball
  let aCap := min (capNormal / 2) (aPhase / 2)
  have haCap : 0 < aCap := lt_min (half_pos hcapNormal) (half_pos haPhase)
  have hcapPhase : aCap < aPhase := (min_le_right _ _).trans_lt (half_lt_self haPhase)
  refine ⟨aCap, haCap, aPhase, haPhase, hcapPhase, δPhase, hδPhase, ?_⟩
  intro aMask haMask hcellMask hmaskCap ηb hηb rMask hrMask Bfull hBfull
    MF Mr κmet κ hMF hMr hκmet hκ Bnormal cJet
  have haNormal : aMask < capNormal :=
    hmaskCap.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hcapNormal))
  have haMaskPhase : aMask < aPhase := hmaskCap.trans_lt hcapPhase
  let b := angularWidth ηb rMask
  have hb : 0 < b := (angularWidth_spec hηb hrMask).1
  choose B₀ D₀ hB₀ hD₀ hphaseProfiles using fun s ↦ hphaseProfiles MF hκmet hκ s
  choose C₀ hC₀ hnormalProfile using fun s ↦
    hprofiles haMask haNormal Bfull hBfull hMF hMr hκmet hκ s
  obtain ⟨W, hW, hw⟩ := exists_fixed_halfOrderRadialFactor_jet_bounds (n := n)
  obtain ⟨P₀, N₀, hP₀, hN₀, hpn⟩ := exists_fixed_angular_reserve_profiles z₀
    (NormedSpace.normalize ηb) haMask hb
  have hboxMask : closedBall (0 : Euclidean n) (4 * aMask) ⊆
      DifferentialChart.chartBox (4 * aMask) := by
    intro x hx j
    exact (PiLp.norm_apply_le x j).trans (mem_closedBall_zero_iff.mp hx)
  choose Cbound hCbound hbound using fun s ↦
    UniformEndpoint.exists_uniform_scalarTransportCarrierAdjoint_periodic_raw_bound
      (N := N) (FixedCutoffs.physical haMask 1)
      (FixedCutoffs.closedBall_four_subset_cell hcellMask) hcellMask hboxMask
      (fun x hx ↦ FixedCutoffs.physical_eq_zero_outside_four haMask 1 hx)
      1 Bnormal cJet (NormalInputs.normalSupport T z₀ ηb rMask aMask)
      (closedBall (0 : Euclidean n) (4 * aMask)) (carrierSupport z₀ (r := aMask))
      (closedDirections ηb rMask) (isCompact_closedBall _ _) (carrierSupport_compact z₀)
      (closedDirections_compact ηb rMask) hn (NormalInputs.normalSupport_directions_unit ηb rMask)
      W P₀ N₀ (fun _ ↦ 1) (B₀ s) (fun _ ↦ 1) (C₀ s) (D₀ s)
      hW (hC₀ s) hP₀ hN₀ (fun _ ↦ zero_le_one) (hB₀ s) (fun _ ↦ zero_le_one) (hD₀ s) s
  refine ⟨Cbound, hCbound, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose Q row col φ y Φ Y initial O Vcomp
    hO hOU hOdom hJO hgraphO hcompE hnull hcomp hIM hfull
    X Z Ω Jnormal g σJet hg hrAmplitude he hei hdom hf hD hΨ hinj hInv
    hphaseNormal hJnormal hclosed himage d₀ Vop hVop s
  have hsmall : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < δPhase :=
    (cNorm_mono_set_of_contDiffAt hball hK (fun x hx ↦
      (((contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)).contDiffAt
        (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp))).trans_lt hclose
  obtain ⟨_hYext, _hcompact, hagree, _hgap, hΦext, hgraphExt, hL, hV,
    hphaseL, hphaseV, _hformulas, hgraphProfile, hfieldProfile⟩ :=
    hphaseProfiles s F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM)
      hmet hnormal hlow hsmall
  let Yext := affineExtension (frozenSpatialReference T (z₀ 0, spectatorCenter z₀))
    χPhase (transportPosition T Q)
  have hagreeA : EqOn Yext (transportPosition T Q) (supportedChart z₀ aPhase) :=
    fun p hp ↦ (hagree p hp).eq_of_nhds
  have hagreeMask := hagreeA.mono (supportedChart_mono z₀ haMaskPhase.le)
  let ν := extendedRetainedNormal T Q F row col φ y initial z₀ haMask
  let d := scalarTransportData d₀ Yext (fun _ ↦ 1) (fun _ ↦ 1) ν
  let H := 1 + cNorm K (s + 2 * (n + 1) + 14) F +
    cNorm Kinitial (s + 2 * (n + 1) + 14) initial
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg K (s + 2 * (n + 1) + 14) F,
      cNorm_nonneg Kinitial (s + 2 * (n + 1) + 14) initial]
  have hhigh : 1 + cNorm K (s + 2 * (n + 1) + 5) F ≤ H := by
    have hh := cNorm_mono_order (s := K) (f := F)
      (by omega : s + 2 * (n + 1) + 5 ≤ s + 2 * (n + 1) + 14)
    dsimp [H]
    linarith [cNorm_nonneg Kinitial (s + 2 * (n + 1) + 14) initial]
  obtain ⟨_hνglobal, hcomponent⟩ :=
    hnormalProfile s Q F row col φ y Φ Y initial O Vcomp rfl hF hi hrank hFM hIM hmet hnormal
      hO hOU hOdom hJO hgraphO hcompE hnull hcomp hfull
  obtain ⟨hcglobal, hcprofile⟩ := hcomponent hcellMask
    (angularMask z₀ (NormedSpace.normalize ηb) haMask hb) FixedCutoffs.highFrequency
  have hm : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)) :=
    angularMask_complex_contDiff z₀ (NormedSpace.normalize ηb) haMask hb
  have hcg (j) : ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical haMask 1) ν j) :=
    hcglobal j
  have hsmooth j : ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦
      frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
        (carrierChartNormalizedComponent d (FixedCutoffs.physical haMask 1) j) p.1 p.2.1 p.2.2) :=
    frequencyScale_carrierChartNormalizedComponent_contDiff d (FixedCutoffs.physical haMask 1)
      ν (fun _ ↦ 1) (fun _ ↦ 1)
      (fun z x ↦ scalarTransportData_normalField d₀ Yext _ _ ν x z) rfl j (hcg j) hm
      contDiff_const contDiff_const hgraphExt
  have hsupp j z x η hne := frequencyScale_carrierChartNormalizedComponent_support d z₀
    (NormedSpace.normalize ηb) haMask hb rfl rfl j z x η hne
  have hbound' := hbound s d rfl (fun _ _ ↦ rfl)
    (fun x _ ↦ FixedCutoffs.periodic_apply haMask hcellMask 1 x)
    ν (fun _ ↦ 1) (fun _ ↦ 1)
    (fun z x ↦ scalarTransportData_normalField d₀ Yext _ _ ν x z)
    hcg hm contDiff_const contDiff_const hgraphExt hΦext g σJet hg
    (fun j ↦ hrAmplitude _ (hsmooth j)) hsupp
    (initialField Yext) (carrierField Yext) hL hV he hei hdom hf hD hΨ hinj hInv
    (hphaseNormal Yext hagreeA) hJnormal hclosed himage
    (fun z x η h _ ↦ hphaseL z x η h) (fun z x η h _ ↦ hphaseV z x η h)
  obtain ⟨hUopen, hunit, hangular⟩ := adjointAngularGraph_neighborhood (n := n)
  obtain ⟨A, hrep, hraw⟩ := hbound' H hH {0}ᶜ hUopen hunit hangular
    (fun R' _ p _ ↦ (scaled_halfOrderRadialFactor_contDiff R').contDiffAt)
    (fun R' hR' p hp i _ ↦ hw R' hR' p hp i)
    (hcprofile H le_rfl)
    (fun R' hR' p hp i _ ↦ (hpn H hH s R' hR' p hp).1 i)
    (fun R' hR' p hp i hi _ ↦ (hpn H hH s R' hR' p hp).2 i hi)
    (fun _ i _ ↦ raw_unit_profile _ i hH _ (by positivity))
    (fun p i hi hi' ↦ (hgraphProfile p i hi hi').trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith [cNorm_nonneg K (s + 2 * (n + 1) + 5) F])
          hhigh (by positivity)) (hB₀ s i)))
    (fun p i _ ↦ raw_unit_profile p i hH _ (by positivity))
    (fun ds hds p _ e he j i hi ↦ (hfieldProfile ds hds p e he j i hi).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith [cNorm_nonneg K (s + 2 * (n + 1) + 5) F])
          hhigh (by positivity)) (hD₀ s ds i)))
  have hkernel := carrierKernel_extendedRetainedNormal_eq T Q F row col φ y initial z₀
    haMask hcellMask (NormedSpace.normalize ηb) hb FixedCutoffs.highFrequency Yext hagreeMask
  have hArep (v) : A v =ᵐ[carrierMeasure n] carrierAdjointIntegral d₀ v :=
    (hrep v).trans (Filter.Eventually.of_forall fun u ↦
      congrFun (congrFun (carrierAdjointIntegral_congr_kernel hkernel) v) u)
  have heq := literalCarrierAdjointOperator_unique d₀ A Vop.adjoint hArep hVop
  simpa only [heq] using hraw

end JanetCartan.ContinuumInverse
