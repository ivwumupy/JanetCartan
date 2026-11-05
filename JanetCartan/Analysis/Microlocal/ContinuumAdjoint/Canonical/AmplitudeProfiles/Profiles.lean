module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Buffers
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Flow
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.InitialScalar
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Frequency
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.KernelAgreement

/-!
# Actual amplitude inputs with one common primitive high norm

The fixed cap and all profiles precede the varying immersion, initial scalar
and flow. The hypotheses about coefficients, domain maps, flow identities and
local unit-initial regularity are retained outputs of
`NullTransport.exists_projected_local_positive_amplitude`. The globally smooth
phase extension and its supported agreement come from
`PhaseExtension.exists_projected_supported_phase_inputs`.

No amplitude profile is assumed. The common high budget uses one immersion
norm and one ORIGINAL initial-scalar norm, on its unchanged `R/8` ball. The
reserve `2*(n+1)+13` is independent of the requested derivative order, including
order zero. The literal canonical kernel, masks and half-order factor survive
unchanged. Consumer: the amplitude inputs of
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`,
`app:ch_waves:eq:joint-tame`). Finite-family selection and application of that
operator endpoint belong to the canonical adjoint assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow PhaseExtension ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport ActualFlow FlowAmplitude LeadingWave AmbientResponse ProjectedStressFrame
open DerivativeKernels ModifiedNormalSymbol

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct all six amplitude profiles for the exact supported replacement
of the canonical carrier. Every additional analytic premise is an explicit
retained local-flow output or the already constructed phase extension. The
geometric and footpoint containments are proved here from fixed primitive data;
the original scalar norm domain is retained. This supplies the amplitude part
of `bg-adjoint`, with a single primitive high budget and no assumed operator
estimate (`app:ch_background:eq:bg-T`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_canonical_amplitude_profiles {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius)
    {ρ R τ : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hτ : 0 < τ) (hτR : τ ≤ R / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z₀)) R)
      (closedBall ((0 : Euclidean n), z₀) ρ))
    (A Hflow : ℕ → ℝ) (hA : ∀ i, 0 < A i) (hHflow : ∀ i, 0 < Hflow i)
    {M κmet κ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ) (Minit : ℝ) :
    ∃ cap > (0 : ℝ), ∀ {a : ℝ} (ha : 0 < a), a < cap →
      ∀ (hcell : 4 * a < 1 / 2) (θ₀ : Euclidean (n-1)) {b : ℝ} (hb : 0 < b) (s : ℕ),
      ∃ (C₀ : Fin n → ℕ → ℝ) (A₀ F₀ W P₀ N₀ : ℕ → ℝ),
        (∀ j i, 0 ≤ C₀ j i) ∧ (∀ i, 0 ≤ A₀ i) ∧ (∀ i, 0 ≤ F₀ i) ∧
        (∀ i, 0 ≤ W i) ∧ (∀ i, 0 ≤ P₀ i) ∧ (∀ i, 0 ≤ N₀ i) ∧
        ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold})
          (F : Euclidean n → Euclidean N) (row col : Fin n)
          (D : Set (ℝ × (Euclidean (n-1) × Euclidean 3)))
          (Φ Y : ℝ × (Euclidean (n-1) × Euclidean 3) → Euclidean (n-1) × Euclidean 3)
          (initial : Euclidean (n-1) × Euclidean 3 → ℝ),
        let p₀ := ((0 : Euclidean (n-1)), z₀)
        let Bρ := closedBall ((0 : Euclidean n), z₀) ρ
        let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
        let L := ball p₀ (R/8)
        let J := Icc (-τ) τ ×ˢ closedBall p₀ (R/8)
        let α := carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1)
        Q.1 = projectedStress F → ContDiffOn ℝ ∞ F U → IsImmersionOn F U →
        HasFullNormalRankOn F U → cNorm K (2*(n+1)+13) F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        IsOpen D → Ioo (-τ) τ ×ˢ ball p₀ (R/32) ⊆ D →
        D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R/4) →
        C ⁻¹' D ⊆ (ball 0 T.physicalRadius ∩ interior K) ×ˢ
          parameterInterior (3 * P.radius / 2) →
        MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ L) D →
        MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ L) →
        (∀ p ∈ L, Φ (0,p) = p) →
        (∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, Y (t, Φ (t,p)) = p) →
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) →
        (∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, (Φ (t,p)).2 = p.2) →
        (∀ q ∈ D, (Y q).2 = q.2.2) →
        (∀ p ∈ L, ∀ t ∈ Ioo (-τ) τ, HasDerivAt (fun u ↦ Φ (u,p))
          ((adaptedCoordinates T.data.adapted
            (carrierTransportDirection T Q row col (C.symm (t, Φ (t,p))))).2, 0) t) →
        (∀ w ∈ C ⁻¹' D,
          carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
          carrierConullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
          carrierAdaptedDenominator T Q row col w ≠ 0) →
        (∀ i, cNorm Bρ i (carrierNullvector T Q col) +
          cNorm Bρ i (carrierConullvector T Q row) +
          cNorm Bρ i (carrierAdaptedDenominator T Q row col) +
          cNorm Bρ i (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹) +
          cNorm Bρ i (carrierTransportDirection T Q row col) +
          cNorm Bρ i (carrierTransportPotential T Q F row col) ≤
            A i * (1 + cNorm K (i+5) F)) →
        (∀ i, cNorm J i Φ + cNorm J i Y ≤ Hflow i * (1 + cNorm K (i+5) F)) →
        (∀ w ∈ Bρ, ContDiffAt ℝ ∞ (carrierNullvector T Q col) w ∧
          ContDiffAt ℝ ∞ (carrierTransportDirection T Q row col) w ∧
          ContDiffAt ℝ ∞ (carrierTransportPotential T Q F row col) w) →
        ContDiffOn ℝ ∞ Φ (Ioo (-(2*τ)) (2*τ) ×ˢ ball p₀ (R/4)) →
        ContDiffOn ℝ ∞ Y (Ioo (-(2*τ)) (2*τ) ×ˢ ball p₀ (R/4)) →
        ContDiffOn ℝ ∞ α (C ⁻¹' D) →
        ContDiffOn ℝ ∞ (fun w ↦ α w • carrierNullvector T Q col w) (C ⁻¹' D) →
        ContDiffOn ℝ ∞ initial (ball p₀ (R/4)) →
        cNorm (closedBall p₀ (R/8)) (2*(n+1)) initial ≤ Minit →
        ∀ Yext : Euclidean n × CarrierParameter → Euclidean (n-1),
          ContDiff ℝ ∞ Yext →
          EqOn Yext (CanonicalCarrier.transportPosition T Q) (supportedChart z₀ a) →
          let r := extendedInitialScalar z₀ hR initial
          let flow := extendedFlowFactor T Q F row col Φ Y z₀ ha
          let ν := extendedGeometricNormal T Q F col z₀ ha
          let d₀ := CanonicalCarrier.data T Q F row col Φ Y initial ha hcell
            (CanonicalConic.angularMask z₀ θ₀ ha hb) FixedCutoffs.highFrequency
          let d := scalarTransportData d₀ Yext r flow ν
          let H := 1 + cNorm K (s+2*(n+1)+13) F +
            cNorm (closedBall p₀ (R/8)) (s+2*(n+1)+13) initial
          carrierKernel d = carrierKernel d₀ ∧ 1 ≤ H ∧
          ContDiff ℝ ∞ (fun p ↦ (r p : ℂ)) ∧
          ContDiff ℝ ∞ flow ∧ ContDiff ℝ ∞ (fun p ↦ (flow p : ℂ)) ∧
          ContDiff ℝ ∞ ν ∧
          (∀ j, ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j)) ∧
          ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)) ∧
          (∀ j, ContDiff ℝ ∞ (fun p : AmplitudeVariables n ↦
            frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
              (carrierChartNormalizedComponent d (FixedCutoffs.physical ha 1) j)
              p.1 p.2.1 p.2.2)) ∧
          (∀ j z x η, frequencyScaleAmplitude (halfOrderRadialFactor d.highCutoff)
            (carrierChartNormalizedComponent d (FixedCutoffs.physical ha 1) j) z x η ≠ 0 →
            z ∈ CanonicalConic.carrierSupport z₀ (r := a) ∧ x ∈ closedBall 0 (4*a) ∧
            ‖η‖⁻¹ • η ∈ sphere 0 1 ∩ closedBall θ₀ (b/2) ∧ 1 ≤ ‖η‖) ∧
          (∀ j p, ∀ i ≤ s+2*(n+1),
            ‖iteratedFDeriv ℝ i (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j) p‖ ≤
              C₀ j i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) ∧
          (∀ p : AdjointJetPoint n, ∀ i ≤ s+2*(n+1),
            ‖iteratedFDeriv ℝ i (fun p ↦ (r p : ℂ)) (p.1, d.transportedPosition p.2 p.1)‖ ≤
              A₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) ∧
          (∀ p : AdjointJetPoint n, ∀ i ≤ s+2*(n+1),
            ‖iteratedFDeriv ℝ i (fun p ↦ (flow p : ℂ)) p‖ ≤
              F₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) ∧
          (∀ R' : ℝ, 1 ≤ R' → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
            (∀ i, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
              halfOrderRadialFactor d.highCutoff (R' • p.2)) p‖ ≤ W i * Real.sqrt R') ∧
            (∀ i, ‖iteratedFDeriv ℝ i
              (fun v : CarrierVariable n ↦ (d.angularCutoff v.1 v.2 : ℂ))
              (adjointAngularGraph R' p)‖ ≤
                P₀ i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ))) ∧
            (∀ i, 1 ≤ i → ‖iteratedFDeriv ℝ i (adjointAngularGraph R') p‖ ≤
                N₀ i * H ^ (((i-1-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)))) := by
  obtain ⟨ρg, σ, X, V, hρg, hσ, hrestrict, hx, hcρ, hX, hV, hXU,
    hσX, hσV, hσK, hcoef⟩ := exists_amplitude_geometry_buffers T hP hKU hball z₀ hz₀ hρ
  obtain ⟨capK, hcapK, hkernel⟩ := exists_extendedScalarTransportData_kernel_cap T
    (N := N) hP hKU z₀ hτ hR (hHflow 1) M
  obtain ⟨capF, hcapF, hwork⟩ := exists_supportedChart_flowCylinder_cap T z₀
    (half_pos hτ) (half_pos hR)
  refine ⟨min capK (min (capF/24) (σ/12)),
    lt_min hcapK (lt_min (by positivity) (by positivity)), ?_⟩
  intro a ha hacap hcell θ₀ b hb s
  have haK : a < capK := hacap.trans_le (min_le_left ..)
  have haF : 24*a < capF := by
    have hh := hacap.trans_le ((min_le_right ..).trans (min_le_left ..))
    linarith
  have haσ : 12*a ≤ σ := by
    have hh := hacap.trans_le ((min_le_right ..).trans (min_le_right ..))
    linarith
  have hs : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
      (tsupport (chartBump z₀ ha))
      (Icc (-τ/2) (τ/2) ×ˢ closedBall ((0 : Euclidean (n-1)), z₀) (R/64)) := by
    intro p hp
    have hh := hwork (by positivity : 0 < 24*a) haF (chartBump_tsupport_subset z₀ ha hp)
    exact ⟨⟨by linarith [hh.1.1], hh.1.2.le⟩,
      (mem_ball.mp hh.2).le.trans_eq (by ring)⟩
  obtain ⟨C₀, hC₀, hc⟩ := exists_carrierChartGeometryComponent_profiles T (N := N)
    hP hK hKU hball z₀ hρg hσ ha haσ hx hcρ hX hV hXU hσX hσV hσK hcoef
    A hA hM hκmet hκ s
  obtain ⟨F₀, hF₀, hf⟩ := exists_extendedFlowFactor_profile T (N := N) K z₀
    hρ hR hτ ha hτR hbuffer A Hflow hA hHflow hs M s
  obtain ⟨A₀, hA₀, hr⟩ := exists_extendedInitialScalar_profile (n := n) z₀ hR Minit s
  obtain ⟨W, hW, hw⟩ := exists_fixed_halfOrderRadialFactor_jet_bounds (n := n)
  obtain ⟨P₀, N₀, hP₀, hN₀, hpn⟩ := exists_fixed_angular_reserve_profiles z₀ θ₀ ha hb
  refine ⟨C₀, A₀, F₀, W, P₀, N₀, hC₀, hA₀, hF₀, hW, hP₀, hN₀, ?_⟩
  intro Q F row col D Φ Y initial p₀ Bρ C L J α hQ hF hi hrank hFM hmet hnormal
    hD hsmall hbig hgeom hΦD hYD hinit hYΦ hinv hcarrier hYcarrier hode hnull
    hcoeff hflow hreg hΦ hY hα hbreg hinitial hIlow Yext hYext hYagree
  dsimp only
  let r := extendedInitialScalar z₀ hR initial
  let flow := extendedFlowFactor T Q F row col Φ Y z₀ ha
  let ν := extendedGeometricNormal T Q F col z₀ ha
  let d₀ := CanonicalCarrier.data T Q F row col Φ Y initial ha hcell
    (CanonicalConic.angularMask z₀ θ₀ ha hb) FixedCutoffs.highFrequency
  let d := scalarTransportData d₀ Yext r flow ν
  let H := 1 + cNorm K (s+2*(n+1)+13) F +
    cNorm (closedBall p₀ (R/8)) (s+2*(n+1)+13) initial
  have hFM6 : cNorm K 6 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  have hFMg : cNorm K (2*(n+1)+6) F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  have hnullB (i) : cNorm (closedBall ((0 : Euclidean n), z₀) ρg) i
      (carrierNullvector T Q col) ≤ A i * (1 + cNorm K (i+5) F) := by
    apply (cNorm_mono_set_of_contDiffAt hrestrict (isCompact_closedBall _ _)
      (fun w hw ↦ (hreg w hw).1.of_le (by simp : (i : ℕ∞ω) ≤ ∞))).trans
    have hh := hcoeff i
    linarith [cNorm_nonneg Bρ i (carrierConullvector T Q row),
      cNorm_nonneg Bρ i (carrierAdaptedDenominator T Q row col),
      cNorm_nonneg Bρ i (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹),
      cNorm_nonneg Bρ i (carrierTransportDirection T Q row col),
      cNorm_nonneg Bρ i (carrierTransportPotential T Q F row col)]
  obtain ⟨hν, hc'⟩ := hc Q F hQ hF hi hrank hFMg hmet hnormal col
    (fun w hw ↦ (hreg w (hrestrict hw)).1) hnullB
  obtain ⟨hcglobal, hcprofile⟩ := hc' row Φ Y initial hcell
    (CanonicalConic.angularMask z₀ θ₀ ha hb) FixedCutoffs.highFrequency
  obtain ⟨hflowreal, hflowcomplex, hfprofile⟩ := hf Q F row col D Φ Y hD hsmall hbig
    hΦD hYD hΦ hY hreg hcoeff hflow hα hbreg hFM
  have hrglobal : ContDiff ℝ ∞ (fun p ↦ (r p : ℂ)) :=
    extendedInitialScalar_complex_contDiff z₀ hR initial
      (hinitial.mono (ball_subset_ball (by linarith)))
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg K (s+2*(n+1)+13) F,
      cNorm_nonneg (closedBall p₀ (R/8)) (s+2*(n+1)+13) initial]
  have hHF : 1 + cNorm K (s+2*(n+1)+13) F ≤ H :=
    le_add_of_nonneg_right (cNorm_nonneg _ _ _)
  have hHC : 1 + cNorm K (s+2*(n+1)+6) F ≤ H :=
    (add_le_add (le_refl (1 : ℝ)) (cNorm_mono_order (s := K) (f := F)
      (by omega : s+2*(n+1)+6 ≤ s+2*(n+1)+13))).trans hHF
  have hHA : 1 + cNorm (closedBall p₀ (R/8)) (s+2*(n+1)) initial ≤ H := by
    have hh := cNorm_mono_order (s := closedBall p₀ (R/8)) (f := initial)
      (by omega : s+2*(n+1) ≤ s+2*(n+1)+13)
    dsimp [H]
    linarith [cNorm_nonneg K (s+2*(n+1)+13) F]
  have hm : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)) :=
    angularMask_complex_contDiff z₀ θ₀ ha hb
  have hcg (j) : ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j) :=
    hcglobal j
  refine ⟨hkernel ha haK hcell θ₀ hb FixedCutoffs.highFrequency Q F row col D Φ Y initial
      hF hrank hQ hFM6 hsmall hgeom hΦD hYD hY (hflow 1) hinit hYΦ hinv
      hcarrier hYcarrier hode hnull Yext hYagree,
    hH, hrglobal, hflowreal, hflowcomplex, hν, hcg, hm, ?_, ?_,
    hcprofile H hHC, ?_, ?_, ?_⟩
  · intro j
    exact frequencyScale_carrierChartNormalizedComponent_contDiff d (FixedCutoffs.physical ha 1)
      ν r flow (fun z x ↦ scalarTransportData_normalField d₀ Yext r flow ν x z) rfl
      j (hcg j) hm hrglobal hflowcomplex (graph_contDiff hYext)
  · intro j z x η hne
    exact frequencyScale_carrierChartNormalizedComponent_support d z₀ θ₀ ha hb rfl rfl j z x η hne
  · intro p i hi
    exact hr initial hinitial hIlow H hHA _ i hi
  · intro p i hi
    exact (hfprofile H hHF p i hi).2
  · intro R' hR' p hp
    exact ⟨hw R' hR' p hp, (hpn H hH s R' hR' p hp).1, (hpn H hH s R' hR' p hp).2⟩

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
