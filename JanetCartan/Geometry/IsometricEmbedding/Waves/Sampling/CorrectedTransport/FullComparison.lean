module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.NormalData
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.IntegratedComparison
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry

/-!
# Constructed corrected transport normal estimates

Apply the retained full-phase geometry and the original corrected amplitude
profiles to construct normal data for every spectator, color and band. The
integrated comparison then controls all prefixes of the same literal kernels.
Geometry is chosen before measurement budgets and every varying history.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CorrectedAtoms CanonicalRowComparison CanonicalAtomRealization
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open FullNormalGeometry FullNormalGeometry.PhaseJets MeasuredAmplitude
open NormalComparison ContinuumRow FullPhaseCharts ProjectedStressFrame
open MeanNormalBound MeanNormalBound.CanonicalGap ColoredNormalComparison
open SamplingKernelBounds SeparatedSampling RawInputPartition RawKernel
open BackgroundQuadrature Realization FullPhaseCharts.ActualComparison LatticeQuadrature

/-- Construct the full phase geometry and insert the literal fixed-response
homotopy before applying the integrated colored transport estimate. Neither
normal data nor a transport estimate is assumed. Geometry precedes immersion bounds, geometric gaps and every
measurement and coefficient budget; constants precede histories and rates.
The physical cutoff, detector projection, high-pass transition and all
original grouped prefixes remain unchanged
(`app:ch_waves:eq:colored-normal-comparison`,
`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem exists_correctedColoredCrossBandData_transport_bound_before_immersion_bounds
    {m p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀ (EuclideanSpace.single 0 1) ≠ 0)
    {ρ rmax emax xmax amin amax : ℝ} (hρ : 0 < ρ)
    (hrmax : 0 < rmax) (hemax : 0 < emax) (hxmax : 0 < xmax)
    (hamin : 0 < amin) (hamax : amin ≤ amax)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (hphaseBall : closedBall ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
      (2 * ρ) ⊆ domain T)
 :
    let center := ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ radius s e δ : ℝ,
      0 < radius ∧ radius ≤ rmax ∧ 0 < s ∧ s ≤ radius ∧
      0 < e ∧ e ≤ emax ∧ e ≤ 1 ∧ e ≤ ρ / 8 ∧ 0 < δ ∧ δ ≤ T.family.threshold ∧
    ∀ {KF : Set (Euclidean (m + 1))} (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ KF)
    (Mgeom : ℝ) {gmetric gnormal : ℝ} (hgmetric : 0 < gmetric) (hgnormal : 0 < gnormal),
    ∀ (Cmeasure : ℕ → ℝ) (hCmeasure : ∀ j, 0 ≤ Cmeasure j)
    (Cjet A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ)
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j),
    ∀ (K Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))),
      IsCompact K → IsOpen Ω → K ⊆ Ω →
    ∀ (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
      (hκ : ContDiff ℝ ∞ κ) (hκc : HasCompactSupport κ),
      tsupport κ ⊆ K →
      Prod.fst '' Function.support κ ⊆ closedBall (0 : Euclidean (m + 1)) (ρ / 2) →
      Prod.fst '' Function.support κ ⊆ closedBall (0 : Euclidean (m + 1)) (s / 4) →
    ∀ (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
      (hang : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
      (_hhom : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
      (hhigh : ContDiff ℝ ∞ highPass) (hhigh₀ : ∀ η, ‖η‖ ≤ 1 → highPass η = 0),
      (∀ η, 2 ≤ ‖η‖ → highPass η = 1) →
      amin ≤ (1 / 2) / ‖ηb‖ → 2 / ‖ηb‖ ≤ amax →
      (∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈
        CanonicalConic.closedDirections (n := m + 1) ηb radius) →
    ∀ (ψ : Point → ℝ) (R : ℝ), ContDiff ℝ ∞ ψ → PatchBounds ψ R 1 →
      (∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 →
        (carrierParameters (v, t), T.reference.spatialPatch (carrierParameters (v, t))) ∈
          closedBall center.2 (ρ / 4) ∧
        carrierParameters (v, t) ∈ parameterInterior (3 * P.radius / 2) ∧
        t ∈ closedBall (z₀ 0) radius ∧ v ∈ closedBall (spectatorCenter z₀) (s / 2)) →
    ∀ (φ : Point → ℝ) (Bpatch Pφ : ℝ), PatchBounds φ Bpatch Pφ → ContDiff ℝ ∞ φ →
      (∀ z, φ z ≠ 0 → ψ z = 1) →
    ∀ (kappa : ℝ → ℝ), HasCompactSupport kappa → ContDiff ℝ ∞ kappa →
      (∫ t, kappa t = 1) → (∀ t, 0 ≤ kappa t) →
      Function.support kappa ⊆ Icc (-(1 / 4)) (1 / 4) → 0 < p →
    ∀ Rmin : ℝ, 0 < Rmin →
    ∃ Ccompare > (0 : ℝ),
    ∀ (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
      Euclidean (m + 1)) (hC : ContDiff ℝ ∞ C),
    ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm KF (20 * ((m + 1) + 1) + 5) F ≤ Mgeom →
      (∀ x ∈ KF, ∀ v, gmetric * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ KF, ∀ w ∈ normalSpace F x, gnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ →
    ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
    let Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold} :=
      ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    ∀ (row col : Fin (m + 1))
      (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
        Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
      (χ : Euclidean (m + 1) → ℝ)
      (B : MetricField (m + 1) →ₗ[ℝ]
        (Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1))))
      (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ),
      (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
      ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω →
    ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L → 20 * ((m + 1) + 1) + 1 ≤ rpar →
      HasDerivativeProfile (Prod.fst '' K) C rpar L Cmeasure →
      HasDerivativeProfile K (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet →
      HasDerivativeProfile K (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀ →
      HasDerivativeProfile K (fullCorrectionPrincipalNormal T Q F row col Φ Y r) (rpar + 1) L A₁ →
      HasDerivativeProfile K (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀ →
      HasDerivativeProfile K (fullCorrectionReconstruction T Q F row col Φ Y r) (rpar + 1) L B₁ →
    ∀ (J : ℕ) (rate : (Fin 3 → Fin (p + 1)) → ℝ)
      (hτ : ∀ color, 0 < rate color), (∀ color, rate color ≤ 1) →
      (∀ color, ContDiffOn ℝ ∞
        (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B (rate color) r w.2 w.1) Ω) →
      (∀ color j, ∀ w ∈ K,
        ‖iteratedFDeriv ℝ j
          (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r (rate color)) w‖ ≤
          rate color * Cresp j * L ^ (j - rpar)) →
    ∀ (hA : ∀ color, Continuous (fun w ↦ κ w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate color) w))
      (hA₀ : Continuous (fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w))
      (Md : ℝ) (hMd : 0 ≤ Md)
      (hdb : ∀ η, ‖MaskProfiles.detectorMask (n := m + 1) angular highPass η‖ ≤ Md),
      (∀ color (j : Fin J), rate color * (2 : ℝ) ^ j.val ≤
        measuredPhaseRadius T hP (ρ := ρ)) →
    let D := correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC.continuous
      Prod.fst continuous_fst (fun q ↦ WithLp.toLp 2 q.2) (by fun_prop)
      hP z₀ hρ hcarrier (fun color ↦ (hτ color).ne') (MaskProfiles.detectorMask angular highPass)
      (MaskProfiles.contDiff_detectorMask angular highPass hang hhigh hhigh₀).continuous Md hMd hdb J
    let D₀ := leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ
      hκc hA₀ hC.continuous hP hcarrier (MaskProfiles.detectorMask angular highPass)
      (MaskProfiles.contDiff_detectorMask angular highPass hang hhigh hhigh₀).continuous Md hMd hdb J
    ∀ (Rcolor : (Fin 3 → Fin (p + 1)) → ℝ), (∀ color, Rmin ≤ Rcolor color) →
    ∀ (h lam Λ : ℝ), 0 < h → h ≤ 1 → 0 < lam → 1 ≤ Λ →
      (∀ color, rate color = (Rcolor color * lam)⁻¹) →
      2 * Λ / (Rmin * lam) ≤ e → J ≤ cutoffCount Λ →
    ∀ Lprefix : ℕ, Lprefix ≤ J →
      let E := patchMeanNormal p Bpatch φ (convolvedBoxWindow kappa p) h
        (fun color z ↦ refinedKernelPrefix D Lprefix (color, z))
      let E₀ := ∫ z : Point, φ z • atomNormal (refinedKernelPrefix D₀ Lprefix z)
      ‖E - E₀‖ ≤ Ccompare * lam⁻¹ * Λ / h ∧
        ‖(4 : ℝ) • realOutputCompression E - (4 : ℝ) • realOutputCompression E₀‖ ≤
          4 * (Ccompare * lam⁻¹ * Λ / h) := by
  classical
  intro center ηb
  let ecap := min emax (min 1 (ρ / 8))
  have hecap : 0 < ecap := lt_min hemax (lt_min zero_lt_one (by positivity))
  obtain ⟨radius, hradius, hrcap, s, hs, hsr, δ, hδ, hδcap, M, _hM, G,
    he, _hX, hX₀, hD₀, _hD, _hDclosure, _hXcap, hext, hphaseBudgets⟩ :=
    exists_uniform_literalFullPhaseNormalData_before_immersion_bounds T hP hz₀ hk hinc hd
      hrmax hecap hxmax hamin hamax
  have hemax' : G.ε₀ ≤ emax := he.trans (min_le_left _ _)
  have heone : G.ε₀ ≤ 1 := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heρ : G.ε₀ ≤ ρ / 8 := he.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨radius, s, G.ε₀, δ, hradius, hrcap, hs, hsr,
    G.ε₀_pos, hemax', heone, heρ, hδ, hδcap, ?_⟩
  intro KF hKF hKFU hball Mgeom gmetric gnormal hgmetric hgnormal
  obtain ⟨Cphase, _hCphase, hgeometry⟩ := hphaseBudgets hKF hKFU hball Mgeom hgmetric hgnormal
  intro Cmeasure hCmeasure Cjet A₀ A₁ B₀ B₁ Cresp hCjet hA₀ hA₁ hB₀ hB₁ hCresp
    K Ω hK hΩ hKΩ κ hκ hκc hκK hκρ hκs angular highPass ha hah hH hH₀ hH₁
    hlo hhi hangle ψ R hψsmooth hψbounds hψsupport φ Bpatch Pφ hφ hφs hplateau
    kappa hc hkappa hm hn hksupport hp Rmin hRmin
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  let V := closedBall (spectatorCenter z₀) (s / 2)
  let S := V ×ˢ (closure G.X ×ˢ closure G.D)
  have hS : IsCompact S := (isCompact_closedBall _ _).prod
    (G.bounded_X.isCompact_closure.prod G.bounded_D.isCompact_closure)
  have hSM : S ⊆ tripleDomain T M := fun q hq ↦ hext q.1 hq.1 hq.2
  have hκX : Prod.fst '' Function.support κ ⊆ G.X₀ := by rwa [hX₀]
  obtain ⟨A, _hA, hactual⟩ := exists_correctedTransportNormalData_of_profiles
    (N := embeddingDimension (m + 1)) T hP z₀ hρ hcarrier hK hΩ hKΩ κ hκ hκK
    Cjet A₀ A₁ B₀ B₁ Cresp Cmeasure hCjet hA₀ hA₁ hB₀ hB₁ hCresp hCmeasure
    M (le_refl (1 : ℝ)) hS hSM ψ hψsmooth angular highPass ha hah hH hH₁ G Cphase V
    (fun v hv w hw ↦ ⟨hv, hw⟩) heone hηb hradius hlo hhi hangle hκX
    (fun v _ t ht ↦ (hψsupport t v ht).2.2.1) hD₀
  obtain ⟨Ccompare, hCcompare, hcompare⟩ := exists_corrected_integrated_prefix_transport_bound
    G (fun j ↦ Cphase j + A j) V (isCompact_closedBall _ _)
    hc hkappa hm hn hksupport hp hφ hφs hRmin
  refine ⟨Ccompare, hCcompare, ?_⟩
  intro C hC F hF hi hrank hFM hmetric hnormal hclose hlow Q row col Φ Y χ B r
    hphase hν₀ hν₁ hV₀ hV₁ L rpar hL hreserve hmeasure hpξ hpν₀ hpν₁ hpV₀ hpV₁
    J rate hτ hτ₁ hresponse hresponseJets hA hA₀ Md hMd hdb hscale D D₀
    Rcolor hR h lam Λ hh hh₁ hlam hΛ hrateeq hbuffer hJ Lprefix hLprefix E E₀
  obtain ⟨_hlow', hN₀⟩ := hgeometry F hF hi hrank hFM hmetric hnormal hclose
  have hmeasureJets (j) (x) (hx : x ∈ Prod.fst '' K) :
      ‖iteratedFDeriv ℝ j C x‖ ≤ Cmeasure j * L ^ (j - rpar) :=
    (norm_iteratedFDeriv_le_cNorm (hK.image continuous_fst)
      (hC.of_le (by simp)) hx le_rfl).trans (hmeasure j)
  choose N₀ hNphase _hNamp _hNparameter hNdomain using
    fun v : V ↦ hN₀ v v.property
  choose Ns hNsp _hNst _hNsd hNsa using fun (v : V) color (j : ℕ) ↦
    hactual C hC Q F row col Φ Y χ B r hphase hν₀ hν₁ hV₀ hV₁
      (rate color) L rpar (hτ color) (hτ₁ color) hL hmeasureJets hpξ hpν₀ hpν₁ hpV₀ hpV₁
      (hresponse color) (hresponseJets color) hreserve v v.property j (N₀ v) (hNdomain v)
  let v₀ : V := ⟨spectatorCenter z₀, mem_closedBall_self (by positivity)⟩
  let Nall (v : Euclidean 2) := if hv : v ∈ V then Ns ⟨v, hv⟩ else Ns v₀
  have hNp (v) (hv : v ∈ V) (color) (j) :
      (Nall v color j).phase = fun ε x u ↦
        normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u) := by
    simpa only [Nall, dite_eq_left hv] using (hNsp ⟨v, hv⟩ color j).trans (hNphase ⟨v, hv⟩)
  have hNa (v) (hv : v ∈ V) (color) (j) :
      (Nall v color j).amplitude = fun ε x u ↦
        (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ (rate color)
          angular highPass ψ j v ε x u).ofLp := by
    simpa only [Nall, dite_eq_left hv] using hNsa ⟨v, hv⟩ color j
  exact hcompare T Q F row col Φ Y χ B r κ C z₀ hρ hκc rate hA hA₀ hC.continuous hP
    hcarrier (fun color ↦ (hτ color).ne') angular highPass
    (MaskProfiles.contDiff_detectorMask angular highPass ha hH hH₀).continuous Md hMd hdb
    center rfl hphaseBall hκρ ψ hψbounds hψsmooth.continuous
    (fun t v ht ↦ (hψsupport t v ht).1) (fun t v ht ↦ (hψsupport t v ht).2.1)
    hplateau (fun t v ht ↦ (hψsupport t v ht).2.2.2) Nall hNp hNa Rcolor hR
    h lam Λ hh hh₁ hlam hΛ hrateeq hbuffer hJ
    (fun color j ↦ by simpa only [abs_of_pos (hτ color)] using hscale color j) Lprefix hLprefix

/-- Specialization of the transport construction to prescribed immersion
budgets. The original public statement and literal kernels are retained
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_correctedColoredCrossBandData_transport_bound_of_profiles
    {m p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀ (EuclideanSpace.single 0 1) ≠ 0)
    {ρ rmax emax xmax amin amax : ℝ} (hρ : 0 < ρ)
    (hrmax : 0 < rmax) (hemax : 0 < emax) (hxmax : 0 < xmax)
    (hamin : 0 < amin) (hamax : amin ≤ amax)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (hphaseBall : closedBall ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
      (2 * ρ) ⊆ domain T)
    {KF : Set (Euclidean (m + 1))} (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ KF)
    (Mgeom : ℝ) {gmetric gnormal : ℝ} (hgmetric : 0 < gmetric) (hgnormal : 0 < gnormal) :
    let center := ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ radius s e δ : ℝ,
      0 < radius ∧ radius ≤ rmax ∧ 0 < s ∧ s ≤ radius ∧
      0 < e ∧ e ≤ emax ∧ e ≤ 1 ∧ e ≤ ρ / 8 ∧ 0 < δ ∧ δ ≤ T.family.threshold ∧
    ∀ (Cmeasure : ℕ → ℝ) (hCmeasure : ∀ j, 0 ≤ Cmeasure j)
    (Cjet A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ)
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j),
    ∀ (K Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))),
      IsCompact K → IsOpen Ω → K ⊆ Ω →
    ∀ (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
      (hκ : ContDiff ℝ ∞ κ) (hκc : HasCompactSupport κ),
      tsupport κ ⊆ K →
      Prod.fst '' Function.support κ ⊆ closedBall (0 : Euclidean (m + 1)) (ρ / 2) →
      Prod.fst '' Function.support κ ⊆ closedBall (0 : Euclidean (m + 1)) (s / 4) →
    ∀ (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
      (hang : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
      (_hhom : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
      (hhigh : ContDiff ℝ ∞ highPass) (hhigh₀ : ∀ η, ‖η‖ ≤ 1 → highPass η = 0),
      (∀ η, 2 ≤ ‖η‖ → highPass η = 1) →
      amin ≤ (1 / 2) / ‖ηb‖ → 2 / ‖ηb‖ ≤ amax →
      (∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈
        CanonicalConic.closedDirections (n := m + 1) ηb radius) →
    ∀ (ψ : Point → ℝ) (R : ℝ), ContDiff ℝ ∞ ψ → PatchBounds ψ R 1 →
      (∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 →
        (carrierParameters (v, t), T.reference.spatialPatch (carrierParameters (v, t))) ∈
          closedBall center.2 (ρ / 4) ∧
        carrierParameters (v, t) ∈ parameterInterior (3 * P.radius / 2) ∧
        t ∈ closedBall (z₀ 0) radius ∧ v ∈ closedBall (spectatorCenter z₀) (s / 2)) →
    ∀ (φ : Point → ℝ) (Bpatch Pφ : ℝ), PatchBounds φ Bpatch Pφ → ContDiff ℝ ∞ φ →
      (∀ z, φ z ≠ 0 → ψ z = 1) →
    ∀ (kappa : ℝ → ℝ), HasCompactSupport kappa → ContDiff ℝ ∞ kappa →
      (∫ t, kappa t = 1) → (∀ t, 0 ≤ kappa t) →
      Function.support kappa ⊆ Icc (-(1 / 4)) (1 / 4) → 0 < p →
    ∀ Rmin : ℝ, 0 < Rmin →
    ∃ Ccompare > (0 : ℝ),
    ∀ (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
      Euclidean (m + 1)) (hC : ContDiff ℝ ∞ C),
    ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm KF (20 * ((m + 1) + 1) + 5) F ≤ Mgeom →
      (∀ x ∈ KF, ∀ v, gmetric * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ KF, ∀ w ∈ normalSpace F x, gnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ →
    ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
    let Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold} :=
      ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    ∀ (row col : Fin (m + 1))
      (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
        Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
      (χ : Euclidean (m + 1) → ℝ)
      (B : MetricField (m + 1) →ₗ[ℝ]
        (Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1))))
      (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ),
      (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
      ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω →
    ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L → 20 * ((m + 1) + 1) + 1 ≤ rpar →
      HasDerivativeProfile (Prod.fst '' K) C rpar L Cmeasure →
      HasDerivativeProfile K (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet →
      HasDerivativeProfile K (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀ →
      HasDerivativeProfile K (fullCorrectionPrincipalNormal T Q F row col Φ Y r) (rpar + 1) L A₁ →
      HasDerivativeProfile K (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀ →
      HasDerivativeProfile K (fullCorrectionReconstruction T Q F row col Φ Y r) (rpar + 1) L B₁ →
    ∀ (J : ℕ) (rate : (Fin 3 → Fin (p + 1)) → ℝ)
      (hτ : ∀ color, 0 < rate color), (∀ color, rate color ≤ 1) →
      (∀ color, ContDiffOn ℝ ∞
        (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B (rate color) r w.2 w.1) Ω) →
      (∀ color j, ∀ w ∈ K,
        ‖iteratedFDeriv ℝ j
          (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r (rate color)) w‖ ≤
          rate color * Cresp j * L ^ (j - rpar)) →
    ∀ (hA : ∀ color, Continuous (fun w ↦ κ w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate color) w))
      (hA₀ : Continuous (fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w))
      (Md : ℝ) (hMd : 0 ≤ Md)
      (hdb : ∀ η, ‖MaskProfiles.detectorMask (n := m + 1) angular highPass η‖ ≤ Md),
      (∀ color (j : Fin J), rate color * (2 : ℝ) ^ j.val ≤
        measuredPhaseRadius T hP (ρ := ρ)) →
    let D := correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC.continuous
      Prod.fst continuous_fst (fun q ↦ WithLp.toLp 2 q.2) (by fun_prop)
      hP z₀ hρ hcarrier (fun color ↦ (hτ color).ne') (MaskProfiles.detectorMask angular highPass)
      (MaskProfiles.contDiff_detectorMask angular highPass hang hhigh hhigh₀).continuous Md hMd hdb J
    let D₀ := leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ
      hκc hA₀ hC.continuous hP hcarrier (MaskProfiles.detectorMask angular highPass)
      (MaskProfiles.contDiff_detectorMask angular highPass hang hhigh hhigh₀).continuous Md hMd hdb J
    ∀ (Rcolor : (Fin 3 → Fin (p + 1)) → ℝ), (∀ color, Rmin ≤ Rcolor color) →
    ∀ (h lam Λ : ℝ), 0 < h → h ≤ 1 → 0 < lam → 1 ≤ Λ →
      (∀ color, rate color = (Rcolor color * lam)⁻¹) →
      2 * Λ / (Rmin * lam) ≤ e → J ≤ cutoffCount Λ →
    ∀ Lprefix : ℕ, Lprefix ≤ J →
      let E := patchMeanNormal p Bpatch φ (convolvedBoxWindow kappa p) h
        (fun color z ↦ refinedKernelPrefix D Lprefix (color, z))
      let E₀ := ∫ z : Point, φ z • atomNormal (refinedKernelPrefix D₀ Lprefix z)
      ‖E - E₀‖ ≤ Ccompare * lam⁻¹ * Λ / h ∧
        ‖(4 : ℝ) • realOutputCompression E - (4 : ℝ) • realOutputCompression E₀‖ ≤
          4 * (Ccompare * lam⁻¹ * Λ / h) := by
  obtain ⟨radius, s, e, δ, hr, hrcap, hs, hsr, he, hecap, heone, heρ, hδ, hδcap, hall⟩ :=
    exists_correctedColoredCrossBandData_transport_bound_before_immersion_bounds
      T hP hz₀ hk hinc hd hρ hrmax hemax hxmax hamin hamax hcarrier hphaseBall
  exact ⟨radius, s, e, δ, hr, hrcap, hs, hsr, he, hecap, heone, heρ, hδ, hδcap,
    hall hKF hKFU hball Mgeom hgmetric hgnormal⟩

end JanetCartan.Sampling.CorrectedTransport
