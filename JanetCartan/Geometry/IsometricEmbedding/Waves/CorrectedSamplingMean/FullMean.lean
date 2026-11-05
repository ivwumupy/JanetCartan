module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.NormalData
public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.NormalIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.LiteralMeanBound.FrequencyGap
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.UniformBound

/-!
# Uniform corrected colored mean from the original profiles

Construct the phase-only data from the original retained Hamilton family,
insert the literal corrected product, derive the active-slice gap, and apply
the uniform dyadic normal bound. Positivity removes the original color masks.
No normal-data, averaged-gradient or summed-operator bound is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedMean
open CorrectedAtoms CanonicalRowComparison CanonicalAtomRealization
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open FullNormalGeometry FullNormalGeometry.PhaseJets MeasuredAmplitude
open NormalComparison ContinuumRow FullPhaseCharts ProjectedStressFrame
open MeanNormalBound MeanNormalBound.CanonicalGap ColoredNormalComparison
open SamplingKernelBounds SeparatedSampling RawInputPartition RawKernel
open BackgroundQuadrature Realization FullPhaseCharts.ActualComparison

/-- Choose the original full-phase geometry once before every measurement
profile. The same `radius`, `s`, `e` and `δ` work for all nonnegative profile
sequences chosen after the supplied masks and weights. Only the normal-amplitude
budget and mean constant use that sequence. This closes the measurement order
of choices in `Sampling.exists_correctedColoredCrossBandData_sample_event_after_cutoff`
without identifying independent geometry witnesses
(`app:ch_waves:eq:sampling-operator-bounds`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem exists_correctedColoredCrossBandData_mean_bound_before_measurement_profiles
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
    (Mgeom : ℝ) {gmetric gnormal : ℝ} (hgmetric : 0 < gmetric) (hgnormal : 0 < gnormal)
    (Cjet A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ)
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j) :
    let center := ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ radius s e δ : ℝ,
      0 < radius ∧ radius ≤ rmax ∧ 0 < s ∧ s ≤ radius ∧
      0 < e ∧ e ≤ emax ∧ e ≤ 1 ∧ e ≤ ρ / 8 ∧ 0 < δ ∧ δ ≤ T.family.threshold ∧
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
    ∀ (φ : Point → ℝ) (Bpatch Pφ : ℝ), PatchBounds φ Bpatch Pφ → Continuous φ →
      (∀ z, φ z ≠ 0 → ψ z = 1) →
    ∀ (Cmeasure : ℕ → ℝ), (∀ j, 0 ≤ Cmeasure j) →
    ∃ Cmean > (0 : ℝ),
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
      HasDerivativeProfile K (fun w ↦ C w.1) rpar L Cmeasure →
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
      (Md : ℝ) (hMd : 0 ≤ Md)
      (hdb : ∀ η, ‖MaskProfiles.detectorMask (n := m + 1) angular highPass η‖ ≤ Md),
      (∀ color (j : Fin J), rate color * (2 : ℝ) ^ j.val ≤
        min e (measuredPhaseRadius T hP (ρ := ρ))) →
    let D := correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC.continuous
      Prod.fst continuous_fst (fun q ↦ WithLp.toLp 2 q.2) (by fun_prop)
      hP z₀ hρ hcarrier (fun color ↦ (hτ color).ne') (MaskProfiles.detectorMask angular highPass)
      (MaskProfiles.contDiff_detectorMask angular highPass hang hhigh hhigh₀).continuous Md hMd hdb J
    ∀ (w : ℝ → ℝ), WindowBounds p w 1 → Continuous w → ∀ h : ℝ, h ≠ 0 →
      let E := patchMeanNormal p Bpatch φ w h (fun color z ↦ refinedKernelPrefix D J (color, z))
      ‖E‖ ≤ Cmean ∧ ‖(4 : ℝ) • realOutputCompression E‖ ≤ 4 * Cmean := by
  intro center ηb
  let ecap := min emax (min 1 (ρ / 8))
  have hecap : 0 < ecap := lt_min hemax (lt_min zero_lt_one (by positivity))
  obtain ⟨rg, hrg, hrgcap, sg, hsg, _hsgr, eg, heg, hegcap, δg, hδg, γg, hγg, hgap⟩ :=
    LiteralMeanBound.exists_uniformNormalData_supported_gap T hP hz₀ hk hinc hd
      hrmax hecap hamin hamax
  obtain ⟨radius, hradius, hrcap, s, hs, hsr, δp, hδp, hδpcap, M, _hM, G,
    he, _hX, hX₀, hD₀, hD, _hDclosure, hXcap, hext, Cphase, _hCphase, hgeometry⟩ :=
    exists_uniform_literalFullPhaseNormalData T hP hz₀ hk hinc hd
      (lt_min hrg hsg) heg (lt_min hxmax (by positivity : 0 < sg / 2))
      hamin hamax hKF hKFU hball Mgeom hgmetric hgnormal
  have hemax' : G.ε₀ ≤ emax := he.trans (hegcap.trans (min_le_left _ _))
  have heone : G.ε₀ ≤ 1 := he.trans (hegcap.trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have heρ : G.ε₀ ≤ ρ / 8 := he.trans (hegcap.trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hrrg : radius ≤ rg := hrcap.trans (min_le_left _ _)
  have hssg : s ≤ sg := hsr.trans (hrcap.trans (min_le_right _ _))
  have hXgap : G.X₀ ⊆ closedBall 0 (sg / 2) :=
    hXcap.trans ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall)
  have hDgap : canonicalInputCoordinates T '' G.D₀ ⊆
      (fun q : ℝ × Euclidean (m + 1) ↦ radialInput T q.1 q.2) ''
        (Icc amin amax ×ˢ normalizedInputCore T z₀ ηb rg) := by
    rw [hD]
    apply image_mono
    apply prod_mono (Subset.refl _)
    intro w hw
    exact ⟨closedBall_subset_closedBall hrrg hw.1, closedBall_subset_closedBall hrrg hw.2⟩
  refine ⟨radius, s, G.ε₀, min δp δg, hradius, hrrg.trans hrgcap, hs, hsr,
    G.ε₀_pos, hemax', heone, heρ, lt_min hδp hδg, (min_le_left _ _).trans hδpcap, ?_⟩
  intro K Ω hK hΩ hKΩ κ hκ hκc hκK hκρ hκs angular highPass ha hah hH hH₀ hH₁
    hlo hhi hangle ψ R hψsmooth hψbounds hψsupport φ Bpatch Pφ hφ hφc hplateau Cmeasure hCmeasure
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  let V := closedBall (spectatorCenter z₀) (s / 2)
  let S := V ×ˢ (closure G.X ×ˢ closure G.D)
  have hS : IsCompact S := (isCompact_closedBall _ _).prod
    (G.bounded_X.isCompact_closure.prod G.bounded_D.isCompact_closure)
  have hSM : S ⊆ tripleDomain T M := fun q hq ↦ hext q.1 hq.1 hq.2
  have hκX : Prod.fst '' Function.support κ ⊆ G.X₀ := by rwa [hX₀]
  obtain ⟨A, _hA, hactual⟩ := exists_fixedRateNormalData_of_measurement_profiles
    (N := embeddingDimension (m + 1)) T hP z₀ hρ hcarrier hK hΩ hKΩ κ hκ hκK Cmeasure hCmeasure
    Cjet A₀ A₁ B₀ B₁ Cresp hCjet hA₀ hA₁ hB₀ hB₁ hCresp M (le_refl (1 : ℝ)) hS hSM
    ψ hψsmooth angular highPass ha hah hH hH₁ G Cphase V
    (fun v hv w hw ↦ ⟨hv, hw⟩) heone hηb hradius hlo hhi hangle hκX
    (fun v _ t ht ↦ (hψsupport t v ht).2.2.1) hD₀
  obtain ⟨Cslice, hCslice, hsum⟩ := exists_uniform_powTwoNormal_bound G
    (fun j ↦ Cphase j + A j) hγg
  let Cmean := ‖Pφ‖ * ∑ _color : Fin 3 → Fin (p + 1),
    Cslice * volume.real (closedBall (0 : Euclidean 2) (2 * R))
  have hCmean : 0 ≤ Cmean := mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ mul_nonneg hCslice.le measureReal_nonneg)
  refine ⟨Cmean + 1, by linarith, ?_⟩
  intro C hC F hF hi hrank hFM hmetric hnormal hclose hlow Q row col Φ Y χ B r
    hphase hν₀ hν₁ hV₀ hV₁ L rpar hL hreserve hmeasure hpξ hpν₀ hpν₁ hpV₀ hpV₁
    J rate hτ hτ₁ hresponse hresponseJets hA Md hMd hdb hscale D w hw hwc h hh
  have hε (color) (j : Fin J) : rate color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀ :=
    ⟨mul_nonneg (hτ color).le (by positivity), (hscale color j).trans (min_le_left _ _)⟩
  have hphaseScale (color) (j : Fin J) :
      |rate color| * (2 : ℝ) ^ j.val ≤ measuredPhaseRadius T hP (ρ := ρ) := by
    rw [abs_of_pos (hτ color)]
    exact (hscale color j).trans (min_le_right _ _)
  obtain ⟨_hlow', hN₀⟩ := hgeometry F hF hi hrank hFM hmetric hnormal
    (hclose.trans_le (min_le_left _ _))
  let Op := fun (color : Fin 3 → Fin (p + 1)) (j : Fin J) (v : Euclidean 2) ↦
    fullBandKernelOperator D (fun z ↦ (j, (color, z)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      ψ hψsmooth.continuous j.val R v
  have hslice (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2) :
      ‖∑ j : Fin J, atomNormal (Op color j v)‖ ≤ Cslice := by
    by_cases hv : ∃ t, ψ (carrierSamplingEquiv (t, v)) ≠ 0
    · obtain ⟨t, ht⟩ := hv
      have hv' := (hψsupport t v ht).2.2.2
      obtain ⟨N₀, hNphase, _hNamp, _hNparameter, hNdomain⟩ := hN₀ v hv'
      choose Ns hNsp _hNst _hNsd hNsa using fun j : Fin J ↦
        hactual C hC Q F row col Φ Y χ B r hphase hν₀ hν₁ hV₀ hV₁
          (rate color) L rpar (hτ color) (hτ₁ color) hL hmeasure hpξ hpν₀ hpν₁ hpV₀ hpV₁
          (hresponse color) (hresponseJets color) hreserve v hv' j.val N₀ hNdomain
      have hNp (j : Fin J) := (hNsp j).trans hNphase
      have hnormal (j : Fin J) := correctedColoredCrossBandData_normal_eq_fixedRateNormal
        T Q F row col Φ Y χ B r κ C z₀ hρ hκc rate hA hC.continuous hP hcarrier
        (fun color ↦ (hτ color).ne') angular highPass
        (MaskProfiles.contDiff_detectorMask angular highPass ha hH hH₀).continuous Md hMd hdb
        center rfl hphaseBall hκρ ψ hψbounds hψsmooth.continuous
        (fun t v ht ↦ (hψsupport t v ht).1) (fun t v ht ↦ (hψsupport t v ht).2.1)
        j color v (hphaseScale color j) (Ns j) (hNp j) (hNsa j) (hε color j)
      have heq : (∑ j : Fin J, atomNormal (Op color j v)) =
          samplingOutputConjugation (m + 1) (∑ j : Fin J,
            ((Ns j).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (rate color * (2 : ℝ) ^ j.val)).comp
              ((Ns j).uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
                (rate color * (2 : ℝ) ^ j.val)).adjoint) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun j _ ↦ hnormal j)
      rw [heq, norm_samplingOutputConjugation]
      apply hsum J Ns (fun j ↦ rate color * (2 : ℝ) ^ j.val) (hε color)
      intro j
      exact (hgap Q (hclose.trans_le (min_le_right _ _)) (m + 1) G
        (fun j ↦ Cphase j + A j) (Ns j) v
        (closedBall_subset_closedBall (by linarith only [hssg]) hv')
        hXgap hDgap he (by intro ε' _ u _ x _; rw [hNp]) _ (hε color j)).1
    · have hz (j : Fin J) : Op color j v = 0 :=
        fullBandKernelOperator_eq_zero_of_cutoff_slice D _ _ ψ hψsmooth.continuous
          j.val R v (by simpa only [not_exists, not_not] using hv)
      simpa only [hz, atomNormal, map_zero, ContinuousLinearMap.zero_comp,
        Finset.sum_const_zero, norm_zero] using hCslice.le
  have hint (color : Fin 3 → Fin (p + 1)) :
      ‖∑ j : Fin J, ∫ v : Euclidean 2, atomNormal (Op color j v)‖ ≤
        Cslice * volume.real (closedBall (0 : Euclidean 2) (2 * R)) := by
    have hi (j : Fin J) : Integrable (fun v : Euclidean 2 ↦ atomNormal (Op color j v)) :=
      integrable_fullBandKernelOperator_cutoff_normal D j (fun z ↦ (color, z))
        (continuous_const.prodMk continuous_id) hψbounds hψsmooth.continuous
    rw [← integral_finsetSum _ (fun j _ ↦ hi j)]
    have heq : (∫ v : Euclidean 2, ∑ j : Fin J, atomNormal (Op color j v)) =
        ∫ v in closedBall (0 : Euclidean 2) (2 * R),
          ∑ j : Fin J, atomNormal (Op color j v) := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro v hv
      apply Finset.sum_eq_zero
      intro j _
      have hz : Op color j v = 0 := fullBandKernelOperator_eq_zero_off_spectator_ball
        D _ _ hψbounds hψsmooth.continuous j.val hv
      simp only [hz, atomNormal, map_zero, ContinuousLinearMap.zero_comp]
    rw [heq]
    exact norm_setIntegral_le_of_norm_le_const (isCompact_closedBall _ _).measure_lt_top
      (fun v _ ↦ hslice color v)
  have horder : (∑ color : Fin 3 → Fin (p + 1), ∫ z : Point,
      φ z • atomNormal (refinedKernelPrefix D J (color, z))) ≤
      Pφ • ∑ color : Fin 3 → Fin (p + 1), ∑ j : Fin J,
        ∫ v : Euclidean 2, atomNormal (Op color j v) := by
    rw [Finset.smul_sum]
    exact Finset.sum_le_sum fun color _ ↦
      integral_refinedKernelPrefix_normal_le_cutoff_fullBand D (fun z ↦ (color, z))
        (continuous_const.prodMk continuous_id) hφ hφc hψbounds hψsmooth.continuous hplateau
  have hmean : ‖patchMeanNormal p Bpatch φ w h
      (fun color z ↦ refinedKernelPrefix D J (color, z))‖ ≤ Cmean := by
    have hmask := norm_refinedKernelPrefix_mean_le_unmasked
      (A := Unit) (fun _ ↦ D) hw (fun _ ↦ hφ) (fun _ ↦ hφc) hwc hh
    simp only [Fintype.sum_unique] at hmask
    apply hmask.trans
    apply (CStarAlgebra.norm_le_norm_of_le_of_nonneg horder ?_).trans
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun color _ ↦ hint color)) (norm_nonneg _)
    · exact Finset.sum_nonneg fun color _ ↦ integral_nonneg fun z ↦
        smul_nonneg (hφ.nonneg z) (atomNormal_nonneg _)
  have hb := hmean.trans (show Cmean ≤ Cmean + 1 by linarith)
  refine ⟨hb, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  exact mul_le_mul_of_nonneg_left ((realOutputCompression_norm_le _).trans hb) (by norm_num)

/-- The literal corrected colored mean is uniformly bounded from the five
raw profiles and the same-response jets, on the supplied retained chart and
with the supplied real measurement controlled by its original uniform profile.
All masks are supplied, and their complete supports are retained. The phase
geometry and active-slice gap are constructed internally. The frequency,
history scale, number of bands and mesh do not enter the constant
(`app:ch_waves:eq:sampling-operator-bounds`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem exists_correctedColoredCrossBandData_mean_bound_of_profiles
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
    (Mgeom : ℝ) {gmetric gnormal : ℝ} (hgmetric : 0 < gmetric) (hgnormal : 0 < gnormal)
    (Cmeasure : ℕ → ℝ) (hCmeasure : ∀ j, 0 ≤ Cmeasure j)
    (Cjet A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ)
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j) :
    let center := ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ radius s e δ : ℝ,
      0 < radius ∧ radius ≤ rmax ∧ 0 < s ∧ s ≤ radius ∧
      0 < e ∧ e ≤ emax ∧ e ≤ 1 ∧ e ≤ ρ / 8 ∧ 0 < δ ∧ δ ≤ T.family.threshold ∧
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
    ∀ (φ : Point → ℝ) (Bpatch Pφ : ℝ), PatchBounds φ Bpatch Pφ → Continuous φ →
      (∀ z, φ z ≠ 0 → ψ z = 1) →
    ∃ Cmean > (0 : ℝ),
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
      HasDerivativeProfile K (fun w ↦ C w.1) rpar L Cmeasure →
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
      (Md : ℝ) (hMd : 0 ≤ Md)
      (hdb : ∀ η, ‖MaskProfiles.detectorMask (n := m + 1) angular highPass η‖ ≤ Md),
      (∀ color (j : Fin J), rate color * (2 : ℝ) ^ j.val ≤
        min e (measuredPhaseRadius T hP (ρ := ρ))) →
    let D := correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC.continuous
      Prod.fst continuous_fst (fun q ↦ WithLp.toLp 2 q.2) (by fun_prop)
      hP z₀ hρ hcarrier (fun color ↦ (hτ color).ne') (MaskProfiles.detectorMask angular highPass)
      (MaskProfiles.contDiff_detectorMask angular highPass hang hhigh hhigh₀).continuous Md hMd hdb J
    ∀ (w : ℝ → ℝ), WindowBounds p w 1 → Continuous w → ∀ h : ℝ, h ≠ 0 →
      let E := patchMeanNormal p Bpatch φ w h (fun color z ↦ refinedKernelPrefix D J (color, z))
      ‖E‖ ≤ Cmean ∧ ‖(4 : ℝ) • realOutputCompression E‖ ≤ 4 * Cmean := by
  intro center ηb
  obtain ⟨radius, s, e, δ, hr, hrcap, hs, hsr, he, hecap, heone, heρ, hδ, hδcap, hall⟩ :=
    exists_correctedColoredCrossBandData_mean_bound_before_measurement_profiles (p := p)
      T hP hz₀ hk hinc hd hρ hrmax hemax hxmax hamin hamax hcarrier hphaseBall
      hKF hKFU hball Mgeom hgmetric hgnormal Cjet A₀ A₁ B₀ B₁ Cresp
      hCjet hA₀ hA₁ hB₀ hB₁ hCresp
  refine ⟨radius, s, e, δ, hr, hrcap, hs, hsr, he, hecap, heone, heρ, hδ, hδcap, ?_⟩
  intro K Ω hK hΩ hKΩ κ hκ hκc hκK hκρ hκs angular highPass ha hah hH hH₀ hH₁
    hlo hhi hangle ψ R hψsmooth hψbounds hψsupport φ Bpatch Pφ hφ hφc hplateau
  exact hall K Ω hK hΩ hKΩ κ hκ hκc hκK hκρ hκs
    angular highPass ha hah hH hH₀ hH₁ hlo hhi hangle
    ψ R hψsmooth hψbounds hψsupport φ Bpatch Pφ hφ hφc hplateau Cmeasure hCmeasure

end JanetCartan.Sampling.CorrectedMean
