module

public import JanetCartan.Iteration.PhysicalSampling.AngularCap
public import JanetCartan.Iteration.PhysicalSampling.WorkingRadius
public import JanetCartan.Iteration.PhysicalSampling.FullGeometry
public import JanetCartan.Iteration.PhysicalSampling.SliceGeometry
public import JanetCartan.Iteration.PhysicalSampling.SliceSharp
public import JanetCartan.Iteration.PhysicalSampling.Mean
public import JanetCartan.Iteration.PhysicalSampling.OriginalKernel

/-!
# Actual original scalar sharp and continuum bounds from pre-seed geometry

The common positive user cap is fixed before the one original source selection.
It controls both the original physical carrier radius and its angular width.
For that SAME selected detector, current immersion, inverse frequencies and
original carrier weight, this theorem constructs the sharp all-label scalar
bound and the uniform continuum mean. Neither operator bound is a hypothesis.
The scalar cutoff covers the original five-radius coefficient ball by
`scalarCutoff_plateau_of_original_cap` (`new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase LeadingWave.FullModulation
open NormalComparison Sampling Sampling.RawKernel Sampling.MeasuredAmplitude Sampling.MeanNormalBound
open Sampling.MeanNormalBound.NormalizedFullPhase RawPrimary.MaskProfiles PhysicalMean
open ContinuumRow ContinuumRow.CanonicalConic ProjectedStressFrame
open SamplingKernelBounds RawInputPartition SeparatedSampling Sampling.Realization

/-- The scalar row's two analytic sampling inputs, for the literal original
masks and weights, are produced from primitive current-map bounds. The only
selector obligation is the simultaneous pre-selection spatial/angular cap. -/
theorem exists_original_scalar_sampling_bounds
    {m : ℕ} (hn : 2 ≤ m + 1) {P : Patch (m + 1)}
    {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {amax emax : ℝ} (hamax : 0 < amax) (hemax : 0 < emax) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
    ∃ hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius),
      closedBall ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀)) (2 * ρ) ⊆ domain T ∧
    ∃ δ ε cap : ℝ, 0 < δ ∧ δ ≤ T.family.threshold ∧ 0 < ε ∧ ε ≤ emax ∧ ε ≤ ρ / 8 ∧ 0 < cap ∧
    ∃ χ : ContDiffBump (0 : Euclidean (m + 1)), cap ≤ χ.rIn ∧
      tsupport (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (amax / 16) ∧
      Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (ρ / 2) ∧
    ∃ β : Point → ℝ, ∃ hβ : Continuous β, ∃ hβone : ∀ z, |β z| ≤ 1,
      (∀ z, β z ≠ 0 →
        (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
          closedBall (z₀, T.reference.spatialPatch z₀) (ρ / 4) ∧
        WithLp.toLp 2 z ∈ parameterCube P.radius) ∧
    ∀ {ηoriginal : Euclidean (m + 1 - 1)} {roriginal aoriginal : ℝ}
      (hηoriginal : ηoriginal ≠ 0) (hroriginal : 0 < roriginal) (haoriginal : 0 < aoriginal),
      NormedSpace.normalize ηoriginal = NormedSpace.normalize
        (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) →
      angularWidth ηoriginal roriginal ≤ cap → aoriginal ≤ cap →
    ∀ {K : Set (Euclidean (m + 1))}, IsCompact K → K ⊆ U →
      closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K →
    ∀ (M : ℝ) {γ κ : ℝ}, 0 < γ → 0 < κ → ∀ p : ℕ,
    ∃ Csharp Cmean : ℝ, 0 < Csharp ∧ 0 < Cmean ∧
    ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K (20 * ((m + 1) + 1) + 5) F ≤ M →
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ →
    ∃ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
    let Q := ⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    ∀ (J : ℕ) (τ : (Fin 3 → Fin (p + 1)) → ℝ) (hτ : ∀ color, 0 < τ color),
      (∀ color (j : Fin J), τ color * (2 : ℝ) ^ j.val ≤ ε) →
    let D := originalScalarKernelData (J := J) T Q χ
      (0, (z₀, T.reference.spatialPatch z₀)) hρ hP hcarrier
      hηoriginal hroriginal τ (fun color ↦ (hτ color).ne')
    let Dcut := scalarCarrierCutKernel D β hβ hβone
    (∀ (i : RefinedIndex J) color z,
      ‖Dcut.operator (refinedRadius i) (i.1, (color, z))‖ ^ 2 ≤ Csharp * refinedRadius i) ∧
    (∀ (B h : ℝ) (w : ℝ → ℝ),
      PatchBounds (originalConicCarrierWeight z₀ haoriginal) B 1 →
      WindowBounds p w 1 → Continuous w → h ≠ 0 →
      ‖patchMeanNormal p B (originalConicCarrierWeight z₀ haoriginal) w h
        (fun color z ↦ refinedKernelPrefix Dcut J (color, z))‖ ≤ Cmean) ∧
    (∀ z, originalConicCarrierWeight z₀ haoriginal z ≠ 0 → β z = 1) := by
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  have hnorm : 0 < ‖ηb‖ := norm_pos_iff.mpr hηb
  obtain ⟨ρ, hρ, hphase, hcarrier, hcube⟩ := exists_scalar_sampling_workingRadius hP T hz₀
  obtain ⟨a, ha, hacap, haR, b, _hb, _hbcap, hbcov, e, he, hecap, heb,
    δs, hδs, hδscap, Gs, _hXs, _hDs, _hX₀s, _hD₀s, hεs, hsbuild⟩ :=
    exists_retained_scalarSliceFamily T hn hP hamax (by norm_num : (0 : ℝ) < 1) hemax
  obtain ⟨r, s, δf, hr, _hrcap, hs, _hsr, hδf, hδfcap, Gf, hef, hXf, _hDf,
    χ, hχρ, hχX, d, hdpos, β, Bβ, _hBβ, hβsmooth, _hβcompact, hβbounds,
    hβplateau, hβgraph, hfbuild⟩ :=
    exists_retained_scalarNormalFamily T hP hz₀ hk hinc hd hρ
      (by norm_num : (0 : ℝ) < 1) he (by positivity : 0 < a / 4)
      (div_pos (by norm_num : (0 : ℝ) < 1 / 2) hnorm)
      (by apply div_le_div_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 2) hnorm.le)
  have hχa : tsupport (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (a / 4) :=
    closure_minimal (hχX.trans (hXf.trans ball_subset_closedBall)) isClosed_closedBall
  obtain ⟨carrierCap, hcarrierCap, hcarplateau⟩ :=
    exists_originalCarrier_scalar_plateau_cap z₀ hdpos β hβplateau
  obtain ⟨cap, hcap, hcapχ, hcapcarrier, _hcapslice, hcapangle⟩ :=
    exists_common_scalar_source_cap χ hηb hr hcarrierCap (by positivity : 0 < a / 4)
  let ε := min Gf.ε₀ (min (measuredPhaseRadius T hP (ρ := ρ)) (ρ / 8))
  have hεpos : 0 < ε := lt_min Gf.ε₀_pos
    (lt_min (measuredPhaseRadius_pos T hρ hP) (by positivity))
  have hεfull : ε ≤ Gf.ε₀ := min_le_left _ _
  have hεphase : ε ≤ measuredPhaseRadius T hP (ρ := ρ) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hερ : ε ≤ ρ / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hβone (z : Point) : |β z| ≤ 1 := by
    rw [abs_of_nonneg (hβbounds.nonneg z)]
    exact hβbounds.le_bound z
  have hβgeometry : ∀ z, β z ≠ 0 →
      (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
        closedBall (z₀, T.reference.spatialPatch z₀) (ρ / 4) ∧
      WithLp.toLp 2 z ∈ parameterCube P.radius := by
    intro z hz
    obtain ⟨⟨t, v⟩, rfl⟩ := carrierSamplingEquiv.surjective z
    have hg := (hβgraph t v hz).1
    simpa only [carrierParameters_eq_sampling] using
      And.intro hg (scalar_parameter_cube_of_graph_support T hcube hg)
  refine ⟨ρ, hρ, hcarrier, hphase, min δf δs, ε, cap, lt_min hδf hδs,
    (min_le_left _ _).trans hδfcap, hεpos, hεfull.trans (hef.trans hecap), hερ, hcap,
    χ, hcapχ, hχa.trans (closedBall_subset_closedBall (by linarith)), hχρ,
    β, hβsmooth.continuous, hβone, hβgeometry, ?_⟩
  intro ηoriginal roriginal aoriginal hηoriginal hroriginal haoriginal hdirection hanglecap haorigcap
    K hK hKU hball M γ κ hγ hκ p
  let angular := originalConicDetector hηoriginal hroriginal
  let H := fun η : Euclidean (m + 1 - 1) ↦ FixedCutoffs.highFrequency ‖η‖
  have hang : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ :=
    fun _ hθ ↦ originalConicDetector_contDiffAt hηoriginal hroriginal hθ
  have hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ :=
    originalConicDetector_homogeneous hηoriginal hroriginal
  have hH : ContDiff ℝ ∞ H := contDiff_originalConicHighPass (m + 1)
  have hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0 := fun _ hη ↦ FixedCutoffs.highFrequency_zero hη
  have hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1 := fun _ hη ↦ FixedCutoffs.highFrequency_one hη
  have hangle : ∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈ closedDirections ηb r :=
    fun _ hθ ↦ originalConicDetector_support_of_angular_cap hηoriginal hroriginal
      hdirection hanglecap hcapangle hθ
  obtain ⟨Cf, _hCf, Cfull, hCfull, hfull⟩ := hfbuild angular H hang hah hH hH₁
    le_rfl le_rfl hangle hK hKU hball M hγ hκ
  obtain ⟨Cs, _hCs, hslice⟩ := hsbuild χ hχa angular H hang hah hH hH₁ hK hKU hball M hγ hκ
  obtain ⟨Csharp, hCsharp, hsharp⟩ := exists_retainedScalar_sharp_bound T Gs Cs ha haR he heb hεs
  let Ccolored := ∑ _color : Fin 3 → Fin (p + 1),
    Cfull * volume.real (closedBall (0 : Euclidean 2) (2 * Bβ))
  have hCcolored : 0 ≤ Ccolored := Finset.sum_nonneg fun _ _ ↦ mul_nonneg hCfull.le (by positivity)
  refine ⟨Csharp, Ccolored + 1, hCsharp, by linarith, ?_⟩
  intro F hF hi hrank hFM hmetric hnormal hsmall
  obtain ⟨hlow, hNf⟩ := hfull F hF hi hrank hFM hmetric hnormal
    (hsmall.trans_le (min_le_left _ _))
  obtain ⟨hlows, hNs⟩ := hslice F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM)
    hmetric hnormal (hsmall.trans_le (min_le_right _ _))
  refine ⟨hlow, ?_⟩
  intro Q J τ hτ hτsmall D Dcut
  have hplateau : ∀ z, originalConicCarrierWeight z₀ haoriginal z ≠ 0 → β z = 1 :=
    hcarplateau haoriginal (haorigcap.trans hcapcarrier)
  have hεj (color) (j : Fin J) : τ color * (2 : ℝ) ^ j.val ∈ Icc 0 Gf.ε₀ :=
    ⟨mul_nonneg (hτ color).le (by positivity), (hτsmall color j).trans hεfull⟩
  have hscale (color) (j : Fin J) : |τ color| * (2 : ℝ) ^ j.val ≤
      measuredPhaseRadius T hP (ρ := ρ) := by
    rw [abs_of_pos (hτ color)]
    exact (hτsmall color j).trans hεphase
  refine ⟨?_, ?_, hplateau⟩
  · apply scalarCarrierCutKernel_sharp D β hβsmooth.continuous hβone hCsharp.le
    intro i color z hz
    obtain ⟨⟨t, v⟩, rfl⟩ := carrierSamplingEquiv.surjective z
    have hgraph := (hβgraph t v hz).1
    have hzCube := scalar_parameter_cube_of_graph_support T hcube hgraph
    obtain ⟨Ns, hNp, hNa⟩ := hNs (carrierParameters (v, t)) hzCube
    have hb := hbcov _ hzCube
    have hband := (hsharp Q χ (0, (z₀, T.reference.spatialPatch z₀)) hρ hP hcarrier
      angular H hang hH hH₀ 1 zero_le_one
      (norm_originalConicDetectorMask_le_one hηoriginal hroriginal) hphase hχa hχρ
      p J τ (fun color ↦ (hτ color).ne') color i.1 (carrierParameters (v, t)) hb hgraph
      ⟨(hεj color i.1).1, (hεj color i.1).2.trans (by simpa only [hεs] using hef)⟩
      (by rw [abs_of_pos (mul_pos (hτ color) (by positivity))]; exact (hτsmall color i.1).trans hερ)
      (Ns i.1.val) (hNp i.1.val) (hNa i.1.val)).2 i.2
    simpa only [D, originalScalarKernelData, angular, H,
      carrierParameters_eq_sampling, WithLp.ofLp_toLp] using hband
  · intro B h w hφ hw hwc hh
    rw [scalarCarrierCutKernel_patchMeanNormal D β hβsmooth.continuous hβone _ hplateau]
    have hbound := (retainedScalarKernelData_mean_le T Q χ
      (0, (z₀, T.reference.spatialPatch z₀)) hρ hP hcarrier
      angular H hang hH hH₀ 1 zero_le_one
      (norm_originalConicDetectorMask_le_one hηoriginal hroriginal) τ (fun color ↦ (hτ color).ne')
      hphase hχρ β hβbounds hβsmooth.continuous
      (fun t v hz ↦ (hβgraph t v hz).1) (fun t v hz ↦ (hβgraph t v hz).2.1)
      hscale hCfull.le (fun v hv ↦ hNf v (by obtain ⟨t, ht⟩ := hv; exact (hβgraph t v ht).2.2.2))
      hεj (originalConicCarrierWeight z₀ haoriginal) B 1 hφ
      (contDiff_originalConicCarrierWeight z₀ haoriginal).continuous hplateau w hw hwc hh).1
    calc
      _ ≤ Ccolored := by
        simpa only [D, originalScalarKernelData, angular, H, Ccolored,
          norm_one, one_mul] using hbound
      _ ≤ Ccolored + 1 := le_add_of_nonneg_right (by norm_num)

end JanetCartan.PhysicalSampling
