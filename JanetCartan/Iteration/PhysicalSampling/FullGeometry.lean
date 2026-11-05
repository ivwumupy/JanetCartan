module

public import JanetCartan.Iteration.PhysicalSampling.Normal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.SupportChoices
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.LiteralMeanBound.FrequencyGap
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.UniformDyadicBound

/-!
# Actual scalar full-normal family from the original retained chart

Construct the phase geometry, buffered scalar cutoff, carrier majorant and all
scalar amplitude budgets before the current immersion. The original phase
producer and canonical frequency-gap theorem then prove the uniform dyadic
normal sum for that same scalar row. No normal geometry, phase-jet estimate,
frequency gap or operator-norm bound is an input.

The current immersion enters only through its original fixed-order physical
map budget, metric and normal gaps, and projected-frame neighborhood. Physical
history specialization must supply those primitive inputs for the SAME original
reference; the same-sample event and sharp transverse band bound remain separate
parts of `new:eq:amplitude-test`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase ActualComparison
open NormalComparison Sampling Sampling.MeasuredAmplitude Sampling.FullNormalGeometry
open Sampling.FullNormalGeometry.PhaseJets Sampling.MeanNormalBound
open Sampling.MeanNormalBound.CanonicalGap Sampling.MeanNormalBound.NormalizedFullPhase
open RawPrimary.MaskProfiles PhysicalMean ContinuumRow ContinuumRow.CanonicalConic
open ProjectedStressFrame

/-- The literal scalar normal family and its uniform dyadic normal bound are
constructed from the original retained chart and current immersion data.
Every cutoff, tolerance and analytic constant precedes the current immersion,
all band ceilings and all inverse frequencies (`new:eq:amplitude-test`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_retained_scalarNormalFamily
    {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {ρ rmax emax xmax amin amax : ℝ} (hρ : 0 < ρ) (hrmax : 0 < rmax)
    (hemax : 0 < emax) (hxmax : 0 < xmax) (hamin : 0 < amin) (hamax : amin ≤ amax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r s δ : ℝ, 0 < r ∧ r ≤ rmax ∧ 0 < s ∧ s ≤ r ∧
      0 < δ ∧ δ ≤ T.family.threshold ∧
    ∃ G : UniformNormalGeometry (m + 1) (m + 1),
      G.ε₀ ≤ emax ∧ G.X₀ ⊆ ball 0 xmax ∧
      G.D₀ = radialSamplingSupport T z₀ ηb r amin amax ∧
    ∃ χ : ContDiffBump (0 : Euclidean (m + 1)),
      Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (ρ / 2) ∧
      Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ G.X₀ ∧
    ∃ d > (0 : ℝ), ∃ ψ : SeparatedSampling.Point → ℝ, ∃ B > (0 : ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ SeparatedSampling.PatchBounds ψ B 1 ∧
      (∀ z, WithLp.toLp 2 z ∈ closedBall z₀ d → ψ z = 1) ∧
      (∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 →
        (carrierParameters (v, t), T.reference.spatialPatch (carrierParameters (v, t))) ∈
          closedBall (z₀, T.reference.spatialPatch z₀) (ρ / 4) ∧
        carrierParameters (v, t) ∈ parameterInterior (3 * P.radius / 2) ∧
        t ∈ closedBall (z₀ 0) r ∧ v ∈ closedBall (spectatorCenter z₀) (s / 2)) ∧
    ∀ (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ),
      (∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) →
      (∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ) →
      ContDiff ℝ ∞ H → (∀ η, 2 ≤ ‖η‖ → H η = 1) →
      amin ≤ (1 / 2) / ‖ηb‖ → 2 / ‖ηb‖ ≤ amax →
      (∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈ closedDirections ηb r) →
    ∀ {K : Set (Euclidean (m + 1))}, IsCompact K → K ⊆ U →
      (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K) →
    ∀ (M : ℝ) {γ κ : ℝ}, 0 < γ → 0 < κ →
    ∃ Cscalar : ℕ → ℝ, (∀ j, 0 < Cscalar j) ∧ ∃ Cmean > (0 : ℝ),
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
      ∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
      ∃ Ns : ℕ → UniformNormalData G Cscalar,
        (∀ j, (Ns j).phase = fun ε x u ↦
          normalizedFullPhase T Q v ε x (RawKernel.canonicalInputCoordinates T u)) ∧
        (∀ j, (Ns j).amplitude = fun ε x u ↦
          (scalarNormalizedAmplitude T χ ψ angular H j (ε, v, x, u)).ofLp) ∧
        ∀ (J : ℕ) (ε : Fin J → ℝ), (∀ j, ε j ∈ Icc 0 G.ε₀) →
          ‖∑ j : Fin J, ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).comp
            ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).adjoint‖ ≤ Cmean := by
  intro ηb
  obtain ⟨rg, hrg, hrgcap, sg, hsg, _hsgr, eg, heg, hegcap, δg, hδg, γg, hγg, hgap⟩ :=
    LiteralMeanBound.exists_uniformNormalData_supported_gap T hP hz₀ hk hinc hd
      hrmax hemax hamin hamax
  obtain ⟨r, hr, hrcap, s, hs, hsr, δp, hδp, hδpcap, Mphase, _hMphase, G,
    he, _hX, hX₀, hD₀, hD, _hDclosure, hXcap, _hext, hbudgets⟩ :=
    exists_uniform_literalFullPhaseNormalData_before_immersion_bounds T hP hz₀ hk hinc hd
      (lt_min hrg hsg) heg (lt_min hxmax (by positivity : 0 < sg / 2))
      hamin hamax
  let δ := min δp δg
  have hδ : 0 < δ := lt_min hδp hδg
  have hδcap : δ ≤ T.family.threshold := (min_le_left _ _).trans hδpcap
  have hrrg : r ≤ rg := hrcap.trans (min_le_left _ _)
  have hssg : s ≤ sg := hsr.trans (hrcap.trans (min_le_right _ _))
  have hXgap : G.X₀ ⊆ closedBall 0 (sg / 2) :=
    hXcap.trans ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall)
  have hDgap : RawKernel.canonicalInputCoordinates T '' G.D₀ ⊆
      (fun q : ℝ × Euclidean (m + 1) ↦ radialInput T q.1 q.2) ''
        (Icc amin amax ×ˢ normalizedInputCore T z₀ ηb rg) := by
    rw [hD]
    apply image_mono
    apply prod_mono (Subset.refl _)
    intro w hw
    exact ⟨closedBall_subset_closedBall hrrg hw.1, closedBall_subset_closedBall hrrg hw.2⟩
  obtain ⟨χ, _hχρ, _hχs, hχplateau, hχcore⟩ :=
    exists_retained_physical_cutoff (n := m + 1) hρ hs
  have hχX : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ G.X₀ := by
    rwa [hX₀]
  obtain ⟨d, hdpos, ψ, B, hB, hψsmooth, hψcompact, hψbounds, hψone, hψsupport, _hψbuffer⟩ :=
    exists_retained_carrier_cutoff_buffered T hP hz₀ hρ hr hs
  refine ⟨r, s, δ, hr, hrrg.trans hrgcap, hs, hsr, hδ, hδcap, G,
    he.trans hegcap, hXcap.trans (ball_subset_ball (min_le_left _ _)), hD₀,
    χ, hχplateau, hχX, d, hdpos, ψ, B, hB, hψsmooth, hψcompact,
    hψbounds, hψone, hψsupport, ?_⟩
  intro angular H ha hah hH hH₁ hlo hhi hangle K hK hKU hball M γ κ hγ hκ
  obtain ⟨Cphase, hCphase, hgeometry⟩ := hbudgets hK hKU hball M hγ hκ
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨A, hA, hscalar⟩ := exists_scalarNormalData T χ ψ hψsmooth angular H ha hah hH hH₁
    G Cphase (isCompact_closedBall (spectatorCenter z₀) (s / 2)) hηb hr hlo hhi hangle hχX
    (fun v _ t hn ↦ (hψsupport t v hn).2.2.1) hD₀
  obtain ⟨Cmean, hCmean, hsum⟩ := exists_uniform_powTwoNormal_bound G
    (fun j ↦ Cphase j + A j) hγg
  refine ⟨fun j ↦ Cphase j + A j, fun j ↦ add_pos (hCphase j) (hA j),
    Cmean, hCmean, ?_⟩
  intro F hF hi hrank hFM hmetric hnormal hclose
  obtain ⟨hlow, hN₀⟩ := hgeometry F hF hi hrank hFM hmetric hnormal
    (hclose.trans_le (min_le_left _ _))
  refine ⟨hlow, ?_⟩
  intro Q v hv
  obtain ⟨N₀, hNphase, _hNamp, _hNparameter, hNdomain⟩ := hN₀ v hv
  choose Ns hNp _hNpar _hNd hNa using fun j ↦ hscalar v hv j N₀ Mphase hNdomain
  have hNsphase (j : ℕ) := (hNp j).trans hNphase
  refine ⟨Ns, hNsphase, hNa, ?_⟩
  intro J ε hε
  apply hsum J (fun j ↦ Ns j.val) ε hε
  intro j
  exact (hgap Q (hclose.trans_le (min_le_right _ _)) (m + 1) G
    (fun j ↦ Cphase j + A j) (Ns j.val) v
    (closedBall_subset_closedBall (by linarith only [hssg]) hv)
    hXgap hDgap he (by intro ε' _ u _ x _; rw [hNsphase]) (ε j) (hε j)).1

end JanetCartan.PhysicalSampling
