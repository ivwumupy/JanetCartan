module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.SupportChoices
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.LiteralMeanBound.FrequencyGap
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.UniformDyadicBound
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.RetainedKernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.RetainedNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.UniformBound

/-!
# One actual measured kernel and its uniform colored mean

Apply the full phase-geometry constructor and insert the retained derivative
polynomial on that very geometry. Actual carrier and physical cutoffs close
all support fields. The fixed high phase budget comes from the SAME original
immersion profile, not from a C14 estimate. No normal data, normalized input
jets, phase chart or operator estimate is an input.

The same construction produces the literal band kernel, a common squared-kernel
constant and the actual `O(1)` colored mean estimate, preserving both real
quadratures and factor four. The canonical gap is derived before applying the
bounded-overlap dyadic estimate; the color masks are removed by positivity.

The remaining reconstruction inputs are precisely the leading and correction
outputs of `RawPrimary.exists_finite_retained_graded_raw_family_with_primitives`.
The finite initialized application still must retain those witnesses, cover
the selected angular support, and supply the original scalar profiles.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open RawKernel RawPrimary LeadingWave LeadingWave.FullModulation ProjectedStressFrame
open AmbientResponse ResponseTransfer ContinuumRow ContinuumRow.CanonicalConic
open FullNormalGeometry FullNormalGeometry.PhaseJets NormalComparison
open MeanNormalBound.CanonicalGap MeanNormalBound
open SamplingKernelBounds RawInputPartition SeparatedSampling Realization ColoredNormalComparison

/-- Construct the SAME nonzero measured normal homotopy, its full radial
geometry and fixed support cutoffs from the original primitive retained
outputs. Every phase/amplitude field, including the epsilon jet, is proved.
The phase constructor and the amplitude constructor share one `G`, one current
frame, one retained scalar and the original immersion profile. The sufficient
map/scalar orders are `20*(n+1)+17`; constants precede fields and band labels.
The literal kernel is then constructed from the SAME measured polynomial;
its kernel constant and colored mean estimate are conclusions. These are the
local `hkernel` and `hmean` inputs of
`exists_threshold_refinedKernelPrefix_realization`. Finite initialized-family
instantiation and the sharp band bound remain separate obligations
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_full_retained_measuredKernel_mean_buffered
    {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {ρ rmax emax xmax amin amax : ℝ} (hρ : 0 < ρ)
    (hrmax : 0 < rmax) (hemax : 0 < emax) (hxmax : 0 < xmax)
    (hamin : 0 < amin) (hamax : amin ≤ amax)
    {K : Set (Euclidean (m + 1))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall (0 : Euclidean (m + 1)) (2 * ρ) ⊆ K)
    (hphase : closedBall ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
      (2 * ρ) ⊆ domain T)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (I : Set (Euclidean (m + 1 - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (measurement : Euclidean (m + 1) →
      Matrix (Fin (embeddingDimension (m + 1))) (Fin (m + 1)) ℂ →L[ℂ]
        EuclideanSpace ℂ (Fin (m + 1)))
    (hm : ContDiffOn ℝ ∞ measurement U) :
    let a := ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∃ G : UniformNormalGeometry (m + 1) (m + 1),
      G.ε₀ ≤ emax ∧ G.ε₀ ≤ 1 ∧ G.ε₀ ≤ ρ / 8 ∧
      G.X = ball 0 (s / 2) ∧ G.X₀ = closedBall 0 (s / 4) ∧
      G.D₀ = radialSamplingSupport T z₀ ηb r amin amax ∧
      canonicalInputCoordinates T '' G.D₀ =
        (fun q : ℝ × Euclidean (m + 1) ↦ MeanNormalBound.CanonicalGap.radialInput T q.1 q.2) ''
          (Icc amin amax ×ˢ MeanNormalBound.CanonicalGap.normalizedInputCore T z₀ ηb r) ∧
      G.X₀ ⊆ ball 0 xmax ∧
    ∃ χ : ContDiffBump (0 : Euclidean (m + 1)),
      Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (ρ / 2) ∧
      Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ G.X₀ ∧
    ∃ d > (0 : ℝ), ∃ ψ : SeparatedSampling.Point → ℝ, ∃ B > (0 : ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ SeparatedSampling.PatchBounds ψ B 1 ∧
      (∀ z, WithLp.toLp 2 z ∈ closedBall z₀ d → ψ z = 1) ∧
      (∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 →
        (carrierParameters (v, t), T.reference.spatialPatch (carrierParameters (v, t))) ∈
          closedBall a.2 (ρ / 4) ∧
        carrierParameters (v, t) ∈ parameterInterior (3 * P.radius / 2) ∧
        t ∈ closedBall (z₀ 0) r ∧ v ∈ closedBall (spectatorCenter z₀) (s / 2)) ∧
      (∀ z, ψ z ≠ 0 → WithLp.toLp 2 z ∈ parameterCube P.radius ∧
        (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈ ball a.2 (ρ / 4)) ∧
    ∀ (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ),
      (∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) →
      (∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ) →
      ContDiff ℝ ∞ highPass → (∀ η, ‖η‖ ≤ 1 → highPass η = 0) →
      (∀ η, 2 ≤ ‖η‖ → highPass η = 1) → amin ≤ (1 / 2) / ‖ηb‖ → 2 / ‖ηb‖ ≤ amax →
      (∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈ closedDirections (n := m + 1) ηb r) →
    ∃ Cnormal : ℕ → ℝ, (∀ j, 0 < Cnormal j) ∧ ∃ Cmean > (0 : ℝ),
    ∃ Ckernel ≥ (0 : ℝ),
      ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ →
      ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
          Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
        (scalar : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y scalar) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y scalar) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y scalar
        let ξ := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) scalar)) →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y scalar) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) scalar)) →
      ∀ (RF Rr : ℕ) (L : ℝ), 1 ≤ L →
      20 * ((m + 1) + 1) + 17 ≤ RF → 20 * ((m + 1) + 1) + 17 ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I scalar Rr L Ar →
      (∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
      ∃ Ns : ℕ → UniformNormalData G Cnormal,
        (∀ j, (Ns j).phase = (fun ε x u ↦ normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))) ∧
        (∀ j, (Ns j).amplitude = (fun ε x u ↦
          (supportedMeasuredNormalAmplitude T Q F row col Φ Y scalar measurement χ a hρ
            angular highPass ψ j v ε x u).ofLp)) ∧
        (∀ j, ∀ ε ∈ Icc 0 G.ε₀, ∀ x u,
          (Ns j).amplitude ε x u =
            (fullMeasuredNormalAmplitude T Q F row col Φ Y scalar measurement χ
              (MaskProfiles.detectorMask angular highPass) ψ j v ε x
                (canonicalInputCoordinates T u)).ofLp) ∧
        ∀ (J : ℕ) (ε : Fin J → ℝ), (∀ j, ε j ∈ Icc 0 G.ε₀) →
          ‖∑ j : Fin J, ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).comp
            ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).adjoint‖ ≤ Cmean) ∧
      ∀ (p J : ℕ) (τ : (Fin 3 → Fin (p + 1)) → ℝ),
        (∀ color, τ color ∈ Icc (-1 : ℝ) 1) → (∀ color, τ color ≠ 0) →
        (∀ color (j : Fin J), |τ color| * (2 : ℝ) ^ j.val ≤
          measuredPhaseRadius T hP (ρ := ρ)) →
        (∀ color (j : Fin J), τ color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀) →
      ∃ D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) (m + 1),
        D.squaredKernelConstant = Ckernel ∧
        D.mask = MaskProfiles.detectorMask angular highPass ∧
        D.phase = (fun q ↦ rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
          (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.1.1.2.2))
          (τ q.1.1.2.1) q.2 q.1.2) ∧
        D.amplitude = measuredBandAmplitude
          (fun q ↦ supportedMeasuredDerivativePolynomial T Q F row col Φ Y scalar measurement χ
            a hρ (τ q.1) (WithLp.toLp 2 q.2))
          (fun q ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.2))
          (fun q ↦ τ q.1) ∧
        (∀ (j : Fin J) (color : Fin 3 → Fin (p + 1)) (z : Point), ψ z ≠ 0 →
          ∀ (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)),
            D.kernel (j, (color, z)) η x =
              ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
                ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand
                  (MaskProfiles.detectorMask angular highPass) j.val η) •
                  (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (phase T Q)
                    (T.reference.spatialPatch (WithLp.toLp 2 z)) (τ color) x η : ℂ)) •
                    fullMeasuredDerivativePolynomial T Q F row col Φ Y scalar measurement χ
                      (τ color) (WithLp.toLp 2 z) x
                      (T.reference.spatialPatch (WithLp.toLp 2 z) + (τ color) • η))) ∧
        ∀ (φ : Point → ℝ) (Bφ Pφ : ℝ), PatchBounds φ Bφ Pφ → Continuous φ →
          (∀ z, φ z ≠ 0 → ψ z = 1) →
        ∀ (w : ℝ → ℝ), WindowBounds p w 1 → Continuous w → ∀ h : ℝ, h ≠ 0 →
        let Emean := patchMeanNormal p Bφ φ w h
          (fun color z ↦ refinedKernelPrefix D J (color, z))
        let Ccolored := ‖Pφ‖ * ∑ _color : Fin 3 → Fin (p + 1),
          Cmean * volume.real (closedBall (0 : Euclidean 2) (2 * B))
        ‖Emean‖ ≤ Ccolored ∧
          ‖(4 : ℝ) • realOutputCompression Emean‖ ≤ 4 * Ccolored := by
  intro a ηb
  let ecap := min emax (min 1 (ρ / 8))
  have hecap : 0 < ecap := lt_min hemax (lt_min zero_lt_one (by positivity))
  obtain ⟨rg, hrg, hrgcap, sg, hsg, _hsgr, eg, heg, hegcap, δg, hδg, γg, hγg, hgap⟩ :=
    LiteralMeanBound.exists_uniformNormalData_supported_gap T hP hz₀ hk hinc hd
      hrmax hecap hamin hamax
  obtain ⟨r, hr, hrcap, s, hs, hsr, δp, hδp, hδpcap, M, hM, G,
    he, hX, hX₀, hD₀, hD, _hDclosure, hXcap, hext, Cphase, hCphase, hgeometry⟩ :=
    exists_uniform_literalFullPhaseNormalData T hP hz₀ hk hinc hd
      (lt_min hrg hsg) heg (lt_min hxmax (by positivity : 0 < sg / 2))
      hamin hamax hK hKU hball (AF (20 * ((m + 1) + 1) + 5)) hγ hκ
  let δ := min δp δg
  have hδ : 0 < δ := lt_min hδp hδg
  have hδcap : δ ≤ T.family.threshold := (min_le_left _ _).trans hδpcap
  have hemax' : G.ε₀ ≤ emax := he.trans (hegcap.trans (min_le_left _ _))
  have heone : G.ε₀ ≤ 1 := he.trans (hegcap.trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have heρ : G.ε₀ ≤ ρ / 8 := he.trans (hegcap.trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hrrg : r ≤ rg := hrcap.trans (min_le_left _ _)
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
  obtain ⟨χ, _hχρ, _hχs, hχplateau, hχcore⟩ :=
    exists_retained_physical_cutoff (n := m + 1) hρ hs
  have hχX : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ G.X₀ := by
    rwa [hX₀]
  obtain ⟨d, hdpos, ψ, B, hB, hψsmooth, hψcompact, hψbounds, hψone, hψsupport, hψbuffer⟩ :=
    exists_retained_carrier_cutoff_buffered T hP hz₀ hρ hr hs
  refine ⟨r, hr, hrrg.trans hrgcap, s, hs, hsr, δ, hδ, hδcap, G, hemax', heone, heρ,
    hX, hX₀, hD₀, hD, hXcap.trans (ball_subset_ball (min_le_left _ _)), χ, hχplateau, hχX,
    d, hdpos, ψ, B, hB, hψsmooth, hψcompact, hψbounds, hψone, hψsupport, hψbuffer, ?_⟩
  intro angular highPass ha hah hH hH₀ hH₁ hlo hhi hangle
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  let V := closedBall (spectatorCenter z₀) (s / 2)
  let S := V ×ˢ (closure G.X ×ˢ closure G.D)
  have hS : IsCompact S := (isCompact_closedBall _ _).prod
    (G.bounded_X.isCompact_closure.prod G.bounded_D.isCompact_closure)
  have hSM : S ⊆ tripleDomain T M := by
    intro q hq
    exact hext q.1 hq.1 hq.2
  obtain ⟨A, hA, hactual⟩ := exists_retained_measuredNormalData T hP M (le_refl (1 : ℝ))
    hS hSM ψ hψsmooth angular highPass ha hah hH hH₁ a hρ hK hKU hball hspace hphase I
    hγ hκ AF Ar E Γ hAF hAr hE hΓ χ measurement χ.contDiff.contDiffOn hm G Cphase V
    (fun v hv w hw ↦ ⟨hv, hw⟩) heone heρ hχplateau
    (fun t v hn ↦ (hψsupport t v hn).1) hηb hr hlo hhi hangle hχX
    (fun v _ t hn ↦ (hψsupport t v hn).2.2.1) hD₀
  obtain ⟨Apoly, hApoly, hpoly⟩ := exists_retained_measuredPolynomial_budgets
    T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ
    χ measurement χ.contDiff.contDiffOn hm
  obtain ⟨Bdet, hBdet, hdet⟩ := MaskProfiles.exists_bound_detectorMask
    angular highPass ha hah hH hH₀ hH₁
  let Ckernel := volume.real (closedBall a.1 ρ) * Bdet ^ 2 *
    ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) * Apoly 0) ^ 2 *
      RawInputRealization.unitBallVolume (m + 1)
  have hCkernel : 0 ≤ Ckernel := by
    dsimp only [Ckernel, RawInputRealization.unitBallVolume]
    positivity
  obtain ⟨Cmean, hCmean, hsum⟩ := MeanNormalBound.exists_uniform_powTwoNormal_bound
    G (fun j ↦ Cphase j + A j) hγg
  refine ⟨fun j ↦ Cphase j + A j, fun j ↦ add_pos (hCphase j) (hA j),
    Cmean, hCmean, Ckernel, hCkernel, ?_⟩
  intro F hF hi hrank hmetric hnormal hclose hlow Q row col Φ Y scalar Ω
    hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr L hL hRF hRr hpF hpr
  have hnormalData : ∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
      ∃ Ns : ℕ → UniformNormalData G (fun j ↦ Cphase j + A j),
        (∀ j, (Ns j).phase = (fun ε x u ↦ normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))) ∧
        (∀ j, (Ns j).amplitude = (fun ε x u ↦
          (supportedMeasuredNormalAmplitude T Q F row col Φ Y scalar measurement χ a hρ
            angular highPass ψ j v ε x u).ofLp)) ∧
        (∀ j, ∀ ε ∈ Icc 0 G.ε₀, ∀ x u,
          (Ns j).amplitude ε x u =
            (fullMeasuredNormalAmplitude T Q F row col Φ Y scalar measurement χ
              (MaskProfiles.detectorMask angular highPass) ψ j v ε x
                (canonicalInputCoordinates T u)).ofLp) ∧
        ∀ (J : ℕ) (ε : Fin J → ℝ), (∀ j, ε j ∈ Icc 0 G.ε₀) →
          ‖∑ j : Fin J, ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).comp
            ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).adjoint‖ ≤ Cmean := by
    intro v hv
    have hFB : cNorm K (20 * ((m + 1) + 1) + 5) F ≤ AF (20 * ((m + 1) + 1) + 5) := by
      have heq : 20 * ((m + 1) + 1) + 5 - RF = 0 := by omega
      simpa only [heq, pow_zero, mul_one] using hpF (20 * ((m + 1) + 1) + 5)
    obtain ⟨hlow', hN₀⟩ := hgeometry F hF hi hrank hFB hmetric hnormal
      (hclose.trans_le (min_le_left _ _))
    obtain ⟨N₀, hNphase, _hNamp, _hNparameter, hNdomain⟩ := hN₀ v hv
    choose Ns hNphase' _hparameter _hdomain hNamp' hliteral using fun j ↦
      hactual F hF hi hrank hmetric hnormal hlow row col Φ Y scalar Ω hΩ hflow hb₀ hb₁
        hleading hcorrection RF Rr (20 * ((m + 1) + 1) + 1) L hL
        (by omega) (by omega) hpF hpr (le_refl _) v hv j N₀ hNdomain
    have hNsphase (j : ℕ) := (hNphase' j).trans hNphase
    refine ⟨Ns, hNsphase, hNamp', hliteral, ?_⟩
    intro J ε hε
    apply hsum J (fun j ↦ Ns j.val) ε hε
    intro j
    exact (hgap Q (hclose.trans_le (min_le_right _ _)) (m + 1) G
      (fun j ↦ Cphase j + A j) (Ns j.val) v
      (closedBall_subset_closedBall (by linarith only [hssg]) hv)
      hXgap hDgap he (by intro ε' _ u _ x _; rw [hNsphase]) (ε j) (hε j)).1

  refine ⟨hnormalData, ?_⟩
  obtain ⟨_, _, hpolysmooth, hpolyjets⟩ :=
    hpoly F hF hi hrank hmetric hnormal hlow row col Φ Y scalar Ω hΩ hflow hb₀ hb₁
      hleading hcorrection RF Rr (20 * ((m + 1) + 1) + 1) L hL
      (by omega) (by omega) hpF hpr
  have hb (τ : ℝ) (hτ : τ ∈ Icc (-1 : ℝ) 1) (z : Euclidean 3)
      (x : Euclidean (m + 1)) (ξ : Euclidean (m + 1 - 1)) :
      ‖supportedMeasuredDerivativePolynomial T Q F row col Φ Y scalar measurement χ a hρ
        τ z x ξ‖ ≤ Apoly 0 := by
    simpa only [supportedMeasuredDerivativePolynomial, Q,
      norm_iteratedFDeriv_zero, Nat.zero_sub, pow_zero, mul_one] using
      hpolyjets τ hτ (x, (z, ξ)) 0
  intro p J τ hτ hτ₀ hscale hε
  let D := retainedMeasuredKernelData (J := J) T Q F row col Φ Y scalar measurement χ a hρ
    hP hcarrier hpolysmooth (Apoly 0) (hApoly 0).le hb angular highPass ha hH hH₀
    Bdet hBdet hdet τ hτ hτ₀
  refine ⟨D, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro j color z hz x η
    obtain ⟨⟨t, v⟩, rfl⟩ := carrierSamplingEquiv.surjective z
    have hτpos : 0 ≤ τ color := nonneg_of_mul_nonneg_left (hε color j).1
      (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    exact retainedMeasuredKernelData_kernel_eq_raw_of_bandScale
      T Q F row col Φ Y scalar measurement χ a hρ hP hcarrier hpolysmooth
      (Apoly 0) (hApoly 0).le hb angular highPass ha hH hH₀ Bdet hBdet hdet
      τ hτ hτ₀ hphase hχplateau j color (carrierSamplingEquiv (t, v))
      (by simpa only [← carrierParameters_eq_sampling] using (hψsupport t v hz).1)
      (by rw [abs_of_nonneg hτpos]; exact (hε color j).2.trans heρ) x η
  intro φ Bφ Pφ hφ hφc hplateau w hw hwc h hh
  dsimp only
  let Op := fun (color : Fin 3 → Fin (p + 1)) (j : Fin J) (v : Euclidean 2) ↦
    fullBandKernelOperator D (fun z ↦ (j, (color, z)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      ψ hψsmooth.continuous j.val B v
  have hslice (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2) :
      ‖∑ j : Fin J, atomNormal (Op color j v)‖ ≤ Cmean := by
    by_cases hv : ∃ t, ψ (carrierSamplingEquiv (t, v)) ≠ 0
    · obtain ⟨t, htv⟩ := hv
      obtain ⟨Ns, hNp, hNa, _hliteral, hNsbound⟩ :=
        hnormalData v (hψsupport t v htv).2.2.2
      have hnormal (j : Fin J) := retainedMeasuredKernelData_normal_eq_uniform
        T Q F row col Φ Y scalar measurement χ a hρ hP hcarrier hpolysmooth
        (Apoly 0) (hApoly 0).le hb angular highPass ha hH hH₀ Bdet hBdet hdet
        τ hτ hτ₀ hphase hχplateau ψ hψbounds hψsmooth.continuous
        (fun t v hn ↦ (hψsupport t v hn).1)
        (fun t v hn ↦ (hψsupport t v hn).2.1)
        j color v (hscale color j) (Ns j.val) (hNp j.val) (hNa j.val) (hε color j)
      have heq : (∑ j : Fin J, atomNormal (Op color j v)) =
          samplingOutputConjugation (m + 1) (∑ j : Fin J,
            ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
              ((τ color) * (2 : ℝ) ^ j.val)).comp
              ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
                ((τ color) * (2 : ℝ) ^ j.val)).adjoint) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun j _ ↦ hnormal j)
      rw [heq, norm_samplingOutputConjugation]
      exact hNsbound J (fun j ↦ τ color * (2 : ℝ) ^ j.val) (hε color)
    · have hz (j : Fin J) : Op color j v = 0 :=
        fullBandKernelOperator_eq_zero_of_cutoff_slice D _ _ ψ hψsmooth.continuous
          j.val B v (by simpa only [not_exists, not_not] using hv)
      simpa only [hz, atomNormal, map_zero, ContinuousLinearMap.zero_comp,
        Finset.sum_const_zero, norm_zero] using hCmean.le
  have hi (color : Fin 3 → Fin (p + 1)) (j : Fin J) :
      Integrable (fun v : Euclidean 2 ↦ atomNormal (Op color j v)) :=
    integrable_fullBandKernelOperator_cutoff_normal D j (fun z ↦ (color, z))
      (continuous_const.prodMk continuous_id) hψbounds hψsmooth.continuous
  have hint (color : Fin 3 → Fin (p + 1)) :
      ‖∑ j : Fin J, ∫ v : Euclidean 2, atomNormal (Op color j v)‖ ≤
        Cmean * volume.real (closedBall (0 : Euclidean 2) (2 * B)) := by
    rw [← integral_finsetSum _ (fun j _ ↦ hi color j)]
    have heq : (∫ v : Euclidean 2, ∑ j : Fin J, atomNormal (Op color j v)) =
        ∫ v in closedBall (0 : Euclidean 2) (2 * B),
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
  have hmean : ‖patchMeanNormal p Bφ φ w h
      (fun color z ↦ refinedKernelPrefix D J (color, z))‖ ≤
      ‖Pφ‖ * ∑ _color : Fin 3 → Fin (p + 1),
        Cmean * volume.real (closedBall (0 : Euclidean 2) (2 * B)) := by
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
  refine ⟨hmean, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  exact mul_le_mul_of_nonneg_left ((realOutputCompression_norm_le _).trans hmean)
    (by norm_num)

/-- Construct the SAME nonzero measured normal homotopy, its full radial
geometry and fixed support cutoffs from the original primitive retained
outputs. Every phase/amplitude field, including the epsilon jet, is proved.
The phase constructor and the amplitude constructor share one `G`, one current
frame, one retained scalar and the original immersion profile. The sufficient
map/scalar orders are `20*(n+1)+17`; constants precede fields and band labels.
The literal kernel is then constructed from the SAME measured polynomial;
its kernel constant and colored mean estimate are conclusions. These are the
local `hkernel` and `hmean` inputs of
`exists_threshold_refinedKernelPrefix_realization`. Finite initialized-family
instantiation and the sharp band bound remain separate obligations
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_full_retained_measuredKernel_mean
    {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {ρ rmax emax xmax amin amax : ℝ} (hρ : 0 < ρ)
    (hrmax : 0 < rmax) (hemax : 0 < emax) (hxmax : 0 < xmax)
    (hamin : 0 < amin) (hamax : amin ≤ amax)
    {K : Set (Euclidean (m + 1))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall (0 : Euclidean (m + 1)) (2 * ρ) ⊆ K)
    (hphase : closedBall ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
      (2 * ρ) ⊆ domain T)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (I : Set (Euclidean (m + 1 - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (measurement : Euclidean (m + 1) →
      Matrix (Fin (embeddingDimension (m + 1))) (Fin (m + 1)) ℂ →L[ℂ]
        EuclideanSpace ℂ (Fin (m + 1)))
    (hm : ContDiffOn ℝ ∞ measurement U) :
    let a := ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∃ G : UniformNormalGeometry (m + 1) (m + 1),
      G.ε₀ ≤ emax ∧ G.ε₀ ≤ 1 ∧ G.ε₀ ≤ ρ / 8 ∧
      G.X = ball 0 (s / 2) ∧ G.X₀ = closedBall 0 (s / 4) ∧
      G.D₀ = radialSamplingSupport T z₀ ηb r amin amax ∧
      canonicalInputCoordinates T '' G.D₀ =
        (fun q : ℝ × Euclidean (m + 1) ↦ MeanNormalBound.CanonicalGap.radialInput T q.1 q.2) ''
          (Icc amin amax ×ˢ MeanNormalBound.CanonicalGap.normalizedInputCore T z₀ ηb r) ∧
      G.X₀ ⊆ ball 0 xmax ∧
    ∃ χ : ContDiffBump (0 : Euclidean (m + 1)),
      Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (ρ / 2) ∧
      Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ G.X₀ ∧
    ∃ d > (0 : ℝ), ∃ ψ : SeparatedSampling.Point → ℝ, ∃ B > (0 : ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ SeparatedSampling.PatchBounds ψ B 1 ∧
      (∀ z, WithLp.toLp 2 z ∈ closedBall z₀ d → ψ z = 1) ∧
      (∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 →
        (carrierParameters (v, t), T.reference.spatialPatch (carrierParameters (v, t))) ∈
          closedBall a.2 (ρ / 4) ∧
        carrierParameters (v, t) ∈ parameterInterior (3 * P.radius / 2) ∧
        t ∈ closedBall (z₀ 0) r ∧ v ∈ closedBall (spectatorCenter z₀) (s / 2)) ∧
    ∀ (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ),
      (∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) →
      (∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ) →
      ContDiff ℝ ∞ highPass → (∀ η, ‖η‖ ≤ 1 → highPass η = 0) →
      (∀ η, 2 ≤ ‖η‖ → highPass η = 1) → amin ≤ (1 / 2) / ‖ηb‖ → 2 / ‖ηb‖ ≤ amax →
      (∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈ closedDirections (n := m + 1) ηb r) →
    ∃ Cnormal : ℕ → ℝ, (∀ j, 0 < Cnormal j) ∧ ∃ Cmean > (0 : ℝ),
    ∃ Ckernel ≥ (0 : ℝ),
      ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ →
      ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
          Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
        (scalar : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y scalar) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y scalar) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y scalar
        let ξ := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) scalar)) →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y scalar) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) scalar)) →
      ∀ (RF Rr : ℕ) (L : ℝ), 1 ≤ L →
      20 * ((m + 1) + 1) + 17 ≤ RF → 20 * ((m + 1) + 1) + 17 ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I scalar Rr L Ar →
      (∀ v ∈ closedBall (spectatorCenter z₀) (s / 2),
      ∃ Ns : ℕ → UniformNormalData G Cnormal,
        (∀ j, (Ns j).phase = (fun ε x u ↦ normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))) ∧
        (∀ j, (Ns j).amplitude = (fun ε x u ↦
          (supportedMeasuredNormalAmplitude T Q F row col Φ Y scalar measurement χ a hρ
            angular highPass ψ j v ε x u).ofLp)) ∧
        (∀ j, ∀ ε ∈ Icc 0 G.ε₀, ∀ x u,
          (Ns j).amplitude ε x u =
            (fullMeasuredNormalAmplitude T Q F row col Φ Y scalar measurement χ
              (MaskProfiles.detectorMask angular highPass) ψ j v ε x
                (canonicalInputCoordinates T u)).ofLp) ∧
        ∀ (J : ℕ) (ε : Fin J → ℝ), (∀ j, ε j ∈ Icc 0 G.ε₀) →
          ‖∑ j : Fin J, ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).comp
            ((Ns j.val).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (ε j)).adjoint‖ ≤ Cmean) ∧
      ∀ (p J : ℕ) (τ : (Fin 3 → Fin (p + 1)) → ℝ),
        (∀ color, τ color ∈ Icc (-1 : ℝ) 1) → (∀ color, τ color ≠ 0) →
        (∀ color (j : Fin J), |τ color| * (2 : ℝ) ^ j.val ≤
          measuredPhaseRadius T hP (ρ := ρ)) →
        (∀ color (j : Fin J), τ color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀) →
      ∃ D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) (m + 1),
        D.squaredKernelConstant = Ckernel ∧
        D.mask = MaskProfiles.detectorMask angular highPass ∧
        D.phase = (fun q ↦ rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
          (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.1.1.2.2))
          (τ q.1.1.2.1) q.2 q.1.2) ∧
        D.amplitude = measuredBandAmplitude
          (fun q ↦ supportedMeasuredDerivativePolynomial T Q F row col Φ Y scalar measurement χ
            a hρ (τ q.1) (WithLp.toLp 2 q.2))
          (fun q ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.2))
          (fun q ↦ τ q.1) ∧
        (∀ (j : Fin J) (color : Fin 3 → Fin (p + 1)) (z : Point), ψ z ≠ 0 →
          ∀ (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)),
            D.kernel (j, (color, z)) η x =
              ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
                ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand
                  (MaskProfiles.detectorMask angular highPass) j.val η) •
                  (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (phase T Q)
                    (T.reference.spatialPatch (WithLp.toLp 2 z)) (τ color) x η : ℂ)) •
                    fullMeasuredDerivativePolynomial T Q F row col Φ Y scalar measurement χ
                      (τ color) (WithLp.toLp 2 z) x
                      (T.reference.spatialPatch (WithLp.toLp 2 z) + (τ color) • η))) ∧
        ∀ (φ : Point → ℝ) (Bφ Pφ : ℝ), PatchBounds φ Bφ Pφ → Continuous φ →
          (∀ z, φ z ≠ 0 → ψ z = 1) →
        ∀ (w : ℝ → ℝ), WindowBounds p w 1 → Continuous w → ∀ h : ℝ, h ≠ 0 →
        let Emean := patchMeanNormal p Bφ φ w h
          (fun color z ↦ refinedKernelPrefix D J (color, z))
        let Ccolored := ‖Pφ‖ * ∑ _color : Fin 3 → Fin (p + 1),
          Cmean * volume.real (closedBall (0 : Euclidean 2) (2 * B))
        ‖Emean‖ ≤ Ccolored ∧
          ‖(4 : ℝ) • realOutputCompression Emean‖ ≤ 4 * Ccolored := by
  obtain ⟨r, hr, hrr, s, hs, hsr, δ, hδ, hδT, G, hemax, heone, heρ,
    hX, hX₀, hD₀, hD, hXmax, χ, hχρ, hχX, d, hd, ψ, B, hB,
    hψ, hψc, hψb, hψone, hψsupport, _hbuffer, hfamily⟩ :=
    exists_full_retained_measuredKernel_mean_buffered T hP hz₀ hk hinc hd hρ
      hrmax hemax hxmax hamin hamax hK hKU hball hspace hphase hcarrier I
      hγ hκ AF Ar E Γ hAF hAr hE hΓ measurement hm
  exact ⟨r, hr, hrr, s, hs, hsr, δ, hδ, hδT, G, hemax, heone, heρ,
    hX, hX₀, hD₀, hD, hXmax, χ, hχρ, hχX, d, hd, ψ, B, hB,
    hψ, hψc, hψb, hψone, hψsupport, hfamily⟩

end JanetCartan.Sampling.MeasuredAmplitude
