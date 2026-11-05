module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.FullNormalData
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.UniformBandBounds

/-!
# Common measured kernel, sharp bands and colored mean

Choose the raw slice cutoff first, then the full normal geometry inside its
plateau. Both estimates concern the same measured polynomial and the same
original detector. Kernel equality transfers the sharp bound without identifying
separately chosen existential kernel records. The carrier cutoff has a positive
plateau in the original parameter cube and a strict retained graph buffer.

This closes the three local analytic estimates consumed by the support-local
sampling realization theorem. Finite angular coverage, the actual retained
family application, background estimates and colored comparison are still
separate obligations of `app:ch_waves:thm:sampling`.
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

/-- Pointwise equality of the literal kernels identifies their annular
operators on the original Lebesgue spaces. Bounds and support witnesses in the
kernel records need not agree (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem bandOperator_eq_of_kernel_eq {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P] {n : ℕ}
    (D E : BandKernelData P n) (R : ℝ) (p : P)
    (h : ∀ η x, D.kernel p η x = E.kernel p η x) :
    D.operator R p = E.operator R p := by
  have hc (η : Euclidean (n - 1)) : D.column p η = E.column p η := by
    apply Lp.ext
    filter_upwards [D.column_coe p η, E.column_coe p η] with x hx hy
    exact hx.trans ((h η x).trans hy.symm)
  apply ContinuousLinearMap.ext
  intro f
  simp only [BandKernelData.operator_apply, hc]

/-- One common choice of physical, carrier and angular localization yields
all THREE actual local sampling estimates: a uniform squared-kernel constant,
the sharp restricted-band bound at every original scale, and an O(1) colored
mean bound. The raw cutoff is selected before the normal geometry, and angular
masks are selected once after this common geometry. No operator bound, normal
data or successful event is a hypothesis. The leading/correction inputs are
the same retained outputs of `RawPrimary` and the original primitive derivative
profiles (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_full_retained_measuredKernel_bounds
    {m : ℕ} (hdim : 1 ≤ m) {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
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
    ∃ Ckernel ≥ (0 : ℝ), ∃ Cband ≥ (0 : ℝ),
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
        (∀ (i : RefinedIndex J) (color : Fin 3 → Fin (p + 1)) (z : Point),
          ψ z ≠ 0 → ‖D.operator (refinedRadius i) (i.1, (color, z))‖ ^ 2 ≤
            Cband * refinedRadius i) ∧
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
  obtain ⟨aslice, bslice, eslice, δslice, has, hbs, hes, hδs,
    hascap, hbscap, hebs, hδscap, θ, hθ, hθc, hθone, hθsupport, hsharp⟩ :=
    exists_uniform_retained_measuredBand_bound hdim hP T z₀
      (T.reference.spatialPatch z₀) hρ hK hKU hball hγ hκ I
      AF Ar E Γ hAF hAr hE hΓ
  obtain ⟨r, hr, hrr, s, hs, hsr, δnormal, hδn, hδnT, G, hGe,
    hGeone, hGeρ, hX, hX₀, hD₀, hD, hXmax, χ, hχρ, hχX, d, hdpos, ψ, B, hB,
    hψ, hψc, hψb, hψone, hψsupport, hψbuffer, hnormal⟩ :=
    exists_full_retained_measuredKernel_mean_buffered T hP hz₀ hk hinc hd hρ
      hrmax (lt_min hemax (by positivity : 0 < eslice / 2))
      (lt_min hxmax (by positivity : 0 < aslice / 8)) hamin hamax
      hK hKU hball hspace hphase hcarrier I hγ hκ AF Ar E Γ hAF hAr hE hΓ measurement hm
  have hχslice : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆
      closedBall 0 (aslice / 8) :=
    hχX.trans (hXmax.trans ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall))
  have hχone : ∀ x, |(χ : Euclidean (m + 1) → ℝ) x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg χ.nonneg]
    exact χ.le_one
  obtain ⟨Mmeasurement, hMmeasurement⟩ := (isCompact_closedBall (0 : Euclidean (m+1))
    (ρ / 2)).exists_bound_of_continuousOn
      (hm.continuousOn.mono ((closedBall_subset_closedBall (by linarith : ρ / 2 ≤ 2 * ρ)).trans
        (hspace.trans hKU)))
  let Cmeasurement := max 0 Mmeasurement
  have hCmeasurement : 0 ≤ Cmeasurement := le_max_left _ _
  have hmeasurement : ∀ x ∈ closedBall (0 : Euclidean (m+1)) (ρ / 2),
      ‖measurement x‖ ≤ Cmeasurement :=
    fun x hx ↦ (hMmeasurement x hx).trans (le_max_right _ _)
  obtain ⟨Apoly, hApoly, hpoly⟩ := exists_retained_measuredPolynomial_budgets
    T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ
    χ measurement χ.contDiff.contDiffOn hm
  refine ⟨r, hr, hrr, s, hs, hsr, min δnormal δslice, lt_min hδn hδs,
    (min_le_left _ _).trans hδnT, G, hGe.trans (min_le_left _ _), hGeone, hGeρ,
    hX, hX₀, hD₀, hD, hXmax.trans (ball_subset_ball (min_le_left _ _)),
    χ, hχρ, hχX, d, hdpos, ψ, B, hB, hψ, hψc, hψb, hψone, hψsupport, hψbuffer, ?_⟩
  intro angular highPass ha hah hH hH₀ hH₁ hlo hhi hangle
  obtain ⟨Cnormal, hCnormal, Cmean, hCmean, Ckernel, hCkernel, hfamily⟩ :=
    hnormal angular highPass ha hah hH hH₀ hH₁ hlo hhi hangle
  obtain ⟨Cband, hCband, hband⟩ := hsharp angular highPass ha hah hH hH₀ hH₁
    Cmeasurement hCmeasurement
  obtain ⟨Bdet, hBdet, hdet⟩ := MaskProfiles.exists_bound_detectorMask
    angular highPass ha hah hH hH₀ hH₁
  refine ⟨Cnormal, hCnormal, Cmean, hCmean, Ckernel, hCkernel, Cband, hCband, ?_⟩
  intro F hF hi hrank hmetric hnormal hclose hlow Q row col Φ Y scalar Ω
    hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr L hL hRF hRr hpF hpr
  obtain ⟨hNs, hfamily⟩ := hfamily F hF hi hrank hmetric hnormal
    (hclose.trans_le (min_le_left _ _)) hlow row col Φ Y scalar Ω
    hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr L hL hRF hRr hpF hpr
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
  refine ⟨hNs, ?_⟩
  intro p J τ hτ hτ₀ hscale hε
  obtain ⟨D, hDkernel, hDmask, hDphase, hDamp, hDliteral, hDmean⟩ :=
    hfamily p J τ hτ hτ₀ hscale hε
  refine ⟨D, hDkernel, hDmask, hDphase, hDamp, hDliteral, ?_, hDmean⟩
  intro i color z hz
  let D' := retainedMeasuredKernelData (J := J) T Q F row col Φ Y scalar measurement χ a hρ
    hP hcarrier hpolysmooth (Apoly 0) (hApoly 0).le hb angular highPass ha hH hH₀
    Bdet hBdet hdet τ hτ hτ₀
  have heq : D.operator (refinedRadius i) (i.1, (color, z)) =
      D'.operator (refinedRadius i) (i.1, (color, z)) := by
    apply bandOperator_eq_of_kernel_eq
    intro η x
    simp only [BandKernelData.kernel, bandKernel, hDmask, hDphase, hDamp]
    rfl
  rw [heq]
  have hτpos : 0 < τ color := lt_of_le_of_ne
    (nonneg_of_mul_nonneg_left (hε color i.1).1 (pow_pos (by norm_num) _))
    (Ne.symm (hτ₀ color))
  have hwin : 2 * (τ color * (2 : ℝ) ^ i.1.val) ≤ eslice := by
    have hh := (hε color i.1).2.trans (hGe.trans (min_le_right _ _))
    linarith
  have hbound := hband F hF hi hrank hmetric hnormal
    (hclose.trans_le (min_le_right _ _)) hlow hspace hphase
    (WithLp.toLp 2 z) (hψbuffer z hz).1 (hψbuffer z hz).2
    row col Φ Y scalar Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr L hL
    hRF hRr hpF hpr measurement χ hmeasurement hχslice hχone
    hcarrier hpolysmooth (Apoly 0) (hApoly 0).le hb Bdet hBdet hdet
    p J τ hτ hτ₀ color i.1 hτpos hwin
  exact hbound.2 i.2

end JanetCartan.Sampling.MeasuredAmplitude
