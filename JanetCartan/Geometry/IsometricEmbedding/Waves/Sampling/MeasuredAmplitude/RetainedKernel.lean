module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.KernelConstruction

/-!
# Constructing the actual kernel from the retained polynomial producer

The coefficient bound and smoothness used by `retainedMeasuredKernelData`
are discharged here by `exists_retained_measuredPolynomial_budgets`. The
original detector's bound is proved from its smoothness and homogeneity.
One squared-kernel constant precedes every immersion, history scale, color,
radial label and band ceiling. The conclusion identifies the actual raw kernel,
not an assumed bounded sampling family. The remaining sharp-band and full
normal estimates still need their same-family instantiation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial RawKernel
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer SamplingKernelBounds
open RawPrimary.MaskProfiles RawInputPartition

/-- Construct the SAME actual measured raw kernels with a common squared-kernel
constant, deriving coefficient smoothness and bounds from the retained
reconstruction outputs and original map/scalar profiles. The equations retain
both quadratures, original detector/high-pass, smooth bands, physical Fourier
normalization and full Lebesgue output. All constants precede the varying data;
no kernel bound or successful normal data is assumed
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_retained_measuredKernelFamily
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean (m + 1))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (I : Set (Euclidean ((m + 1) - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (χ : Euclidean (m + 1) → ℝ)
    (measurement : Euclidean (m + 1) → Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (hχ : ContDiffOn ℝ ∞ χ U) (hm : ContDiffOn ℝ ∞ measurement U)
    (hχplateau : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hH : ContDiff ℝ ∞ highPass) (hH₀ : ∀ η, ‖η‖ ≤ 1 → highPass η = 0)
    (hH₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
      ∀ (F : Euclidean (m + 1) → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) →
          Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
        (r : Euclidean ((m + 1) - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      ∀ (RF Rr rpar : ℕ) (L : ℝ), 1 ≤ L →
      14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I r Rr L Ar →
      ∀ (p J : ℕ) (τ : (Fin 3 → Fin (p + 1)) → ℝ),
      (∀ color, τ color ∈ Icc (-1 : ℝ) 1) → (∀ color, τ color ≠ 0) →
      ∃ D : BandKernelData
          (Fin J × ((Fin 3 → Fin (p + 1)) × SeparatedSampling.Point)) (m + 1),
        D.squaredKernelConstant = Ckernel ∧
        D.mask = detectorMask angular highPass ∧
        D.phase = (fun q ↦ rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
          (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.1.1.2.2))
          (τ q.1.1.2.1) q.2 q.1.2) ∧
        D.amplitude = measuredBandAmplitude
          (fun q ↦ supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ
            a hρ (τ q.1) (WithLp.toLp 2 q.2))
          (fun q ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.2))
          (fun q ↦ τ q.1) ∧
        ∀ (j : Fin J) (color : Fin 3 → Fin (p + 1)) (z : SeparatedSampling.Point),
          (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
            closedBall a.2 (ρ / 4) →
          |τ color| * (2 : ℝ) ^ j.val ≤ ρ / 8 →
          ∀ (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)),
            D.kernel (j, (color, z)) η x =
              ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
                ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand
                  (detectorMask angular highPass) j.val η) •
                  (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (phase T Q)
                    (T.reference.spatialPatch (WithLp.toLp 2 z)) (τ color) x η : ℂ)) •
                    fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ
                      (τ color) (WithLp.toLp 2 z) x
                      (T.reference.spatialPatch (WithLp.toLp 2 z) + (τ color) • η)) := by
  obtain ⟨A, hA, hpoly⟩ := exists_retained_measuredPolynomial_budgets (N := N) T a hρ
    hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ χ measurement hχ hm
  obtain ⟨B, hB, hdB⟩ := exists_bound_detectorMask angular highPass ha hah hH hH₀ hH₁
  let Ckernel := volume.real (closedBall a.1 ρ) * B ^ 2 *
    ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) * A 0) ^ 2 *
      RawInputRealization.unitBallVolume (m + 1)
  refine ⟨Ckernel, ?_, ?_⟩
  · dsimp only [Ckernel, RawInputRealization.unitBallVolume]
    positivity
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨_, _, hs, hjets⟩ := hpoly F hF hi hrank hmetric hnormal hlow row col Φ Y r
    Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  have hb (τ : ℝ) (hτ : τ ∈ Icc (-1 : ℝ) 1) (z : Euclidean 3)
      (x : Euclidean (m + 1)) (ξ : Euclidean (m + 1 - 1)) :
      ‖supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
        τ z x ξ‖ ≤ A 0 := by
    simpa only [supportedMeasuredDerivativePolynomial, Q,
      norm_iteratedFDeriv_zero, Nat.zero_sub, pow_zero, mul_one] using
      hjets τ hτ (x, (z, ξ)) 0
  intro p J τ hτ hτ₀
  let D := retainedMeasuredKernelData (J := J) T Q F row col Φ Y r measurement χ a hρ
    hP hcarrier hs (A 0) (hA 0).le hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀
  refine ⟨D, rfl, rfl, rfl, rfl, ?_⟩
  intro j color z hz hscale x η
  exact retainedMeasuredKernelData_kernel_eq_raw_of_bandScale
    T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs (A 0) (hA 0).le hb
    angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχplateau
    j color z hz hscale x η

end JanetCartan.Sampling.MeasuredAmplitude
