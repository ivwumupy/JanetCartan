module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.CommonBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.PointwiseRealization

/-!
# Local choices before selecting the finite family

For `app:ch_waves:thm:sampling`, construct all local geometry and analytic
bounds first, on an arbitrary index type. Any finite subfamily can then use
those SAME radii, cutoffs and kernels. This order permits compactness to select
a cone cover after the local constructors return their radii. Reapplying a
local existential constructor after selection would not preserve that cover.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open RawKernel RawPrimary LeadingWave LeadingWave.FullModulation ProjectedStressFrame
open AmbientResponse ResponseTransfer ContinuumRow ContinuumRow.CanonicalConic
open FullNormalGeometry FullNormalGeometry.PhaseJets NormalComparison
open MeanNormalBound.CanonicalGap MeanNormalBound
open SamplingKernelBounds RawInputPartition SeparatedSampling Realization ColoredNormalComparison
open LatticeQuadrature BackgroundQuadrature

/-- Construct local sampling choices before selecting a finite subfamily.
The original profiles and retained raw outputs imply all three operator bounds
and one event for every selected finite subfamily. The selected subfamily never
changes the local radii or masks (`app:ch_waves:thm:sampling`). -/
theorem exists_indexed_retained_sampling_realization
    {A V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {m : ℕ} (hdim : 1 ≤ m) (P : A → Patch (m + 1))
    {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : ∀ a, PatchQuantitativeFamily (P a) U hU)
    {c C : A → ℝ} (hP : ∀ a, (P a).IsValid (c a) (C a))
    (z₀ : A → Euclidean 3) (hz₀ : ∀ a, z₀ a ∈ parameterInterior (P a).radius)
    (k : A → Euclidean (m + 1)) (hk : ∀ a, k a ≠ 0)
    (hinc : ∀ a, incidence (k a) ((P a).toFun (z₀ a)) = 0)
    (hd : ∀ a, fderiv ℝ (fun z ↦ incidence (k a) ((P a).toFun z)) (z₀ a)
      (EuclideanSpace.single 0 1) ≠ 0)
    {ρ rmax emax xmax amin amax : A → ℝ}
    (hρ : ∀ a, 0 < ρ a) (hrmax : ∀ a, 0 < rmax a)
    (hemax : ∀ a, 0 < emax a) (hxmax : ∀ a, 0 < xmax a)
    (hamin : ∀ a, 0 < amin a) (hamax : ∀ a, amin a ≤ amax a)
    {K : Set (Euclidean (m + 1))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ a, closedBall (0 : Euclidean (m + 1))
      (T a).data.localReference.stateRadius ⊆ K)
    (hspace : ∀ a, closedBall (0 : Euclidean (m + 1)) (2 * ρ a) ⊆ K)
    (hphase : ∀ a, closedBall ((0 : Euclidean (m + 1)),
      (z₀ a, (T a).reference.spatialPatch (z₀ a))) (2 * ρ a) ⊆ domain (T a))
    (hcarrier : ∀ a, closedBall (z₀ a) (2 * ρ a) ⊆ parameterInterior (2 * (P a).radius))
    (I : A → Set (Euclidean (m + 1 - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF : ℕ → ℝ) (Ar E Γ : A → ℕ → ℝ)
    (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ a j, 0 ≤ Ar a j)
    (hE : ∀ a j, 0 < E a j) (hΓ : ∀ a j, 0 < Γ a j)
    (measurement : A → Euclidean (m + 1) →
      Matrix (Fin (embeddingDimension (m + 1))) (Fin (m + 1)) ℂ →L[ℂ]
        EuclideanSpace ℂ (Fin (m + 1)))
    (hm : ∀ a, ContDiffOn ℝ ∞ (measurement a) U) :
    let center := fun a ↦ ((0 : Euclidean (m + 1)),
      (z₀ a, (T a).reference.spatialPatch (z₀ a)))
    let ηb := fun a ↦ (T a).data.adapted.embedding.toContinuousLinearMap.adjoint (k a)
    ∃ r s δ : A → ℝ, (∀ a, 0 < r a ∧ r a ≤ rmax a ∧
      0 < s a ∧ s a ≤ r a ∧ 0 < δ a ∧ δ a ≤ (T a).family.threshold) ∧
    ∃ G : A → UniformNormalGeometry (m + 1) (m + 1),
      (∀ a, (G a).ε₀ ≤ emax a ∧ (G a).ε₀ ≤ 1 ∧ (G a).ε₀ ≤ ρ a / 8 ∧
        (G a).X = ball 0 (s a / 2) ∧ (G a).X₀ = closedBall 0 (s a / 4) ∧
        (G a).D₀ = radialSamplingSupport (T a) (z₀ a) (ηb a) (r a) (amin a) (amax a) ∧
        canonicalInputCoordinates (T a) '' (G a).D₀ =
          (fun q : ℝ × Euclidean (m + 1) ↦ radialInput (T a) q.1 q.2) ''
            (Icc (amin a) (amax a) ×ˢ normalizedInputCore (T a) (z₀ a) (ηb a) (r a)) ∧
        (G a).X₀ ⊆ ball 0 (xmax a)) ∧
    ∃ χ : A → ContDiffBump (0 : Euclidean (m + 1)),
      (∀ a, Function.support (χ a : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (ρ a / 2) ∧
        Function.support (χ a : Euclidean (m + 1) → ℝ) ⊆ (G a).X₀) ∧
    ∃ d B : A → ℝ, ∃ ψ : A → Point → ℝ,
      (∀ a, 0 < d a ∧ 0 < B a ∧ ContDiff ℝ ∞ (ψ a) ∧ HasCompactSupport (ψ a) ∧
        PatchBounds (ψ a) (B a) 1 ∧
        (∀ z, WithLp.toLp 2 z ∈ closedBall (z₀ a) (d a) → ψ a z = 1) ∧
        (∀ t v, ψ a (carrierSamplingEquiv (t, v)) ≠ 0 →
          (carrierParameters (v, t), (T a).reference.spatialPatch (carrierParameters (v, t))) ∈
            closedBall (center a).2 (ρ a / 4) ∧
          carrierParameters (v, t) ∈ parameterInterior (3 * (P a).radius / 2) ∧
          t ∈ closedBall (z₀ a 0) (r a) ∧ v ∈ closedBall (spectatorCenter (z₀ a)) (s a / 2)) ∧
        (∀ z, ψ a z ≠ 0 → WithLp.toLp 2 z ∈ parameterCube (P a).radius ∧
          (WithLp.toLp 2 z, (T a).reference.spatialPatch (WithLp.toLp 2 z)) ∈
            ball (center a).2 (ρ a / 4))) ∧
    ∀ indices : Finset A,
    let T := fun a : indices ↦ T a.1
    let ρ := fun a : indices ↦ ρ a.1
    let amin := fun a : indices ↦ amin a.1
    let amax := fun a : indices ↦ amax a.1
    let hP := fun a : indices ↦ hP a.1
    let hρ := fun a : indices ↦ hρ a.1
    let I := fun a : indices ↦ I a.1
    let Ar := fun a : indices ↦ Ar a.1
    let E := fun a : indices ↦ E a.1
    let Γ := fun a : indices ↦ Γ a.1
    let measurement := fun a : indices ↦ measurement a.1
    let center := fun a : indices ↦ center a.1
    let ηb := fun a : indices ↦ ηb a.1
    let r := fun a : indices ↦ r a.1
    let δ := fun a : indices ↦ δ a.1
    let G := fun a : indices ↦ G a.1
    let χ := fun a : indices ↦ χ a.1
    let ψ := fun a : indices ↦ ψ a.1
    ∀ (angular : indices → Euclidean (m + 1 - 1) → ℂ)
      (highPass : indices → Euclidean (m + 1 - 1) → ℝ),
      (∀ a θ, θ ≠ 0 → ContDiffAt ℝ ∞ (angular a) θ) →
      (∀ a (t : ℝ), 0 < t → ∀ θ, angular a (t • θ) = angular a θ) →
      (∀ a, ContDiff ℝ ∞ (highPass a)) →
      (∀ a η, ‖η‖ ≤ 1 → highPass a η = 0) →
      (∀ a η, 2 ≤ ‖η‖ → highPass a η = 1) →
      (∀ a, amin a ≤ (1 / 2) / ‖ηb a‖) → (∀ a, 2 / ‖ηb a‖ ≤ amax a) →
      (∀ a θ, angular a θ ≠ 0 → NormedSpace.normalize θ ∈
        closedDirections (n := m + 1) (ηb a) (r a)) →
    ∀ (p : ℕ), 0 < p →
    ∀ (mollifier : ℝ → ℝ), HasCompactSupport mollifier → ContDiff ℝ ∞ mollifier →
      (∫ t, mollifier t = 1) → (∀ t, 0 ≤ mollifier t) →
      Function.support mollifier ⊆ Icc (-(1 / 4)) (1 / 4) →
    ∀ (φ : indices → Point → ℝ) (Bφ : ℝ) (Pφ : indices → ℝ),
      (∀ a, PatchBounds (φ a) Bφ (Pφ a)) → (∀ a, Continuous (φ a)) →
      (∀ a z, φ a z ≠ 0 → ψ a z = 1) →
    ∀ ε : ℝ, 0 < ε → ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ ≥ Λ₀,
      ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      (∀ a, cNorm (closedBall (0 : Euclidean (m + 1)) (T a).data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ a) →
      ∀ hlow : ∀ a, cNorm (closedBall (0 : Euclidean (m + 1))
        (T a).data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < (T a).family.threshold,
      let Q := fun a ↦ ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow a⟩
      ∀ (row col : indices → Fin (m + 1))
        (Φ Y : indices → ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
          Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
        (scalar : indices → Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
        (Ω : indices → Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))),
      (∀ a, IsOpen (Ω a)) → (∀ a, closedBall (center a) (2 * ρ a) ⊆ Ω a) →
      (∀ a, ContDiffOn ℝ ∞ (fullLeadingCovector (T a) (Q a) F (row a) (col a)
        (Φ a) (Y a) (scalar a)) (Ω a)) →
      (∀ a, ContDiffOn ℝ ∞ (fullCorrectionCovector (T a) (Q a) F (row a) (col a)
        (Φ a) (Y a) (scalar a)) (Ω a)) →
      (∀ a j,
        let J := closedBall (center a) (ρ a)
        let b₀ := fullLeadingCovector (T a) (Q a) F (row a) (col a) (Φ a) (Y a) (scalar a)
        let ξ := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) ↦
          phaseGradient (T a) (Q a) w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase (T a) (Q a) w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E a j * (1 + cNorm K (j + 14) F + cNorm (I a) (j + 14) (scalar a))) →
      (∀ a j, cNorm (closedBall (center a) (ρ a)) j
        (fullCorrectionCovector (T a) (Q a) F (row a) (col a) (Φ a) (Y a) (scalar a)) ≤
          Γ a j * (1 + cNorm K (j + 14) F + cNorm (I a) (j + 14) (scalar a))) →
      ∀ (RF Rr : ℕ) (L : ℝ), 1 ≤ L →
      20 * ((m + 1) + 1) + 17 ≤ RF → 20 * ((m + 1) + 1) + 17 ≤ Rr →
      HasDerivativeProfile K F RF L AF →
      (∀ a, HasDerivativeProfile (I a) (scalar a) Rr L (Ar a)) →
      ∀ (τ : indices → (Fin 3 → Fin (p + 1)) → ℝ),
        (∀ a color, τ a color ∈ Icc (-1 : ℝ) 1) → (∀ a color, τ a color ≠ 0) →
        (∀ a color (j : Fin (cutoffCount Λ)), |τ a color| * (2 : ℝ) ^ j.val ≤
          measuredPhaseRadius (T a) (hP a) (ρ := ρ a)) →
        (∀ a color (j : Fin (cutoffCount Λ)),
          τ a color * (2 : ℝ) ^ j.val ∈ Icc 0 (G a).ε₀) →
      ∃ D : indices → BandKernelData
        (Fin (cutoffCount Λ) × ((Fin 3 → Fin (p + 1)) × Point)) (m + 1),
        (∀ a, (D a).mask = MaskProfiles.detectorMask (angular a) (highPass a) ∧
          (D a).phase = (fun q ↦ rawPrimaryPhaseDifference (extendedRetainedPhase (T a) (Q a))
            (extendedRetainedCarrier (T a) (center a).2.1 (hρ a) (WithLp.toLp 2 q.1.1.2.2))
            (τ a q.1.1.2.1) q.2 q.1.2) ∧
          (D a).amplitude = measuredBandAmplitude
            (fun q ↦ supportedMeasuredDerivativePolynomial (T a) (Q a) F (row a) (col a)
              (Φ a) (Y a) (scalar a) (measurement a) (χ a)
              (center a) (hρ a) (τ a q.1) (WithLp.toLp 2 q.2))
            (fun q ↦ extendedRetainedCarrier (T a) (center a).2.1 (hρ a) (WithLp.toLp 2 q.2))
            (fun q ↦ τ a q.1) ∧
          (∀ (j : Fin (cutoffCount Λ)) (color : Fin 3 → Fin (p + 1)) (z : Point),
            ψ a z ≠ 0 → ∀ (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)),
              (D a).kernel (j, (color, z)) η x =
                ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
                  ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand
                    (MaskProfiles.detectorMask (angular a) (highPass a)) j.val η) •
                    (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (phase (T a) (Q a))
                      ((T a).reference.spatialPatch (WithLp.toLp 2 z)) (τ a color) x η : ℂ)) •
                      fullMeasuredDerivativePolynomial (T a) (Q a) F (row a) (col a)
                        (Φ a) (Y a) (scalar a) (measurement a) (χ a)
                        (τ a color) (WithLp.toLp 2 z) x
                        ((T a).reference.spatialPatch (WithLp.toLp 2 z) + (τ a color) • η)))) ∧
        ∃ ξ : indices → ShiftSpace p Bφ (samplingMesh ε Λ),
          (∀ a q i, 0 ≤ extendedShift (ξ a) q i ∧
            extendedShift (ξ a) q i < samplingMesh ε Λ) ∧
          (∀ L ≤ cutoffCount Λ,
            ‖familyDeviation p Bφ φ (convolvedBoxWindow mollifier p)
              (samplingMesh ε Λ) (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤
                samplingTolerance ε Λ) ∧
          (∀ L ≤ cutoffCount Λ,
            ‖(4 : ℝ) • realOutputCompression
              (familyDeviation p Bφ φ (convolvedBoxWindow mollifier p)
                (samplingMesh ε Λ) (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ)‖ ≤
                  4 * samplingTolerance ε Λ) ∧
          (∀ a, SampleGeometry p Bφ (Pφ a) 1 (φ a) (convolvedBoxWindow mollifier p)
            (samplingMesh ε Λ) (extendedShift (ξ a))) ∧
          (∀ (H : indices → (Fin 3 → Fin (p + 1)) → Point → V) (Qbg : indices → ℝ),
            (∀ a c, ContDiff ℝ p (fun z ↦ φ a z • H a c z)) →
            (∀ a, 0 ≤ Qbg a) →
            (∀ a c z, ‖iteratedFDeriv ℝ p (fun z ↦ φ a z • H a c z) z‖ ≤ Qbg a) →
            ‖familyBackgroundError p Bφ φ (convolvedBoxWindow mollifier p)
              (samplingMesh ε Λ) (fun a ↦ extendedShift (ξ a)) H‖ ≤
                backgroundQuadratureConstant p Bφ * (∑ a, Qbg a) * samplingMesh ε Λ ^ p) := by
  classical
  intro center ηb
  choose r hr hrr s hs hsr δ hδ hδT G hGe hGeone hGeρ hX hX₀ hD₀ hD hXmax
    χ hχρ hχX d hdpos ψ B hB hψ hψc hψb hψone hψsupport hψbuffer hcommon using
    fun a ↦ exists_full_retained_measuredKernel_bounds hdim (T a) (hP a) (hz₀ a)
      (hk a) (hinc a) (hd a) (hρ a) (hrmax a) (hemax a) (hxmax a) (hamin a) (hamax a)
      hK hKU (hball a) (hspace a) (hphase a) (hcarrier a) (I a)
      hγ hκ AF (Ar a) (E a) (Γ a) hAF (hAr a) (hE a) (hΓ a) (measurement a) (hm a)
  refine ⟨r, s, δ, fun a ↦ ⟨hr a, hrr a, hs a, hsr a, hδ a, hδT a⟩,
    G, fun a ↦ ⟨hGe a, hGeone a, hGeρ a, hX a, hX₀ a, hD₀ a, hD a, hXmax a⟩,
    χ, fun a ↦ ⟨hχρ a, hχX a⟩, d, B, ψ,
    fun a ↦ ⟨hdpos a, hB a, hψ a, hψc a, hψb a, hψone a, hψsupport a, hψbuffer a⟩, ?_⟩
  intro indices T ρ amin amax hP hρ I Ar E Γ measurement center ηb r δ G χ ψ
    angular highPass ha hah hH hH₀ hH₁ hlo hhi hangle
  choose Cnormal hCnormal Cmean hCmean Ckernel hCkernel Cband hCband hfamily using
    fun a : indices ↦ hcommon a.1 (angular a) (highPass a) (ha a) (hah a) (hH a) (hH₀ a)
      (hH₁ a) (hlo a) (hhi a) (hangle a)
  intro p hp mollifier hmc hms hmm hmp hmsupp φ Bφ Pφ hφ hφc hplateau ε hε
  let Ccolored := fun a ↦ ‖Pφ a‖ * ∑ _color : Fin 3 → Fin (p + 1),
    Cmean a * volume.real (closedBall (0 : Euclidean 2) (2 * B a))
  obtain ⟨Λ₀, hΛ₀, hsample⟩ := exists_uniform_refinedKernelPrefix_threshold_of_support
    (A := indices) (n := m + 1) (p := p) (V := V)
    (C_mean := ∑ a, Ccolored a) (C_op := ∑ a, Cband a)
    (by omega) hmc hms hmm hmp hmsupp hp hφ hφc hε hCkernel
    (Finset.sum_nonneg fun a _ ↦ hCband a)
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ F hF hi hrank hmetric hnormal hclose hlow Q row col Φ Y scalar Ω
    hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr L hL hRF hRr hpF hpr τ hτ hτ₀ hscale hεscale
  have hactual (a : indices) := (hfamily a F hF hi hrank hmetric hnormal (hclose a) (hlow a)
    (row a) (col a) (Φ a) (Y a) (scalar a) (Ω a) (hΩ a) (hflow a)
    (hb₀ a) (hb₁ a) (hleading a) (hcorrection a) RF Rr L hL hRF hRr hpF (hpr a)).2
      p (cutoffCount Λ) (τ a) (hτ a) (hτ₀ a) (hscale a) (hεscale a)
  choose D hDkernel hDmask hDphase hDamp hDliteral hDband hDmean using hactual
  have hΛpos : 0 < Λ := zero_lt_one.trans_le (hΛ₀.trans hΛ)
  have hh : 0 < samplingMesh ε Λ := Real.rpow_pos_of_pos hΛpos _
  have hw := convolvedBoxWindow_bounds (hms.continuous.integrable_of_hasCompactSupport hmc)
    hmm hmp hmsupp hp
  have hwc := (contDiff_convolvedBoxWindow hmc hms p).continuous
  have hmean (a : indices) := (hDmean a (φ a) Bφ (Pφ a) (hφ a) (hφc a) (hplateau a)
    (convolvedBoxWindow mollifier p) hw hwc (samplingMesh ε Λ) hh.ne').1
  obtain ⟨ξ, hξ, hprefix, hgeometry, hbackground⟩ :=
    hsample Λ hΛ D (fun a ↦ (hDkernel a).le)
      (fun a i color z hz ↦ (hDband a i color z (by
        change ψ a z ≠ 0
        rw [hplateau a z hz]
        exact one_ne_zero)).trans (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun b _ ↦ hCband b) (Finset.mem_univ a))
          (refinedRadius_pos i).le))
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ ↦ hmean a))
  refine ⟨D, fun a ↦ ⟨hDmask a, hDphase a, hDamp a, hDliteral a⟩,
    ξ, hξ, hprefix, ?_, hgeometry, hbackground⟩
  intro L hL'
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  exact mul_le_mul_of_nonneg_left
    ((realOutputCompression_norm_le _).trans (hprefix L hL')) (by norm_num)

end JanetCartan.Sampling.MeasuredAmplitude
