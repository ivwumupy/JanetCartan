module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.BandNorm
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FiniteJetSlices.Canonical
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedGrades.Constants

/-!
# Sharp bounds for the actual measured bands at every original scale

Apply the canonical raw slice construction and the actual retained coefficient
producers. Its order-zero branch works at every band scale, even below `L`.
The resulting bound concerns the literal `retainedMeasuredKernelData` and both
of its sharp Hilbert restrictions. Constants and the raw norm cutoff precede
the immersion, scalar, frequency and band count. The sampling measurement can
be chosen inside this cutoff's plateau before the full-normal construction.

The source inputs are the retained leading/correction outputs and the original
immersion/scalar profiles. Kernel smoothness and finite bounds below only
specify the already constructed `BandKernelData`; they are produced by
`exists_full_retained_measuredKernel_mean`, and are not used as sharp operator
bounds. The final finite-family and weighted-event applications remain with
the sampling parent (`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave LeadingWave.FullModulation
open ProjectedStressFrame AmbientResponse ResponseTransfer RawPrimary RawKernel
open RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open RawPrimary.SliceGeometry RawPrimary.SliceBounds NormalComparison SingleChannel
open RawInputPartition SamplingKernelBounds MeanNormalBound

/-- The actual retained measured band satisfies the sharp squared channel
bound at EVERY original `2^j ≥ 1`, with no assumption `L ≤ 2^j`. Its annular
restrictions have the same bound. All analytic slice estimates are derived
from the original primitive profiles and retained coefficient outputs; no
band norm or successful sample is assumed
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_uniform_retained_measuredBand_bound {d : ℕ} (hdim : 1 ≤ d)
    {P : Patch (d + 1)} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (z₀ : Euclidean 3) (ζ₀ : Euclidean d) {σ : ℝ} (hσ : 0 < σ)
    {Kgeom : Set (Euclidean (d + 1))} (hKgeom : IsCompact Kgeom) (hKU : Kgeom ⊆ U)
    (hball : closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius ⊆ Kgeom)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (I : Set (Euclidean d × Euclidean 3))
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j) :
    ∃ a b e δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < e ∧ 0 < δ ∧
      4 * a ≤ σ / 2 ∧ b ≤ σ / 4 ∧ 16 * e < b ∧ δ ≤ T.family.threshold ∧
    ∃ θ : Euclidean (d + 1) → ℝ,
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      EqOn θ 1 (closedBall 0 (a / 8)) ∧ tsupport θ ⊆ closedBall 0 (a / 4) ∧
    ∀ (angular : Euclidean d → ℂ) (H : Euclidean d → ℝ)
      (hang : ∀ η, η ≠ 0 → ContDiffAt ℝ ∞ angular η)
      (_hhom : ∀ t : ℝ, 0 < t → ∀ η, angular (t • η) = angular η)
      (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
      (_hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1),
    ∀ Cmeasurement : ℝ, 0 ≤ Cmeasurement →
    ∃ Cband ≥ (0 : ℝ),
    ∀ (F : Euclidean (d + 1) → Euclidean (embeddingDimension (d + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ Kgeom, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Kgeom, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < δ →
    ∀ hlow : cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < T.family.threshold,
    let Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean (d + 1))
        T.data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress (d + 1)) <
          T.family.threshold} := ⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    closedBall (0 : Euclidean (d+1)) (2 * σ) ⊆ Kgeom →
    closedBall ((0 : Euclidean (d+1)), (z₀, ζ₀)) (2 * σ) ⊆ domain T →
    ∀ z ∈ parameterCube P.radius,
      (z, T.reference.spatialPatch z) ∈ ball (z₀, ζ₀) (σ / 4) →
    ∀ (row col : Fin (d + 1))
      (Φ Y : ℝ × (Euclidean d × (Euclidean 3 × Euclidean d)) →
        Euclidean d × (Euclidean 3 × Euclidean d))
      (r : Euclidean d × Euclidean 3 → ℝ)
      (Ω : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d))),
      IsOpen Ω → closedBall ((0 : Euclidean (d+1)), (z₀, ζ₀)) (2 * σ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j,
        let J := closedBall ((0 : Euclidean (d+1)), (z₀, ζ₀)) σ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm Kgeom (j+14) F + cNorm I (j+14) r)) →
      (∀ j, cNorm (closedBall ((0 : Euclidean (d+1)), (z₀, ζ₀)) σ) j
        (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ j * (1 + cNorm Kgeom (j+14) F + cNorm I (j+14) r)) →
    ∀ (RF Rr : ℕ) (L : ℝ), 1 ≤ L →
      rawSliceJetOrder (d+1) + 17 ≤ RF →
      rawSliceJetOrder (d+1) + 17 ≤ Rr →
      HasDerivativeProfile Kgeom F RF L AF → HasDerivativeProfile I r Rr L Ar →
    ∀ (measurement : Euclidean (d + 1) →
      Matrix (Fin (embeddingDimension (d + 1))) (Fin (d + 1)) ℂ →L[ℂ]
        EuclideanSpace ℂ (Fin (d + 1))) (χ : Euclidean (d + 1) → ℝ),
      (∀ x ∈ closedBall 0 (σ / 2), ‖measurement x‖ ≤ Cmeasurement) →
      Function.support χ ⊆ closedBall 0 (a / 8) → (∀ x, |χ x| ≤ 1) →
    let center := ((0 : Euclidean (d + 1)), (z₀, ζ₀))
    ∀ (hcarrier : closedBall z₀ (2 * σ) ⊆ parameterInterior (2 * P.radius))
      (hs : ContDiff ℝ ∞ (fun q : ℝ × (Euclidean (d + 1) ×
        (Euclidean 3 × Euclidean d)) ↦
          supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ center hσ
            q.1 q.2.2.1 q.2.1 q.2.2.2))
      (M : ℝ) (hM : 0 ≤ M)
      (hb : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x ξ,
        ‖supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ center hσ
          τ z x ξ‖ ≤ M)
      (Bdet : ℝ) (hBdet : 0 ≤ Bdet)
      (hdB : ∀ η, ‖MaskProfiles.detectorMask (n := d+1) angular H η‖ ≤ Bdet)
      (p J : ℕ) (τ : (Fin 3 → Fin (p + 1)) → ℝ)
      (hτ : ∀ color, τ color ∈ Icc (-1 : ℝ) 1)
      (hτ₀ : ∀ color, τ color ≠ 0),
    ∀ (color : Fin 3 → Fin (p + 1)) (j : Fin J),
      0 < τ color → 2 * (τ color * (2 : ℝ) ^ j.val) ≤ e →
    let D := retainedMeasuredKernelData T Q F row col Φ Y r measurement χ center hσ hP
      hcarrier hs M hM hb angular H hang hH hH₀ Bdet hBdet hdB τ hτ hτ₀
    ‖wideBandKernelOperator D j.val (j, (color, z.ofLp))‖ ^ 2 ≤ Cband * (2 : ℝ) ^ j.val ∧
      ∀ q : Fin 2, ‖D.operator (refinedRadius (j, q)) (j, (color, z.ofLp))‖ ^ 2 ≤
        Cband * refinedRadius (j, q) := by
  obtain ⟨CA, Pξ, CP, hCA, _hPξ, hCP, hgrades⟩ :=
    exists_fullAmplitude_grades_on_retained_workingBall (N := embeddingDimension (d+1)) T
      ((0 : Euclidean (d+1)), (z₀, ζ₀)) hσ hKgeom hKU hball I hγ hκ AF Ar E Γ hAF hAr hE hΓ
  obtain ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    θ, hθ, hθc, hθone, hθsmall, hslice⟩ :=
    exists_uniform_canonical_rawSliceSobolev_finiteOrders hdim hP T z₀ ζ₀ hσ
      hKgeom hKU hball (AF (20 * (d+1) + 5)) hγ hκ CA CP
      (fun j ↦ (hCA j).le) (fun j ↦ (hCP j).le)
  refine ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    θ, hθ, hθc, hθone, hθsmall, ?_⟩
  intro angular H hang hhom hH hH₀ hH₁ Cmeasurement hCmeasurement
  obtain ⟨B, hB, hbound⟩ := hslice (fun _ ↦ angular) H univ isOpen_univ (subset_univ _)
    (fun _ _ η hη ↦ (hang η hη).comp _ contDiffAt_snd)
    (fun _ ↦ hhom) hH hH₀ hH₁
  let cFourier : ℝ := (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2)
  let Cband := (cFourier * Cmeasurement * B 0) ^ 2
  have hFourier : 0 < cFourier := Real.rpow_pos_of_pos (by positivity) _
  have hB₀ : 0 < B 0 := hB 0
  refine ⟨Cband, sq_nonneg _, ?_⟩
  intro F hF hi hrank hmetric hnormal hclose hlow Q hspace hphase
    z hz hzball row col Φ Y r Ω hΩ hflow hb₀ hb₁ hleading hcorrection
    RF Rr L hL hRF hRr hpF hpr measurement χ hmeasurement hχ hχone center
    hcarrier hs M hM hpoly Bdet hBdet hdB p J τ hτ hτ₀ color j hτpos hwin D
  have hK : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
  have hRF' : 14 + (rawSliceJetOrder (d+1) + 1 + 2) ≤ RF := by omega
  have hRr' : 14 + (rawSliceJetOrder (d+1) + 1 + 2) ≤ Rr := by omega
  have hFM : cNorm Kgeom (20 * (d+1) + 5) F ≤ AF (20 * (d+1) + 5) := by
    have hh := hpF (20 * (d+1) + 5)
    have heq : 20 * (d+1) + 5 - RF = 0 := by
      dsimp only [rawSliceParameterOrder, rawSliceJetOrder] at hRF
      omega
    simpa only [heq, pow_zero, mul_one] using hh
  obtain ⟨_hD, hA, hjoint, _hmixed, _hphys, _hpD, _hpA, _hpR, _hpξ, hjζ, _hmζ, _hxζ⟩ :=
    hgrades F hF hi hrank hspace hphase hmetric hnormal hlow row col Φ Y r Ω
      hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr (rawSliceJetOrder (d+1) + 1) L
      hL hRF' hRr' hpF hpr (τ color) hτpos (hτ color).2
  obtain ⟨Cc, _hCc, hc⟩ := exists_fullCorrection_reconstruction_grades
    (N := embeddingDimension (d+1)) T center hσ hKgeom hKU hball hspace hphase
      I hγ hκ AF Ar Γ hAF hAr hΓ
  obtain ⟨hν₁, hV₁, _hpν₁, _hpV₁⟩ := hc F hF hi hrank hmetric hnormal hlow
    row col Φ Y r Ω hΩ hflow hb₁ hcorrection RF Rr (rawSliceJetOrder (d+1) + 1) L
    hL hRF' hRr' hpF hpr
  obtain ⟨hν₀, hV₀, _hpν₀, _hpV₀⟩ := fullLeading_profiles_of_retained_budget T Q F
    row col Φ Y r center hσ (ball_subset_closedBall.trans (hspace.trans hKU)) hphase
      hF hi hrank (hb₀.mono (ball_subset_closedBall.trans hflow)) hAF hAr
      (fun j ↦ (hE j).le) hleading hL hRF' hRr' hpF hpr
  have hprod := rawSlice_product_subset_workingBall T hσ hacap hbcap z₀ z ζ₀ hzball
  have hsmall : closedBall center σ ⊆ ball center (2 * σ) :=
    closedBall_subset_ball (by linarith)
  have hshift4 := (rawSlice_window_containments T z (a := a) he heb hK hτpos.le hwin).2.2.2
  have hshift : ∀ η ∈ closedBall 0 ((2 : ℝ) ^ cutoffCount ((2 : ℝ) ^ j.val)),
      T.reference.spatialPatch z + τ color • η ∈ ball (T.reference.spatialPatch z) b :=
    fun η hη ↦ hshift4 η (closedBall_subset_closedBall (cutoffCount_ceiling hK) hη)
  have hχσ : Function.support χ ⊆ closedBall center.1 (σ / 2) :=
    hχ.trans (closedBall_subset_closedBall (by linarith))
  have hχX : Function.support χ ⊆ slicePhysicalDomain (d+1) a :=
    hχ.trans (closedBall_subset_ball (by linarith : a / 8 < 4 * a))
  have hscale : |τ color| * (2 : ℝ) ^ j.val ≤ σ / 8 := by
    rw [abs_of_pos hτpos]
    linarith
  let j' : Fin (cutoffCount ((2 : ℝ) ^ j.val)) :=
    ⟨j.val, by rw [cutoffCount_two_pow]; omega⟩
  have hwide : ‖wideBandKernelOperator D j.val (j, (color, z.ofLp))‖ ≤
      cFourier * Cmeasurement * B 0 * ((2 : ℝ) ^ j.val) ^ (1 / 2 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    obtain ⟨u, _hu, ext, hext, _hjet, hnorm, _hcart, _hres⟩ := hbound F hF hi hrank
      hFM hmetric hnormal hclose hlow
        ((closedBall_subset_closedBall (by linarith : σ ≤ 2 * σ)).trans hphase)
      z hz hzball row col Φ Y r ((2 : ℝ) ^ j.val) 1 (τ color) hK le_rfl hτpos hwin hA 0
      (Or.inr rfl) (fun k hk w hw ↦ by
        have hh := (hjoint k w hw).2.1
        have heq : k - (rawSliceJetOrder (d+1) + 1) = 0 := by omega
        simpa only [heq, pow_zero, one_pow, mul_one] using hh)
      (fun k hk w hw ↦ by
        have hh := hjζ k w hw
        have heq : k - 1 - (rawSliceJetOrder (d+1) + 1 + 2) = 0 := by omega
        simp only [heq, pow_zero, mul_one] at hh
        simp only [one_pow, mul_one]
        change ‖iteratedFDeriv ℝ k
          (fun q : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
            fderiv ℝ (phase T Q q.1) q.2.2) w‖ ≤ CP k
        exact hh) (PiLp.single 2 j' f) univ
    have ht := norm_retainedMeasuredKernelData_band_le_rawIntegral T Q F row col Φ Y r
      measurement χ center hσ hP hcarrier hs M hM hpoly angular H hang hH hH₀
      Bdet hBdet hdB τ hτ hτ₀ hphase hχσ color z.ofLp (ball_subset_closedBall hzball)
      isOpen_ball (fun w hw ↦ hphase (ball_subset_closedBall hw)) hν₀ hν₁ hV₀ hV₁
      (mem_ball_self hb) (fun q hq ↦ hsmall (hprod q hq)) hχX j hscale hshift
      f θ ext hext (fun x hx ↦ hθone (hχ hx)) hχone hCmeasurement hmeasurement
    have hn : ext.jetNorm ≤ B 0 * ((2 : ℝ) ^ j.val) ^ (1 / 2 : ℝ) * ‖f‖ := by
      simpa only [Nat.cast_zero, zero_add, PiLp.norm_single] using hnorm
    exact ht.trans ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq
      (by ring))
  have hsq : ‖wideBandKernelOperator D j.val (j, (color, z.ofLp))‖ ^ 2 ≤
      Cband * (2 : ℝ) ^ j.val := by
    apply (pow_le_pow_left₀ (norm_nonneg _) hwide 2).trans_eq
    have hsqroot : (((2 : ℝ) ^ j.val) ^ (1 / 2 : ℝ)) ^ 2 = (2 : ℝ) ^ j.val := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, Real.rpow_one]
    rw [mul_pow, hsqroot]
  refine ⟨hsq, ?_⟩
  intro q
  apply (pow_le_pow_left₀ (norm_nonneg _)
    (norm_annularOperator_le_wideBand D j.val (j, (color, z.ofLp)) q) 2).trans
  apply hsq.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)

end JanetCartan.Sampling.MeasuredAmplitude
