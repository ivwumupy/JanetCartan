module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.SupportedNormal

/-!
# Applying the retained raw estimates to the actual normalized amplitude

This module applies the measured-polynomial construction and the fixed
normalized pullback estimates to the SAME raw fields. Constants precede the
immersion, scalar, history scale, bands and colors. In particular low joint
jets are independent of the history scale; no normalized-amplitude budget
is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial RawKernel
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer
open FullNormalGeometry FullNormalGeometry.PhaseJets

/-- Actual normalized joint-amplitude bounds, with the original detector,
high-pass, half derivative and all correction powers. This explicitly applies
`exists_retained_measuredPolynomial_budgets` on the retained reconstruction
outputs. The primitive covector estimates have the SAME producer as that
endpoint, namely `RetainedCorrection` with its selected minors and flows.
For `UniformNormalData`, joint order `20*(n+1)+1` requires original map/scalar
profile orders at least `20*(n+1)+17`; C14 alone is insufficient.
The cutoff agreement and support are proved in `SupportedNormal`
(`app:ch_waves:setup:oscillatory`, `app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_retained_normalizedAmplitude_budgets
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C) (M : ℝ) {e : ℝ} (he : e ≤ 1)
    {S : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hS : IsCompact S) (hSM : S ⊆ tripleDomain T M)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hhigh : ContDiff ℝ ∞ highPass) (hhigh₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1)
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
    (hχ : ContDiffOn ℝ ∞ χ U) (hm : ContDiffOn ℝ ∞ measurement U) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
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
      ∀ j,
        let f := fun q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) ↦
          supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
            angular highPass ψ j q.2.1 q.1 q.2.2.1 q.2.2.2
        ContDiffOn ℝ ∞ f (univ ×ˢ tripleDomain T M) ∧
          (∀ q ∈ Icc (-e) e ×ˢ S, ∀ k,
            ‖iteratedFDeriv ℝ k f q‖ ≤ A k * L ^ (k - rpar)) ∧
          ∀ q ∈ Icc (-e) e ×ˢ S, ∀ k ≤ rpar,
            ‖iteratedFDeriv ℝ k f q‖ ≤ A k := by
  obtain ⟨A, hA, hraw⟩ := exists_retained_measuredPolynomial_budgets (N := N) T a hρ
    hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ χ measurement hχ hm
  obtain ⟨B, hB, hpull⟩ := exists_normalizedMeasuredPullback_budgets T hP M he hS hSM
    ψ hψ angular highPass ha hah hhigh hhigh₁ A (fun k ↦ (hA k).le)
  refine ⟨fun k ↦ 1 + B k, fun k ↦ by linarith [hB k], ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr j
  obtain ⟨_, _, hs, hj⟩ := hraw F hF hi hrank hmetric hnormal hlow
    row col Φ Y r Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hcont, hbound⟩ := hpull _ hs L rpar hL hj j
  refine ⟨hcont, ?_, ?_⟩
  · intro q hq k
    exact (hbound q hq k).trans (mul_le_mul_of_nonneg_right (by linarith)
      (pow_nonneg (zero_le_one.trans hL) _))
  intro q hq k hk
  have hh := hbound q hq k
  rw [Nat.sub_eq_zero_of_le hk, pow_zero, mul_one] at hh
  exact hh.trans (le_add_of_nonneg_left zero_le_one)

end JanetCartan.Sampling.MeasuredAmplitude
