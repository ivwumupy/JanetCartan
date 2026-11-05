module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.Literal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.RetainedBudgets

/-!
# Retained joint budgets for the actual background polynomial

Apply `exists_retained_jointPolynomial_budgets` to the original immersion and
scalar profiles, then the existing real Hermitian bilinear map. All constants
precede the varying fields, inverse frequencies, radial labels and amplitude
scale. The consumer is the carrier-graph pullback in the deterministic
background estimate `app:ch_waves:eq:background-quadrature`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer

/-- The Hermitian polynomial's joint jets follow from the original map/scalar
profiles and the SAME retained leading/correction outputs. No background jet
bound or L2 regularity is assumed. The retained producer is
`RawPrimary.exists_finite_retained_graded_raw_family_with_primitives`; finite
family application remains with the sampling parent
(`app:ch_waves:eq:background-quadrature`,
`app:ch_waves:eq:background-quadrature-rough`). -/
theorem exists_retained_backgroundPolynomial_budgets
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (I : Set (Euclidean (n - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
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
      let H := fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦
        backgroundPolynomial T Q F row col Φ Y r q.1 q.2
      ContDiffOn ℝ ∞ H (univ ×ˢ ball a (2 * ρ)) ∧
        ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w ∈ closedBall a ρ, ∀ j,
          ‖iteratedFDeriv ℝ j H (τ, w)‖ ≤ A j * L ^ (j - rpar) := by
  obtain ⟨A, hA, hpoly⟩ := MeasuredAmplitude.exists_retained_jointPolynomial_budgets
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ
  let B := hermitianCrossBilinear (Fin N) (Fin n)
  let C := productProfile B A A
  have hC (j) : 0 ≤ C j := productProfile_nonneg B (fun j ↦ (hA j).le)
    (fun j ↦ (hA j).le) j
  refine ⟨fun j ↦ 1 + C j, fun j ↦ by linarith [hC j], ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hs, hj⟩ := hpoly F hF hi hrank hmetric hnormal hlow row col Φ Y r
    Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  refine ⟨B.contDiff.comp_contDiffOn hs |>.clm_apply hs, ?_⟩
  intro τ hτ w hw j
  have hw' : (τ, w) ∈ (univ : Set ℝ) ×ˢ ball a (2 * ρ) :=
    ⟨mem_univ _, closedBall_subset_ball (by linarith) hw⟩
  exact (jet_bilinear_le B (isOpen_univ.prod isOpen_ball) hs hs hw' hL
    (fun j ↦ (hA j).le) (fun j ↦ (hA j).le) (hj τ hτ w hw) (hj τ hτ w hw) j).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
        (pow_nonneg (le_trans zero_le_one hL) _))

end JanetCartan.Sampling.RetainedBackground
