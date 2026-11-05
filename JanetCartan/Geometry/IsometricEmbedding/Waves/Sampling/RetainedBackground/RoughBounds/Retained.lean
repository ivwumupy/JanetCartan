module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.RoughBounds.Restriction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.TransportComparison.Pointwise

/-!
# Actual retained physical and transport bounds

Apply the original immersion/scalar profile producer to the SAME full
background polynomial, then restrict its physical jets and its inverse-frequency
segment. These are the actual amplitude estimates used by
`app:ch_waves:eq:background-quadrature-rough` and the adjacent transport comparison.
The original scalar domain and reserve fourteen are unchanged.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.RetainedBackground
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer

/-- Produce physical `C^k` and radial `O(λ⁻¹)` bounds from the original
retained inputs, with constants before the fields, radial labels and scale.
The tensor is the fixed supported extension, whose plateau agrees with
`localizedBackground`; its zero endpoint is `backgroundPolynomial_zero`.
Consumers: `app:ch_waves:eq:background-quadrature-rough` and its adjacent
colored-to-transport comparison. Finite-family application and identification
under the unchanged carrier weight remain the sampling parent's obligation. -/
theorem exists_retained_background_physical_and_transport_budgets
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
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) :
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
      (∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z : Euclidean 3,
        ∀ J : Set (Euclidean n), ∀ k,
          cNorm J k (fun x ↦ supportedJointTensor a hρ χ H
            (τ, (x, (z, T.reference.spatialPatch z)))) ≤
              (∑ j ∈ Finset.range (k + 1), A j) * L ^ k) ∧
      (1 ≤ rpar → ∀ (R lam : ℝ), 1 ≤ R → 1 ≤ lam →
        ∀ w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)),
          ‖supportedJointTensor a hρ χ H ((R * lam)⁻¹, w) -
            supportedJointTensor a hρ χ H (0, w)‖ ≤ A 1 * lam⁻¹) := by
  obtain ⟨A, hA, hprod⟩ := exists_retained_supportedBackground_budgets
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ χ hχ
  refine ⟨A, hA, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hs, hj⟩ := hprod F hF hi hrank hmetric hnormal hlow row col Φ Y r
    Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  constructor
  · intro τ hτ z J k
    exact cNorm_physicalSlice_le hs (fun j ↦ (hA j).le) hL hj hτ
      (z, T.reference.spatialPatch z) J k
  · intro hrpar R lam hR hlam w
    exact norm_radial_inverseFrequency_sub_zero_le hs (hA 1).le hrpar hj hR hlam w

end JanetCartan.Sampling.RetainedBackground
