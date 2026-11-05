module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.CrossProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.FixedRatePullback

/-!
# Corrected normal-amplitude jets from the primitive profiles

Apply the cutoff, Hermitian product and covector-only pullback estimates to
one literal corrected coefficient. Its six profile sequences precede the
varying raw fields, physical rate, reserve and history scale. Neither the
corrected coefficient jets nor normalized amplitude jets are hypotheses.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedMean
open CorrectedAtoms RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open FullNormalGeometry.PhaseJets MeasuredAmplitude

/-- Construct all joint jets of the literal corrected normal amplitude from
exactly the five raw coefficient profiles and the same response derivative
profile. The original supplied cutoff, real measurement, carrier and detector
are retained. The measurement profile is uniform before the varying measurement. The constant precedes every varying raw field, physical rate,
reserve, history scale and band label; no response is evaluated at rate zero
unless that rate was already supplied (`app:ch_response:eq:current-atomic-amplitudes`,
`app:ch_waves:setup:oscillatory`, `app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_fixedRateNormalAmplitude_budgets_of_measurement_profiles
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (hκK : tsupport κ ⊆ K)
    (Cmeasure : ℕ → ℝ) (hCmeasure : ∀ j, 0 ≤ Cmeasure j)
    (Cjet A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ)
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j)
    (M : ℝ) {e : ℝ} (he : e ≤ 1)
    {S : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hS : IsCompact S) (hSM : S ⊆ tripleDomain T M)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hhigh : ContDiff ℝ ∞ highPass) (hhigh₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1) :
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
        Euclidean (m + 1)), ContDiff ℝ ∞ C →
      ∀ (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
        ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
        (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
          Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
        (χ : Euclidean (m + 1) → ℝ)
        (B : MetricField (m + 1) →ₗ[ℝ] (Euclidean (m + 1) → Euclidean N))
        (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ),
      (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
      ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω →
      ∀ (τ L : ℝ) (rpar : ℕ), 0 < τ → τ ≤ 1 → 1 ≤ L →
      HasDerivativeProfile K (fun w ↦ C w.1) rpar L Cmeasure →
      HasDerivativeProfile K (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet →
      HasDerivativeProfile K (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀ →
      HasDerivativeProfile K (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
        (rpar + 1) L A₁ →
      HasDerivativeProfile K (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀ →
      HasDerivativeProfile K (fullCorrectionReconstruction T Q F row col Φ Y r)
        (rpar + 1) L B₁ →
      ContDiffOn ℝ ∞ (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω →
      (∀ j, ∀ w ∈ K,
        ‖iteratedFDeriv ℝ j (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
          τ * Cresp j * L ^ (j - rpar)) →
      ∀ j,
        let f := fun q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) ↦
          fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
            angular highPass ψ j q.2.1 q.1 q.2.2.1 q.2.2.2
        ContDiffOn ℝ ∞ f (univ ×ˢ tripleDomain T M) ∧
          (∀ q ∈ Icc (-e) e ×ˢ S, ∀ k,
            ‖iteratedFDeriv ℝ k f q‖ ≤ D k * L ^ (k - rpar)) ∧
          ∀ q ∈ Icc (-e) e ×ˢ S, ∀ k ≤ rpar,
            ‖iteratedFDeriv ℝ k f q‖ ≤ D k := by
  let A := fun j ↦ derivativeProfile (m + 1) N Cjet A₀ A₁ B₀ B₁ j + Cresp j
  have hA (j) : 0 ≤ A j := add_nonneg
    (polynomialProfiles_nonneg (m + 1) N hCjet hA₀ hA₁ hB₀ hB₁ j).2.2.2.2 (hCresp j)
  let Acut := productProfile (ContinuousLinearMap.lsmul ℝ ℝ
    (E := Matrix (Fin N) (Fin (m + 1)) ℂ)) (fun j ↦ cNorm K j κ) A
  have hAcut (j) : 0 ≤ Acut j := productProfile_nonneg _ (fun j ↦ cNorm_nonneg _ _ _) hA j
  obtain ⟨Across, hAcross, hcross⟩ := exists_carrierCrossCoefficient_budgets_of_measurement_profiles (N := N)
    T hP z₀ hρ hcarrier hK κ hκK Cmeasure hCmeasure Acut hAcut
  obtain ⟨D, hD, hpull⟩ := exists_fixedRatePullback_budgets T hP M he hS hSM
    ψ hψ angular highPass ha hah hhigh hhigh₁ Across hAcross
  refine ⟨fun k ↦ 1 + D k, fun k ↦ by linarith [hD k], ?_⟩
  intro C hC Q F row col Φ Y χ B r hphase hν₀ hν₁ hV₀ hV₁ τ L rpar hτ hτ₁ hL hmeasure
    hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets j
  obtain ⟨hcutSmooth, hcutJet⟩ := cutCorrectedDerivativeAmplitude_budgets_of_profiles
    T Q F row col Φ Y χ B r hK hΩ hKΩ hphase hν₀ hν₁ hV₀ hV₁
    hCjet hA₀ hA₁ hB₀ hB₁ hCresp hτ hτ₁ hL hpξ hpν₀ hpν₁ hpV₀ hpV₁
    hresponse hresponseJets κ hκ hκK
  obtain ⟨hcrossSmooth, hcrossJet⟩ := hcross C hC _ hcutSmooth
    (fun w hw ↦ by simp only [hw, zero_smul]) L rpar hL hcutJet hmeasure
  obtain ⟨hs, hj⟩ := hpull _ hcrossSmooth L rpar hL hcrossJet j
  refine ⟨hs, ?_, ?_⟩
  · intro q hq k
    exact (hj q hq k).trans
      (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (zero_le_one.trans hL) _))
  · intro q hq k hk
    have hh := hj q hq k
    rw [Nat.sub_eq_zero_of_le hk, pow_zero, mul_one] at hh
    exact hh.trans (le_add_of_nonneg_left zero_le_one)

/-- Construct all joint jets of the literal corrected normal amplitude from
exactly the five raw coefficient profiles and the same response derivative
profile. The original supplied cutoff, real measurement, carrier and detector
are retained. The constant precedes every varying raw field, physical rate,
reserve, history scale and band label; no response is evaluated at rate zero
unless that rate was already supplied (`app:ch_response:eq:current-atomic-amplitudes`,
`app:ch_waves:setup:oscillatory`, `app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_fixedRateNormalAmplitude_budgets_of_profiles
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (hκK : tsupport κ ⊆ K)
    (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
      Euclidean (m + 1)) (hC : ContDiff ℝ ∞ C)
    (Cjet A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ)
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j)
    (M : ℝ) {e : ℝ} (he : e ≤ 1)
    {S : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hS : IsCompact S) (hSM : S ⊆ tripleDomain T M)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hhigh : ContDiff ℝ ∞ highPass) (hhigh₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1) :
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
        ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
        (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
          Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
        (χ : Euclidean (m + 1) → ℝ)
        (B : MetricField (m + 1) →ₗ[ℝ] (Euclidean (m + 1) → Euclidean N))
        (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ),
      (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
      ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω →
      ∀ (τ L : ℝ) (rpar : ℕ), 0 < τ → τ ≤ 1 → 1 ≤ L →
      HasDerivativeProfile K (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet →
      HasDerivativeProfile K (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀ →
      HasDerivativeProfile K (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
        (rpar + 1) L A₁ →
      HasDerivativeProfile K (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀ →
      HasDerivativeProfile K (fullCorrectionReconstruction T Q F row col Φ Y r)
        (rpar + 1) L B₁ →
      ContDiffOn ℝ ∞ (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω →
      (∀ j, ∀ w ∈ K,
        ‖iteratedFDeriv ℝ j (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
          τ * Cresp j * L ^ (j - rpar)) →
      ∀ j,
        let f := fun q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) ↦
          fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
            angular highPass ψ j q.2.1 q.1 q.2.2.1 q.2.2.2
        ContDiffOn ℝ ∞ f (univ ×ˢ tripleDomain T M) ∧
          (∀ q ∈ Icc (-e) e ×ˢ S, ∀ k,
            ‖iteratedFDeriv ℝ k f q‖ ≤ D k * L ^ (k - rpar)) ∧
          ∀ q ∈ Icc (-e) e ×ˢ S, ∀ k ≤ rpar,
            ‖iteratedFDeriv ℝ k f q‖ ≤ D k := by
  let meas := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) ↦ C w.1
  let Cmeasure := fun j ↦ cNorm K j meas
  have hCmeasure (j) : 0 ≤ Cmeasure j := cNorm_nonneg _ _ _
  obtain ⟨D, hD, hall⟩ := exists_fixedRateNormalAmplitude_budgets_of_measurement_profiles (N := N)
    T hP z₀ hρ hcarrier hK hΩ hKΩ κ hκ hκK Cmeasure hCmeasure
    Cjet A₀ A₁ B₀ B₁ Cresp hCjet hA₀ hA₁ hB₀ hB₁ hCresp M he hS hSM
    ψ hψ angular highPass ha hah hhigh hhigh₁
  refine ⟨D, hD, ?_⟩
  intro Q F row col Φ Y χ B r hphase hν₀ hν₁ hV₀ hV₁ τ L rpar hτ hτ₁ hL
  apply hall C hC Q F row col Φ Y χ B r hphase hν₀ hν₁ hV₀ hV₁ τ L rpar hτ hτ₁ hL
  intro j
  exact le_mul_of_one_le_right (hCmeasure j) (one_le_pow₀ hL)

end JanetCartan.Sampling.CorrectedMean
