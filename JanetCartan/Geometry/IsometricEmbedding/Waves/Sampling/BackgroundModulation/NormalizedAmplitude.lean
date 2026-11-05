module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.CarrierPullback

/-!
# The normalized actual background-modulation amplitude

The original carrier weight, detector, high-pass and dyadic masks multiply
the measured Hermitian product. The common plateau identifies the supported
extension everywhere, including epsilon zero. The all-order budget below
applies the actual retained producers, before the varying fields and scales.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.BackgroundModulation
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open RawKernel LeadingWave RawPrimary LeadingWave.FullModulation
open RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open ProjectedStressFrame AmbientResponse ResponseTransfer MeasuredAmplitude
open FullNormalGeometry FullNormalGeometry.PhaseJets MeanNormalBound.NormalizedFullPhase
open ContinuumRow ContinuumRow.CanonicalConic RawPrimary.MaskProfiles

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) →
    Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
  (r : Euclidean ((m + 1) - 1) × Euclidean 3 → ℝ) (χ : Euclidean (m + 1) → ℝ)

/-- The actual normalized Hermitian product, with the original masks
and common inverse frequency (`app:ch_background:setup:bg-wkb-input`). -/
def backgroundModulationNormalAmplitude
    (angular : Euclidean ((m + 1) - 1) → ℂ) (H : Euclidean ((m + 1) - 1) → ℝ)
    (ψ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x u : Euclidean (m + 1)) : EuclideanSpace ℂ (Fin (m + 1)) :=
  normalizedMeasuredPullback T ψ angular H
    (fun q ↦ measuredBackgroundModulationPolynomial T Q F row col Φ Y r χ
      q.1 q.2.2.1 q.2.1 q.2.2.2) j (ε, v, x, u)

/-- The supported extension of that SAME normalized product
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def supportedBackgroundModulationNormalAmplitude
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (angular : Euclidean ((m + 1) - 1) → ℂ) (H : Euclidean ((m + 1) - 1) → ℝ)
    (ψ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x u : Euclidean (m + 1)) : EuclideanSpace ℂ (Fin (m + 1)) :=
  normalizedMeasuredPullback T ψ angular H
    (fun q ↦ supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
      q.1 q.2.2.1 q.2.1 q.2.2.2) j (ε, v, x, u)

variable
  (angular : Euclidean ((m + 1) - 1) → ℂ) (H : Euclidean ((m + 1) - 1) → ℝ)
  (ψ : SeparatedSampling.Point → ℝ)

/-- Literal normalized covector insertion, retaining both polynomial
factors, the lowest band and the high-pass transition from one to two
(`app:ch_waves:eq:phase-quotient`). -/
theorem backgroundModulationNormalAmplitude_literal (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x : Euclidean (m + 1)) (s : ℝ) (θ : Euclidean ((m + 1) - 1)) :
    backgroundModulationNormalAmplitude T Q F row col Φ Y r χ angular H ψ j v ε x
        (fullInputCoordinates m (s, θ)) =
      ((ψ (carrierSamplingEquiv (s, v)) : ℂ) * normalizedMask (n := m + 1) angular H j θ) •
        measuredBackgroundModulationPolynomial T Q F row col Φ Y r χ
          (ε / (2 : ℝ) ^ j) (carrierParameters (v, s)) x
          (T.reference.spatialPatch (carrierParameters (v, s)) + ε • θ) := by
  simp only [backgroundModulationNormalAmplitude, normalizedMeasuredPullback,
    normalizedRetainedPoint, normalizedRetainedMask, inputCoordinates_apply, adapted_canonicalInputCoordinates]
  simp only [div_eq_mul_inv, mul_comm]

/-- Global equality with the literal amplitude follows from the original
physical and carrier supports and the same wide radial band. No support is
shrunk in the equality (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem supportedBackgroundModulationNormalAmplitude_eq
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hψ : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (j : ℕ) (v : Euclidean 2) {ε : ℝ} (hε : |ε| ≤ ρ / 8)
    (x u : Euclidean (m + 1)) :
    supportedBackgroundModulationNormalAmplitude T Q F row col Φ Y r χ a hρ
        angular H ψ j v ε x u =
      backgroundModulationNormalAmplitude T Q F row col Φ Y r χ angular H ψ j v ε x u := by
  obtain ⟨⟨s, θ⟩, rfl⟩ := (fullInputCoordinates m).surjective u
  simp only [supportedBackgroundModulationNormalAmplitude, backgroundModulationNormalAmplitude,
    normalizedMeasuredPullback, normalizedRetainedPoint, normalizedRetainedMask,
    inputCoordinates_apply, adapted_canonicalInputCoordinates]
  by_cases hψ₀ : ψ (carrierSamplingEquiv (s, v)) = 0
  · simp only [hψ₀, Complex.ofReal_zero, zero_mul, zero_smul]
  by_cases hm : normalizedMask (n := m + 1) angular H j θ = 0
  · simp only [hm, mul_zero, zero_smul]
  have hθ : ‖θ‖ ≤ 2 := (lt_of_not_ge (fun hh ↦
    hm (normalizedMask_eq_zero_of_ge (n := m + 1) angular H j hh))).le
  rw [supportedBackgroundModulationPolynomial_eq_raw T Q F row col Φ Y r χ a hρ
    hχ (hψ s v hψ₀) _ x (ε • θ) (by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |ε| * ‖θ‖ ≤ (ρ / 8) * 2 := mul_le_mul hε hθ (norm_nonneg _) (by positivity)
        _ = ρ / 4 := by ring)]

/-- The original physical, carrier and angular masks give the support
required by the retained full normal geometry
(`app:ch_waves:setup:oscillatory`). -/
theorem support_backgroundModulationNormalAmplitude_subset
    (hangular : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    {z₀ : Euclidean 3} {ηb : Euclidean ((m + 1) - 1)} (hηb : ηb ≠ 0)
    {radius amin amax : ℝ} (hradius : 0 < radius)
    (hlo : amin ≤ (1 / 2) / ‖ηb‖) (hhi : 2 / ‖ηb‖ ≤ amax)
    (hangle : ∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈
      closedDirections (n := m + 1) ηb radius)
    {X₀ : Set (Euclidean (m + 1))} (hχ : Function.support χ ⊆ X₀)
    (v : Euclidean 2)
    (hψ : ∀ s, ψ (carrierSamplingEquiv (s, v)) ≠ 0 → s ∈ closedBall (z₀ 0) radius)
    (j : ℕ) (ε : ℝ) :
    Function.support (Function.uncurry
      (backgroundModulationNormalAmplitude T Q F row col Φ Y r χ angular H ψ j v ε)) ⊆
      X₀ ×ˢ radialSamplingSupport T z₀ ηb radius amin amax := by
  rintro ⟨x, u⟩ hnonzero
  obtain ⟨⟨s, θ⟩, rfl⟩ := (fullInputCoordinates m).surjective u
  change backgroundModulationNormalAmplitude T Q F row col Φ Y r χ angular H ψ j v ε x
    (fullInputCoordinates m (s, θ)) ≠ 0 at hnonzero
  rw [backgroundModulationNormalAmplitude_literal] at hnonzero
  have hmask : normalizedMask (n := m + 1) angular H j θ ≠ 0 := by
    intro hz
    exact hnonzero (by simp only [hz, mul_zero, zero_smul])
  have hweight : ψ (carrierSamplingEquiv (s, v)) ≠ 0 := by
    intro hz
    exact hnonzero (by simp only [hz, Complex.ofReal_zero, zero_mul, zero_smul])
  have hphysical : χ x ≠ 0 := by
    intro hz
    exact hnonzero (by simp only [measuredBackgroundModulationPolynomial, hz,
      Complex.ofReal_zero, zero_smul, smul_zero])
  have hθlo : (1 / 2 : ℝ) < ‖θ‖ := lt_of_not_ge (fun hh ↦
    hmask (normalizedMask_eq_zero_of_le (n := m + 1) angular H j hh))
  have hθhi : ‖θ‖ < 2 := lt_of_not_ge (fun hh ↦
    hmask (normalizedMask_eq_zero_of_ge (n := m + 1) angular H j hh))
  have hθangle : angular θ ≠ 0 := by
    intro hz
    apply hmask
    rw [normalizedMask_eq_fixed_radial (n := m + 1) angular H hangular]
    simp only [hz, zero_mul, mul_zero]
  have hwide : θ ∈ RawInputPartition.wideBand (m + 1) 0 := by
    constructor
    · norm_num [RawInputPartition.dyadicScale, mem_closedBall, dist_zero_right]
      exact hθhi.le
    · simpa only [RawInputPartition.dyadicScale, pow_zero, one_div, mem_ball,
        dist_zero_right, not_lt] using hθlo.le
  exact ⟨hχ hphysical, wideBand_mem_radialSamplingSupport T hηb hradius
    (hψ s hweight) hlo hhi hwide (hangle θ hθangle)⟩

/-- Every normalized joint jet of the actual Hermitian product follows
from the retained raw reconstruction and the varying projected-stress bound.
The existing three-profile mask construction preserves the original high-pass
transition and derivative reserve. All constants precede the immersion,
scalar, colors and band ceiling (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_retained_backgroundModulation_normalized_budgets
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
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K : Set (Euclidean (m + 1))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (I : Set (Euclidean ((m + 1) - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (χ : Euclidean (m + 1) → ℝ)
    (hχ : ContDiffOn ℝ ∞ χ U) :
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
          supportedBackgroundModulationNormalAmplitude T Q F row col Φ Y r χ a hρ
            angular highPass ψ j q.2.1 q.1 q.2.2.1 q.2.2.2
        ContDiffOn ℝ ∞ f (univ ×ˢ tripleDomain T M) ∧
          (∀ q ∈ Icc (-e) e ×ˢ S, ∀ k,
            ‖iteratedFDeriv ℝ k f q‖ ≤ A k * L ^ (k - rpar)) ∧
          ∀ q ∈ Icc (-e) e ×ˢ S, ∀ k ≤ rpar,
            ‖iteratedFDeriv ℝ k f q‖ ≤ A k := by
  obtain ⟨A, hA, hraw⟩ := exists_retained_backgroundModulation_budgets (N := N) T hP a hρ hcarrier
    hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ χ hχ
  obtain ⟨B, hB, hpull⟩ := exists_normalizedMeasuredPullback_budgets T hP M he hS hSM
    ψ hψ angular highPass ha hah hhigh hhigh₁ A (fun k ↦ (hA k).le)
  refine ⟨fun k ↦ 1 + B k, fun k ↦ by linarith [hB k], ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr j
  obtain ⟨hs, hj⟩ := hraw F hF hi hrank hmetric hnormal hlow
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

end JanetCartan.Sampling.BackgroundModulation
