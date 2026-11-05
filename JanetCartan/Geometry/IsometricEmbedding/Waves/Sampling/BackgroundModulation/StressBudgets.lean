module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.CanonicalEndpoint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.JointBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Tame
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# The actual projected-stress measurement budget

The stress in the canonical channel varies with the immersion. Its loss-two
estimate follows from the same metric and normal gaps as the raw producer.
Thus the measurement constants precede the immersion and history scale.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.BackgroundModulation
open ProjectedStressFrame ActualCarriers.CurrentFullPhase
open RawPrimary.AmplitudeGrades.Polynomial

/-- The complex contraction is real linear in the original real stress
frame (`app:ch_background:setup:bg-wkb-input`). -/
def complexStressContractionLinear (n : ℕ) :
    (Fin n → MetricTensor n) →L[ℝ]
      (Matrix (Fin n) (Fin n) ℂ →L[ℝ] EuclideanSpace ℂ (Fin n)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun S ↦ (complexStressContraction S).restrictScalars ℝ
      map_add' := by
        intro S T
        ext A i
        simp [complexStressContraction, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t S
        ext A i
        simp [complexStressContraction, Finset.mul_sum, mul_assoc] }

/-- All jets of the literal varying projected stress satisfy a fixed
reserve after spending its two derivatives. The constants use the fixed
immersion profile and the separate metric and normal gaps, with no stress
or measurement budget assumed (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_projectedStress_jet_budgets
    {n N : ℕ} {U : Set (Euclidean n)} (hU : IsOpen U)
    (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall a ρ ⊆ K)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean n → Euclidean N) (_hF : ContDiffOn ℝ ∞ F U)
        (_hi : IsImmersionOn F U) (_hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ (RF rpar : ℕ) (L : ℝ), 1 ≤ L → 4 ≤ RF → 2 + rpar ≤ RF →
      HasDerivativeProfile K F RF L AF →
      ∀ x ∈ closedBall a ρ, ∀ j,
        ‖iteratedFDeriv ℝ j (projectedStress F) x‖ ≤ A j * L ^ (j - rpar) := by
  choose C hC hc using fun j ↦ exists_cNorm_projectedStress_le_tame
    (N := N) a hρ (AF 4 + 1) hγ hκ j
  let A := fun j : ℕ ↦ ((j + 1 : ℝ) * C j) * (1 + AF (j + 2))
  have hA (j) : 0 < A j := by
    dsimp [A]
    have := hC j
    have := hAF (j + 2)
    positivity
  refine ⟨A, hA, ?_⟩
  intro F hF hi hrank hmetric hnormal RF rpar L hL hRF hreserve hpF x hx j
  have hs : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hFM : cNorm K 4 F ≤ AF 4 + 1 := by
    have hh := hpF 4
    rw [Nat.sub_eq_zero_of_le hRF, pow_zero, mul_one] at hh
    linarith
  have hframe := frame_cNorm_le_of_componentwise (isCompact_closedBall a ρ)
    (fun y hy ↦ (hs.contDiffAt (hU.mem_nhds (hKU (hball hy)))).of_le
      (by simp : (j : ℕ∞ω) ≤ ∞))
    (mul_nonneg (hC j).le (by linarith [cNorm_nonneg K (j + 2) F]))
    (hc j F U K hU hK hball hKU hF hi hFM hmetric hnormal)
  have hjet := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
    (fun y hy ↦ (hs.contDiffAt (hU.mem_nhds (hKU (hball hy)))).of_le
      (by simp : (j : ℕ∞ω) ≤ ∞)) hx le_rfl
  apply JointBudget.fixed_profile_transfer_bound hL (hAF (j + 2))
    (mul_nonneg (by positivity : (0 : ℝ) ≤ j + 1) (hC j).le) hreserve (hpF (j + 2))
  exact (hjet.trans hframe).trans_eq (by ring)

/-- The original physical cutoff times the actual projected-stress
contraction has uniform jet bounds before the varying immersion. These are
the measurement inputs for the Hermitian product, retaining the derivative
reserve (`app:ch_background:setup:bg-wkb-input`). -/
theorem exists_projectedStressMeasurement_jet_budgets
    {n N : ℕ} {U : Set (Euclidean n)} (hU : IsOpen U)
    (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall a ρ ⊆ K)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j)
    (χ : Euclidean n → ℝ) (hχ : ContDiffOn ℝ ∞ χ U) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean n → Euclidean N) (_hF : ContDiffOn ℝ ∞ F U)
        (_hi : IsImmersionOn F U) (_hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ (RF rpar : ℕ) (L : ℝ), 1 ≤ L → 4 ≤ RF → 2 + rpar ≤ RF →
      HasDerivativeProfile K F RF L AF →
      let meas := fun x ↦ χ x • (complexStressContraction (projectedStress F x)).restrictScalars ℝ
      ContDiffOn ℝ ∞ meas U ∧ ∀ x ∈ closedBall a ρ, ∀ j,
        ‖iteratedFDeriv ℝ j meas x‖ ≤ A j * L ^ (j - rpar) := by
  obtain ⟨A, hA, hstress⟩ := exists_projectedStress_jet_budgets
    (N := N) hU a hρ hK hKU hball hγ hκ AF hAF
  let C := complexStressContractionLinear n
  let B := fun j ↦ ‖C‖ * A j
  have hB (j) : 0 ≤ B j := mul_nonneg (norm_nonneg C) (hA j).le
  let b := fun j ↦ cNorm (closedBall a ρ) j χ
  have hb (j) : 0 ≤ b j := cNorm_nonneg _ _ _
  let sm := ContinuousLinearMap.lsmul ℝ ℝ
    (E := Matrix (Fin n) (Fin n) ℂ →L[ℝ] EuclideanSpace ℂ (Fin n))
  let D := productProfile sm b B
  have hD (j) : 0 ≤ D j := productProfile_nonneg sm hb hB j
  refine ⟨fun j ↦ 1 + D j, fun j ↦ by linarith [hD j], ?_⟩
  intro F hF hi hrank hmetric hnormal RF rpar L hL hRF hreserve hpF
  have hs : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hcs : ContDiffOn ℝ ∞ (C ∘ projectedStress F) U := C.contDiff.comp_contDiffOn hs
  refine ⟨hχ.smul hcs, ?_⟩
  intro x hx j
  have hbjet (k) : ‖iteratedFDeriv ℝ k χ x‖ ≤ b k * L ^ (k - rpar) := by
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ (hχ.contDiffAt (hU.mem_nhds (hKU (hball hy)))).of_le
        (by simp : (k : ℕ∞ω) ≤ ∞)) hx le_rfl).trans
      (le_mul_of_one_le_right (hb k) (one_le_pow₀ hL))
  have hCjet (k) : ‖iteratedFDeriv ℝ k (C ∘ projectedStress F) x‖ ≤
      B k * L ^ (k - rpar) := by
    apply (C.norm_iteratedFDeriv_comp_left
      (hs.contDiffAt (hU.mem_nhds (hKU (hball hx)))) (by simp : (k : ℕ∞ω) ≤ ∞)).trans
    exact (mul_le_mul_of_nonneg_left
      (hstress F hF hi hrank hmetric hnormal RF rpar L hL hRF hreserve hpF x hx k)
      (norm_nonneg _)).trans_eq (by dsimp [B]; ring)
  exact (jet_bilinear_le sm hU hχ hcs (hKU (hball hx)) hL hb hB hbjet hCjet j).trans
    (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith)
      (pow_nonneg (le_trans zero_le_one hL) _))

end JanetCartan.Sampling.BackgroundModulation
