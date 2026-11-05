module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.LocalTransfer

/-!
# Finite assembly of the proved direct-factor costs

These elementary deductions combine the concrete PDO and elapsed-integral
estimates for `app:ch_regular:lem:finite-chain`. They do not produce analytic
bounds for an unknown factor. Consumers are the complete solver, residual,
identity defect and physical pairing in this directory.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open ResponseTransfer

variable {ι X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Adding two actual factors preserves their polynomial costs, with one
common input order (`app:ch_regular:eq:chain-tail`). -/
theorem polynomialCost_add (G : GradedScale X) (H : GradedScale Y)
    {ρ : ι → ℝ} (hρ : ∀ i, 1 ≤ ρ i) {S T : ι → X →ₗ[ℝ] Y}
    (hS : HasPolynomialSobolevCost G H ρ S) (hT : HasPolynomialSobolevCost G H ρ T) :
    HasPolynomialSobolevCost G H ρ (fun i ↦ S i + T i) := by
  intro s
  obtain ⟨t, c, D, hD, hs⟩ := hS s
  obtain ⟨u, b, C, hC, ht⟩ := hT s
  refine ⟨max t u, max c b, D+C, add_nonneg hD hC, ?_⟩
  intro i v hv
  have hρi : 0 ≤ ρ i := zero_le_one.trans (hρ i)
  obtain ⟨hm, hn⟩ := hs i v (G.antitone_level (le_max_left _ _) hv)
  obtain ⟨hk, hl⟩ := ht i v (G.antitone_level (le_max_right _ _) hv)
  refine ⟨(H.level s).add_mem hm hk, (gradeNorm_add_le H hm hk).trans ?_⟩
  calc
    _ ≤ D * ρ i ^ max c b * G.gradeNorm (max t u) v +
        C * ρ i ^ max c b * G.gradeNorm (max t u) v := by
      apply add_le_add
      · exact hn.trans (mul_le_mul (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hρ i) (le_max_left _ _)) hD)
          (G.gradeNorm_mono (le_max_left _ _) hv) (G.gradeNorm_nonneg _ _) (by positivity))
      · exact hl.trans (mul_le_mul (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hρ i) (le_max_right _ _)) hC)
          (G.gradeNorm_mono (le_max_right _ _) hv) (G.gradeNorm_nonneg _ _) (by positivity))
    _ = _ := by ring

/-- Actual finite sums retain membership and a common polynomial cost
(`app:ch_regular:lem:finite-chain`). -/
theorem polynomialCost_sum {κ : Type*} (G : GradedScale X) (H : GradedScale Y)
    {ρ : ι → ℝ} (hρ : ∀ i, 1 ≤ ρ i) (F : κ → ι → X →ₗ[ℝ] Y) (I : Finset κ)
    (hF : ∀ j ∈ I, HasPolynomialSobolevCost G H ρ (F j)) :
    HasPolynomialSobolevCost G H ρ (fun i ↦ ∑ j ∈ I, F j i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro s
    refine ⟨0, 0, 0, le_rfl, ?_⟩
    intro i v hv
    simp only [Finset.sum_empty, LinearMap.zero_apply, zero_mul]
    refine ⟨(H.level s).zero_mem, ?_⟩
    rw [H.gradeNorm_eq (H.level s).zero_mem]
    exact le_of_eq (map_zero (H.seminorm s))
  | @insert j I hj ih =>
    simpa only [Finset.sum_insert hj] using polynomialCost_add G H hρ
      (hF j (Finset.mem_insert_self _ _)) (ih (fun k hk ↦ hF k (Finset.mem_insert_of_mem hk)))

/-- Composition adds the two fixed frequency exponents. This is used only
for the fixed fiber maps in the physical pairing/compression
(`app:ch_regular:eq:chain-tail`). -/
theorem polynomialCost_comp (G : GradedScale X) (H : GradedScale Y) (K : GradedScale Z)
    {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i) {S : ι → Y →ₗ[ℝ] Z} {T : ι → X →ₗ[ℝ] Y}
    (hS : HasPolynomialSobolevCost H K ρ S) (hT : HasPolynomialSobolevCost G H ρ T) :
    HasPolynomialSobolevCost G K ρ (fun i ↦ (S i).comp (T i)) := by
  intro s
  obtain ⟨t, c, D, hD, hs⟩ := hS s
  obtain ⟨u, b, C, hC, ht⟩ := hT t
  refine ⟨u, c+b, D*C, mul_nonneg hD hC, ?_⟩
  intro i v hv
  obtain ⟨hm, hn⟩ := ht i v hv
  obtain ⟨hk, hl⟩ := hs i (T i v) hm
  refine ⟨hk, hl.trans ?_⟩
  calc
    _ ≤ D * ρ i ^ c * (C * ρ i ^ b * G.gradeNorm u v) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg hD (Real.rpow_nonneg (hρ i).le _))
    _ = _ := by rw [Real.rpow_add (hρ i)]; ring

/-- The retained identity term has cost zero (`app:ch_regular:eq:chain-tail`). -/
theorem polynomialCost_identity (G : GradedScale X) (ρ : ι → ℝ) :
    HasPolynomialSobolevCost G G ρ (fun _ ↦ LinearMap.id) := by
  intro s
  exact ⟨s, 0, 1, zero_le_one, fun i v hv ↦ ⟨hv, by simp⟩⟩

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
