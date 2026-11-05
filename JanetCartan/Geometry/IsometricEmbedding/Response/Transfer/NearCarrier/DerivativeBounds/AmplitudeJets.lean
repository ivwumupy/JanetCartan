module

public import JanetCartan.Analysis.ContDiff.Norm.Products

/-!
# Finite joint jets of modified near-carrier amplitudes

The amplitude step of `app:ch_response:eq:direct-envelope-profile`.
Expressions below are evaluated as actual functions: a derivative node is a
Fréchet derivative, and a product node is an actual continuous bilinear map.
All positions, normalized covectors, and compact parameters belong to the same
domain, so there is only one derivative budget. Primitive leaves include the
selector, inverse coefficients, weights and original amplitude.

This module proves bounds from finite primitive jet hypotheses. It neither
constructs the phase coefficients nor asserts the operator transfer identities.
The bilinear formulation permits the existing Frobenius matrix multiplication
map without assuming the identity matrix has norm one.
-/

@[expose] public noncomputable section
open scoped ContDiff BigOperators

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual differential expressions for the full amplitudes in
`app:ch_response:eq:direct-envelope-profile`. Products keep their literal order. -/
inductive AmplitudeExpression (X E ι : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | primitive : ι → AmplitudeExpression X E ι
  | add : AmplitudeExpression X E ι → AmplitudeExpression X E ι → AmplitudeExpression X E ι
  | bilinear : (E →L[ℝ] E →L[ℝ] E) → AmplitudeExpression X E ι →
      AmplitudeExpression X E ι → AmplitudeExpression X E ι
  | deriv : X → AmplitudeExpression X E ι → AmplitudeExpression X E ι

namespace AmplitudeExpression

/-- Evaluation differentiates the complete amplitude, including its selector
and both physical masks (`app:ch_response:eq:direct-envelope-profile`). -/
def evaluate (a : ι → X → E) : AmplitudeExpression X E ι → X → E
  | .primitive i => a i
  | .add e f => fun x => evaluate a e x + evaluate a f x
  | .bilinear B e f => fun x => B (evaluate a e x) (evaluate a f x)
  | .deriv v e => fun x => fderiv ℝ (evaluate a e) x v

/-- Total number of primitive derivatives, shared across all product factors
in `app:ch_response:eq:direct-envelope-profile`. An addition uses the larger budget. -/
def derivativeCost : AmplitudeExpression X E ι → ℕ
  | .primitive _ => 0
  | .add e f => max e.derivativeCost f.derivativeCost
  | .bilinear _ e f => e.derivativeCost + f.derivativeCost
  | .deriv _ e => e.derivativeCost + 1

/-- Explicit finite Leibniz constants, chosen before the scale, frequency,
primitive fields, or datum in `app:ch_response:eq:direct-envelope-profile`. -/
def jetConstant (M : ι → ℕ → ℝ) : AmplitudeExpression X E ι → ℕ → ℝ
  | .primitive i, j => M i j
  | .add e f, j => e.jetConstant M j + f.jetConstant M j
  | .bilinear B e f, j => ‖B‖ * ∑ k ∈ Finset.range (j + 1),
      (j.choose k : ℝ) * e.jetConstant M k * f.jetConstant M (j - k)
  | .deriv v e, j => ‖v‖ * e.jetConstant M (j + 1)

/-- Nonnegative constants for the amplitude induction in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem jetConstant_nonneg (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (e : AmplitudeExpression X E ι) (j : ℕ) : 0 ≤ e.jetConstant M j := by
  induction e generalizing j with
  | primitive i => exact hM i j
  | add e f he hf => exact add_nonneg (he j) (hf j)
  | bilinear B e f he hf =>
    exact mul_nonneg (norm_nonneg B) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (he k)) (hf (j - k)))
  | deriv v e he => exact mul_nonneg (norm_nonneg _) (he (j + 1))

/-- Smooth primitive fields give smooth modified full amplitudes, as used in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_evaluate (a : ι → X → E) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (e : AmplitudeExpression X E ι) : ContDiff ℝ ∞ (e.evaluate a) := by
  induction e with
  | primitive i => exact ha i
  | add e f he hf => exact he.add hf
  | bilinear B e f he hf => exact (B.contDiff.comp he).clm_apply hf
  | deriv v e he => exact (he.fderiv_right (by simp)).clm_apply contDiff_const

private theorem truncated_product_exponent (p q R : ℕ) :
    (p - R) + (q - R) ≤ p + q - R := by omega

/-- Finite joint jet estimate for every actual differential expression used
in `app:ch_response:eq:direct-envelope-profile`. Only primitive derivatives
through `N` are assumed. In particular the product rule spends a single total
budget, rather than giving each coefficient its own high-order allowance. -/
theorem norm_iteratedFDeriv_evaluate_le
    (a : ι → X → E) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (L : ℝ) (hL : 1 ≤ L) (R N : ℕ) (x : X)
    (hjet : ∀ i j, j ≤ N → ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j - R))
    (e : AmplitudeExpression X E ι) (j : ℕ) (hbudget : j + e.derivativeCost ≤ N) :
    ‖iteratedFDeriv ℝ j (e.evaluate a) x‖ ≤
      e.jetConstant M j * L ^ (j + e.derivativeCost - R) := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  induction e generalizing j with
  | primitive i => simpa [evaluate, derivativeCost, jetConstant] using hjet i j (by simpa [derivativeCost] using hbudget)
  | add e f he hf =>
    have hecost : e.derivativeCost ≤ max e.derivativeCost f.derivativeCost := le_max_left _ _
    have hfcost : f.derivativeCost ≤ max e.derivativeCost f.derivativeCost := le_max_right _ _
    have he' := he j (by dsimp [derivativeCost] at hbudget; omega)
    have hf' := hf j (by dsimp [derivativeCost] at hbudget; omega)
    have hes := e.contDiff_evaluate a ha
    have hfs := f.contDiff_evaluate a ha
    change ‖iteratedFDeriv ℝ j (e.evaluate a + f.evaluate a) x‖ ≤ _
    rw [iteratedFDeriv_add_apply (hes.of_le (by simp)).contDiffAt
      (hfs.of_le (by simp)).contDiffAt]
    apply (norm_add_le _ _).trans
    change _ ≤ (e.jetConstant M j + f.jetConstant M j) *
      L ^ (j + max e.derivativeCost f.derivativeCost - R)
    rw [add_mul]
    apply add_le_add
    · exact he'.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by omega)) (e.jetConstant_nonneg M hM j))
    · exact hf'.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by omega)) (f.jetConstant_nonneg M hM j))
  | bilinear B e f he hf =>
    apply (B.norm_iteratedFDeriv_le_of_bilinear
      (e.contDiff_evaluate a ha) (f.contDiff_evaluate a ha) x (by simp : (j : ℕ∞ω) ≤ ∞)).trans
    change _ ≤ (‖B‖ * ∑ k ∈ Finset.range (j + 1),
      (j.choose k : ℝ) * e.jetConstant M k * f.jetConstant M (j - k)) *
        L ^ (j + (e.derivativeCost + f.derivativeCost) - R)
    rw [mul_assoc, Finset.sum_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Finset.sum_le_sum
    intro k hk
    have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have he' := he k (by dsimp [derivativeCost] at hbudget; omega)
    have hf' := hf (j - k) (by dsimp [derivativeCost] at hbudget; omega)
    calc
      _ ≤ (j.choose k : ℝ) * (e.jetConstant M k * L ^ (k + e.derivativeCost - R)) *
          (f.jetConstant M (j - k) * L ^ (j - k + f.derivativeCost - R)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he' (Nat.cast_nonneg _)) hf'
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (e.jetConstant_nonneg M hM k) (pow_nonneg hL0 _)))
      _ = ((j.choose k : ℝ) * e.jetConstant M k * f.jetConstant M (j - k)) *
          L ^ ((k + e.derivativeCost - R) + (j - k + f.derivativeCost - R)) := by
        rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by
          have := truncated_product_exponent (k + e.derivativeCost)
            (j - k + f.derivativeCost) R
          omega))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (e.jetConstant_nonneg M hM k))
          (f.jetConstant_nonneg M hM (j - k)))
  | deriv v e he =>
    apply (norm_iteratedFDeriv_clm_apply_const
      ((e.contDiff_evaluate a ha).fderiv_right (by simp)).contDiffAt
        (by simp : (j : ℕ∞ω) ≤ ∞)).trans
    rw [norm_iteratedFDeriv_fderiv]
    have he' := mul_le_mul_of_nonneg_left (he (j + 1)
      (by dsimp [derivativeCost] at hbudget; omega)) (norm_nonneg v)
    simpa only [jetConstant, derivativeCost, Nat.add_assoc, Nat.add_comm 1,
      mul_assoc] using he'

end AmplitudeExpression
end JanetCartan.IsometricEmbedding.Response.NearCarrier
