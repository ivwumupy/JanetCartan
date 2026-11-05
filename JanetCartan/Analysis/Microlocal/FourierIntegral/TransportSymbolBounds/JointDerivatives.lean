module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Differentiation
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Finite joint derivative budgets for the transport amplitudes

Leibniz convolutions retain one joint derivative count across the primitive
factors in `app:ch_regular_base:eq:direct-graph-amplitudes`. The domain `E` may
contain physical, source, and normalized covector variables simultaneously.
These are bounds on actual Fréchet derivatives, with finite regularity inputs.
Interpolation and radial frequency weights are separate obligations in
`app:ch_regular_base:eq:actual-one-high`.
-/

@[expose] public noncomputable section
open scoped BigOperators ContDiff
namespace JanetCartan.FourierIntegral

/-- The uncollapsed Leibniz budget in
`app:ch_regular_base:eq:joint-primitive-product`. -/
def transportLeibnizBound (p q : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * p i * q (n - i)

/-- Monotonicity uses only derivative indices at most `n`, for
`app:ch_regular_base:eq:actual-one-high`. -/
theorem transportLeibnizBound_mono {p q P Q : ℕ → ℝ} {n : ℕ}
    (hp : ∀ i ≤ n, 0 ≤ p i) (hQ : ∀ i ≤ n, 0 ≤ Q i)
    (hpP : ∀ i ≤ n, p i ≤ P i) (hqQ : ∀ i ≤ n, q i ≤ Q i) :
    transportLeibnizBound p q n ≤ transportLeibnizBound P Q n := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hni : n - i ≤ n := Nat.sub_le _ _
  exact (mul_le_mul_of_nonneg_left (hqQ _ hni)
    (mul_nonneg (Nat.cast_nonneg _) (hp i hi'))).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpP i hi') (Nat.cast_nonneg _)) (hQ _ hni))

variable {ι : Type*} [Fintype ι]

/-- Primitive budget for both terms of `b₋₁` in
`app:ch_regular_base:eq:direct-graph-amplitudes`. Each summand allocates a total
of `n` derivatives, including the derivatives landing on the phase Hessian. -/
def correctionDerivativeBound (c1 dU : ι → ℕ → ℝ)
    (c2 S : ι → ι → ℕ → ℝ) (U : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j, transportLeibnizBound (c1 j) (dU j) n) +
    (1 / 2 : ℝ) * ∑ j, ∑ l,
      transportLeibnizBound (S j l) (transportLeibnizBound (c2 j l) U) n

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℂ R]
local instance : NormedAlgebra ℝ R := NormedAlgebra.restrictScalars ℝ ℂ R

/-- Finite joint regularity of the actual correction amplitude in
`app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem contDiff_correctionAmplitude {N : ℕ∞ω}
    {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hc1 : ∀ j, ContDiff ℝ N (c1 j)) (hdU : ∀ j, ContDiff ℝ N (dU j))
    (hc2 : ∀ j l, ContDiff ℝ N (c2 j l))
    (hS : ∀ j l, ContDiff ℝ N (S j l)) (hU : ContDiff ℝ N U) :
    ContDiff ℝ N (fun x ↦ correctionAmplitude (fun j ↦ c1 j x)
      (fun j ↦ dU j x) (fun j l ↦ c2 j l x) (fun j l ↦ S j l x) (U x)) :=
  ((ContDiff.sum fun j _ ↦ (hc1 j).mul (hdU j)).const_smul _).sub
    ((ContDiff.sum fun j _ ↦ ContDiff.sum fun l _ ↦
      (hS j l).smul ((hc2 j l).mul hU)).const_smul _)

/-- Finite joint derivative bound for `b₀`, keeping the shared derivative
budget in `app:ch_regular_base:eq:actual-one-high`. -/
theorem norm_iteratedFDeriv_leadingAmplitude_le {N : ℕ∞ω} {c U : E → R}
    (hc : ContDiff ℝ N c) (hU : ContDiff ℝ N U) (x : E) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y ↦ leadingAmplitude (c y) (U y)) x‖ ≤
      transportLeibnizBound (fun k ↦ ‖iteratedFDeriv ℝ k c x‖)
        (fun k ↦ ‖iteratedFDeriv ℝ k U x‖) n :=
  norm_iteratedFDeriv_mul_le hc hU x hn

/-- The joint derivative bound for the literal `b₋₁` is expressed solely in
primitive derivatives (`app:ch_regular_base:eq:direct-graph-amplitudes`). -/
theorem norm_iteratedFDeriv_correctionAmplitude_le {N : ℕ∞ω}
    {c1 dU : ι → E → R} {c2 : ι → ι → E → R}
    {S : ι → ι → E → ℂ} {U : E → R}
    (hc1 : ∀ j, ContDiff ℝ N (c1 j)) (hdU : ∀ j, ContDiff ℝ N (dU j))
    (hc2 : ∀ j l, ContDiff ℝ N (c2 j l))
    (hS : ∀ j l, ContDiff ℝ N (S j l)) (hU : ContDiff ℝ N U)
    (x : E) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y ↦ correctionAmplitude (fun j ↦ c1 j y)
      (fun j ↦ dU j y) (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y)) x‖ ≤
      correctionDerivativeBound (fun j k ↦ ‖iteratedFDeriv ℝ k (c1 j) x‖)
        (fun j k ↦ ‖iteratedFDeriv ℝ k (dU j) x‖)
        (fun j l k ↦ ‖iteratedFDeriv ℝ k (c2 j l) x‖)
        (fun j l k ↦ ‖iteratedFDeriv ℝ k (S j l) x‖)
        (fun k ↦ ‖iteratedFDeriv ℝ k U x‖) n := by
  have hp (j : ι) := ((hc1 j).mul (hdU j)).of_le hn
  have hq (j l : ι) : ContDiff ℝ n (fun y ↦ S j l y • (c2 j l y * U y)) :=
    ((hS j l).smul ((hc2 j l).mul hU)).of_le hn
  have hs1 := ContDiff.sum (fun j (_ : j ∈ Finset.univ) ↦ hp j)
  have hs2 := ContDiff.sum (fun j (_ : j ∈ Finset.univ) ↦
    ContDiff.sum (fun l (_ : l ∈ Finset.univ) ↦ hq j l))
  simp only [correctionAmplitude,
    fun_iteratedFDeriv_sub_apply (hs1.const_smul _).contDiffAt (hs2.const_smul _).contDiffAt,
    iteratedFDeriv_const_smul_apply' hs1.contDiffAt,
    iteratedFDeriv_const_smul_apply' hs2.contDiffAt]
  apply (norm_sub_le _ _).trans
  simp only [norm_smul, norm_neg, Complex.norm_I, norm_div, Complex.norm_ofNat,
    one_mul, correctionDerivativeBound]
  apply add_le_add
  · rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦ (hp j).contDiffAt)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦
      norm_iteratedFDeriv_mul_le (hc1 j) (hdU j) x hn)
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦
      (ContDiff.sum fun l (_ : l ∈ Finset.univ) ↦ hq j l).contDiffAt)]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [iteratedFDeriv_fun_sum_apply (fun l _ ↦ (hq j l).contDiffAt)]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro l _
    apply (norm_iteratedFDeriv_smul_le (hS j l) ((hc2 j l).mul hU) x hn).trans
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact norm_iteratedFDeriv_mul_le (hc2 j l) hU x
      ((show ((n - i : ℕ) : ℕ∞ω) ≤ n by exact_mod_cast Nat.sub_le n i).trans hn)

end JanetCartan.FourierIntegral
