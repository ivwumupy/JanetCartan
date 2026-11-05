module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite estimates for the mean recurrence

The bookkeeping of `main:lem:mean-recurrence` in paper.tex. Two seminorms retain
its mixed weighted C⁰/L² estimate; no choice of matrix norm or Fourier convention
is made here.
-/

@[expose] public noncomputable section

namespace JanetCartan.MeanRecurrence

open Finset

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `main:lem:mean-recurrence`: geometric residuals have total size at most `2 * ε`,
independently of the number of steps. -/
theorem sum_le_two_mul {a : ℕ → ℝ} {ε q : ℝ} (hε : 0 ≤ ε)
    (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) (n : ℕ)
    (ha : ∀ i < n, a i ≤ ε * q ^ i) :
    ∑ i ∈ range n, a i ≤ 2 * ε := by
  calc
    ∑ i ∈ range n, a i ≤ ∑ i ∈ range n, ε * (1 / 2 : ℝ) ^ i := by
      apply sum_le_sum
      intro i hi
      exact (ha i (mem_range.mp hi)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqhalf i) hε)
    _ = ε * ∑ i ∈ range n, (1 / 2 : ℝ) ^ i := (mul_sum ..).symm
    _ ≤ ε * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hε
    _ = 2 * ε := mul_comm ..

/-- `main:lem:mean-recurrence`: the sum of per-update sizes is bounded
uniformly in the number of steps. This also applies to scalar analytic size
functionals before they have been packaged as seminorms. -/
theorem sum_update_sizes_le {a b : ℕ → ℝ} {ε q L : ℝ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) (hL : 0 ≤ L) (n : ℕ)
    (ha : ∀ i < n, a i ≤ ε * q ^ i) (hb : ∀ i < n, b i ≤ L * a i) :
    ∑ i ∈ range n, b i ≤ 2 * L * ε := by
  calc
    _ ≤ ∑ i ∈ range n, L * a i := sum_le_sum (fun i hi ↦ hb i (mem_range.mp hi))
    _ = L * ∑ i ∈ range n, a i := (mul_sum ..).symm
    _ ≤ L * (2 * ε) := mul_le_mul_of_nonneg_left
      (sum_le_two_mul hε hq hqhalf n ha) hL
    _ = 2 * L * ε := by ring

/-- `main:lem:mean-recurrence`: a per-update seminorm bound accumulates by the
sum of source residual sizes. It applies separately at every derivative order. -/
theorem seminorm_sum_le (p : Seminorm ℝ X) {d : ℕ → X} {a : ℕ → ℝ}
    {L : ℝ} (n : ℕ) (hd : ∀ i < n, p (d i) ≤ L * a i) :
    p (∑ i ∈ range n, d i) ≤ L * ∑ i ∈ range n, a i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ, mul_add]
    exact (map_add_le_add p _ _).trans
      (add_le_add (ih fun i hi ↦ hd i (by omega)) (hd n (by omega)))

/-- `main:lem:mean-recurrence`: all canonical size estimates with a uniform
per-step factor `L` have an accuracy-independent accumulated bound. -/
theorem accumulated_seminorm_le (p : Seminorm ℝ X) {d : ℕ → X}
    {a : ℕ → ℝ} {ε q L : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hqhalf : q ≤ 1 / 2) (hL : 0 ≤ L) (n : ℕ)
    (ha : ∀ i < n, a i ≤ ε * q ^ i)
    (hd : ∀ i < n, p (d i) ≤ L * a i) :
    p (∑ i ∈ range n, d i) ≤ 2 * L * ε := by
  calc
    _ ≤ L * ∑ i ∈ range n, a i := seminorm_sum_le p n hd
    _ ≤ L * (2 * ε) := mul_le_mul_of_nonneg_left
      (sum_le_two_mul hε hq hqhalf n ha) hL
    _ = 2 * L * ε := by ring

/-- `main:eq:full-recursion`: the exact increment of a quadratic map. Symmetry
of the bilinear map is unnecessary. -/
theorem quadratic_difference (B : X →ₗ[ℝ] X →ₗ[ℝ] Y) (s d : X) :
    B (s + d) (s + d) - B s s = B s d + B d s + B d d := by
  simp only [map_add, LinearMap.add_apply]
  abel

/-- `main:lem:mean-recurrence`: the mixed estimate for the nonlinear difference. -/
theorem norm_quadratic_difference_le (B : X →ₗ[ℝ] X →ₗ[ℝ] Y)
    (p t : Seminorm ℝ X) {C : ℝ}
    (hB : ∀ x y, ‖B x y‖ ≤ C * p x * t y) (s d : X) :
    ‖B (s + d) (s + d) - B s s‖ ≤
      C * (p s * t d + p d * t s + p d * t d) := by
  rw [quadratic_difference]
  calc
    _ ≤ ‖B s d‖ + ‖B d s‖ + ‖B d d‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C * p s * t d + C * p d * t s + C * p d * t d :=
      add_le_add (add_le_add (hB s d) (hB d s)) (hB d d)
    _ = _ := by ring

/-- `main:lem:mean-recurrence`: if the past residual sum is at most `2 * ε`
and the current residual is at most `ε`, the quadratic increment is at most
`5 * C * U * V * ε` times the current residual. In the manuscript,
`U = C₀ Kmax^(n/2)` and `V = C₀ Kmax^(1/2)`. -/
theorem norm_quadratic_difference_le_of_sizes
    (B : X →ₗ[ℝ] X →ₗ[ℝ] Y) (p t : Seminorm ℝ X)
    {C U V ε a : ℝ} (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hε : 0 ≤ ε) (ha : 0 ≤ a) (haε : a ≤ ε)
    (hB : ∀ x y, ‖B x y‖ ≤ C * p x * t y)
    {s d : X} (hps : p s ≤ 2 * U * ε) (hts : t s ≤ 2 * V * ε)
    (hpd : p d ≤ U * a) (htd : t d ≤ V * a) :
    ‖B (s + d) (s + d) - B s s‖ ≤ 5 * C * U * V * ε * a := by
  have h₁ := mul_le_mul hps htd (apply_nonneg t d) (by positivity : 0 ≤ 2 * U * ε)
  have h₂ := mul_le_mul hpd hts (apply_nonneg t s) (mul_nonneg hU ha)
  have h₃ := mul_le_mul hpd htd (apply_nonneg t d) (mul_nonneg hU ha)
  have h₄ := mul_le_mul_of_nonneg_left haε (by positivity : 0 ≤ U * V * a)
  calc
    _ ≤ C * (p s * t d + p d * t s + p d * t d) :=
      norm_quadratic_difference_le B p t hB s d
    _ ≤ C * (5 * U * V * ε * a) := by
      apply mul_le_mul_of_nonneg_left _ hC
      nlinarith
    _ = _ := by ring

end JanetCartan.MeanRecurrence
