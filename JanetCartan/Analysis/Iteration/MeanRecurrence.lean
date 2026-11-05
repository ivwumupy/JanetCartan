module

public import JanetCartan.Analysis.Iteration.MeanRecurrence.Estimates
public import JanetCartan.Analysis.Iteration.MeanRecurrence.Precision
import Mathlib.Tactic.Abel

/-!
# A finite nonlinear mean with one fixed row

Conditional finite bookkeeping for `main:lem:mean-recurrence` of paper.tex.
`Q₀` is fixed throughout; `E` and `E₀` are the current and reference prefix
normals. The two canonical linear errors are explicit inputs: a relative normal
comparison and an absolute raw-tail bound, the latter allowed to use the earlier
geometric residual bounds. No residual conclusion is assumed.

The quadratic map is `s ↦ B s s`. Its mixed seminorm bound captures the weighted
C⁰/L² product estimate. Canonical update bounds in any further seminorm yield
uniform accumulated estimates via `accumulated_seminorm_le`.

This module does not prove the analytic canonical estimates, the equal-gap tail
estimate, or the final Sobolev interpolation of the manuscript.
-/

@[expose] public noncomputable section

namespace JanetCartan.MeanRecurrence

open Finset

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `main:eq:full-recursion`: construct the accumulated change and residual,
using the same `Q₀` at every step. -/
def run (Q₀ : Y →ₗ[ℝ] Y) (E : ℕ → Y →ₗ[ℝ] Y)
    (D : ℕ → Y →ₗ[ℝ] X) (B : X →ₗ[ℝ] X →ₗ[ℝ] Y) (e : Y) : ℕ → X × Y
  | 0 => (0, e)
  | l + 1 =>
    let z := run Q₀ E D B e l
    let d := D l z.2
    (z.1 + d, z.2 - E l (Q₀ z.2) - (B (z.1 + d) (z.1 + d) - B z.1 z.1))

/-- `main:lem:mean-recurrence`: the first component of `run` is the sum of
all previous canonical changes. -/
theorem run_accumulated_eq_sum (Q₀ : Y →ₗ[ℝ] Y) (E : ℕ → Y →ₗ[ℝ] Y)
    (D : ℕ → Y →ₗ[ℝ] X) (B : X →ₗ[ℝ] X →ₗ[ℝ] Y) (e : Y) (l : ℕ) :
    (run Q₀ E D B e l).1 = ∑ i ∈ range l, D i (run Q₀ E D B e i).2 := by
  induction l with
  | zero => simp [run]
  | succ l ih =>
    simpa only [run, sum_range_succ] using
      (congrArg (fun s ↦ s + D l (run Q₀ E D B e l).2) ih)

/-- `main:eq:full-recursion`: the constructed iteration satisfies the displayed
residual recurrence with the actual accumulated canonical changes. -/
theorem run_residual_recurrence (Q₀ : Y →ₗ[ℝ] Y) (E : ℕ → Y →ₗ[ℝ] Y)
    (D : ℕ → Y →ₗ[ℝ] X) (B : X →ₗ[ℝ] X →ₗ[ℝ] Y) (e : Y) (l : ℕ) :
    let r := fun i ↦ (run Q₀ E D B e i).2
    let s := ∑ i ∈ range l, D i (r i)
    r (l + 1) = r l - E l (Q₀ (r l)) -
      (B (s + D l (r l)) (s + D l (r l)) - B s s) := by
  dsimp only
  conv_lhs => rw [run]
  simp only [run_accumulated_eq_sum]

/-- `main:eq:linear-two-errors`: the normal-comparison and raw-tail errors add
up to the full linear residual for the fixed row. -/
theorem linear_error_decomposition (Q₀ E E₀ : Y →ₗ[ℝ] Y) (r : Y) :
    r - E (Q₀ r) = (E₀ - E) (Q₀ r) + (r - E₀ (Q₀ r)) := by
  simp only [LinearMap.sub_apply]
  abel

/-- `main:lem:mean-recurrence`: the cumulative full-output identity, obtained
by telescoping the exact recurrence, with no analytic assumptions. -/
theorem residual_eq_source_sub_accumulated
    (Q₀ : Y →ₗ[ℝ] Y) (E : ℕ → Y →ₗ[ℝ] Y)
    (B : X →ₗ[ℝ] X →ₗ[ℝ] Y) (r : ℕ → Y) (d : ℕ → X) (n : ℕ)
    (hstep : ∀ l < n,
      r (l + 1) = r l - E l (Q₀ (r l)) -
        (B ((∑ i ∈ range l, d i) + d l) ((∑ i ∈ range l, d i) + d l) -
          B (∑ i ∈ range l, d i) (∑ i ∈ range l, d i))) :
    r n = r 0 - (∑ i ∈ range n, E i (Q₀ (r i))) -
      B (∑ i ∈ range n, d i) (∑ i ∈ range n, d i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hstep n (by omega)]
    simp only [sum_range_succ]
    rw [ih (fun l hl ↦ hstep l (by omega))]
    abel

/-- `main:lem:mean-recurrence`: finite contraction from the exact recurrence,
the two canonical linear error bounds, and the mixed quadratic bound.

The tail hypothesis is only a bound on `r l - E₀ l (Q₀ (r l))`; it may use the
induction bounds through step `l`. In particular it does not assume the next
residual bound. The budget expresses the large-threshold choice in the paper. -/
theorem residual_geometric_bound
    (Q₀ : Y →ₗ[ℝ] Y) (E E₀ : ℕ → Y →ₗ[ℝ] Y)
    (D : ℕ → Y →ₗ[ℝ] X) (B : X →ₗ[ℝ] X →ₗ[ℝ] Y)
    (p t : Seminorm ℝ X) (r : ℕ → Y) (N : ℕ)
    {ε q C U V α β : ℝ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2)
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V) (hα : 0 ≤ α)
    (hbudget : α + 5 * C * U * V * ε ≤ (1 - β) * q)
    (hB : ∀ x y, ‖B x y‖ ≤ C * p x * t y)
    (hDp : ∀ l < N, ∀ x, p (D l x) ≤ U * ‖x‖)
    (hDt : ∀ l < N, ∀ x, t (D l x) ≤ V * ‖x‖)
    (hnormal : ∀ l < N, ∀ x, ‖(E₀ l - E l) (Q₀ x)‖ ≤ α * ‖x‖)
    (htail : ∀ l < N, (∀ i ≤ l, ‖r i‖ ≤ ε * q ^ i) →
      ‖r l - E₀ l (Q₀ (r l))‖ ≤ β * ε * q ^ (l + 1))
    (hinit : ‖r 0‖ ≤ ε)
    (hstep : ∀ l < N,
      let s := ∑ i ∈ range l, D i (r i)
      r (l + 1) = r l - E l (Q₀ (r l)) -
        (B (s + D l (r l)) (s + D l (r l)) - B s s)) :
    ∀ l ≤ N, ‖r l‖ ≤ ε * q ^ l := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simpa using hinit
    | succ l =>
      have hl : l < N := by omega
      have hprev : ∀ i ≤ l, ‖r i‖ ≤ ε * q ^ i :=
        fun i hi ↦ ih i (by omega) (by omega)
      let s := ∑ i ∈ range l, D i (r i)
      have hps : p s ≤ 2 * U * ε := accumulated_seminorm_le p hε hq hqhalf hU l
        (fun i hi ↦ hprev i (by omega)) (fun i hi ↦ hDp i (by omega) (r i))
      have hts : t s ≤ 2 * V * ε := accumulated_seminorm_le t hε hq hqhalf hV l
        (fun i hi ↦ hprev i (by omega)) (fun i hi ↦ hDt i (by omega) (r i))
      have haε : ‖r l‖ ≤ ε := (hprev l le_rfl).trans (by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq (by linarith)) hε)
      have hnl := norm_quadratic_difference_le_of_sizes B p t hC hU hV hε
        (norm_nonneg (r l)) haε hB hps hts (hDp l hl (r l)) (hDt l hl (r l))
      have hlin : ‖r l - E l (Q₀ (r l))‖ ≤ α * ‖r l‖ + β * ε * q ^ (l + 1) := by
        rw [linear_error_decomposition Q₀ (E l) (E₀ l)]
        exact (norm_add_le _ _).trans (add_le_add (hnormal l hl (r l)) (htail l hl hprev))
      have hcoef : 0 ≤ α + 5 * C * U * V * ε := by positivity
      calc
        ‖r (l + 1)‖ ≤ ‖r l - E l (Q₀ (r l))‖ +
            ‖B (s + D l (r l)) (s + D l (r l)) - B s s‖ := by
          rw [hstep l hl]
          exact norm_sub_le _ _
        _ ≤ (α + 5 * C * U * V * ε) * ‖r l‖ + β * ε * q ^ (l + 1) := by
          linarith
        _ ≤ (α + 5 * C * U * V * ε) * (ε * q ^ l) + β * ε * q ^ (l + 1) := by
          exact add_le_add (mul_le_mul_of_nonneg_left (hprev l le_rfl) hcoef) le_rfl
        _ ≤ ((1 - β) * q) * (ε * q ^ l) + β * ε * q ^ (l + 1) := by
          exact add_le_add (mul_le_mul_of_nonneg_right hbudget (by positivity)) le_rfl
        _ = ε * q ^ (l + 1) := by rw [pow_succ]; ring

/-- `main:eq:linear-two-errors`: when the uncut fixed normal has right inverse
`Q₀`, the reference error is exactly the raw input tail. `P₂` represents the
squared raw cutoff, and `Astar` the fixed row adjoint. -/
theorem reference_error_eq_raw_tail {W : Type*} [AddCommGroup W] [Module ℝ W]
    (A : W →ₗ[ℝ] Y) (Astar : Y →ₗ[ℝ] W) (Q₀ : Y →ₗ[ℝ] Y)
    (P₂ : W →ₗ[ℝ] W) (r : Y) (hinverse : A (Astar (Q₀ r)) = r) :
    r - A (P₂ (Astar (Q₀ r))) = A (((LinearMap.id : W →ₗ[ℝ] W) - P₂) (Astar (Q₀ r))) := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hinverse]

/-- `main:lem:mean-recurrence`: any positive relative accuracy can be reached
in finitely many geometric steps. Canonical estimates only need to be supplied
up to the chosen finite count. -/
theorem exists_precision_steps {q δ : ℝ} (hqhalf : q ≤ 1 / 2) (hδ : 0 < δ) :
    ∃ N : ℕ, q ^ N ≤ δ := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (show q < 1 by linarith)
  exact ⟨N, hN.le⟩

/-- `main:lem:mean-recurrence`: a finite sum of changes stays in any common
linear support space, including a fixed Fourier band once its support space
has been identified. -/
theorem accumulated_mem_submodule (M : Submodule ℝ X) (d : ℕ → X) (N : ℕ)
    (hd : ∀ i < N, d i ∈ M) : (∑ i ∈ range N, d i) ∈ M := by
  exact M.sum_mem (fun i hi ↦ hd i (mem_range.mp hi))

/-- `main:lem:mean-recurrence`: the constructed finite iteration attains the
requested relative precision and has total source size at most `2 * ε`.
Any family of auxiliary/data/derivative updates with seminorm bound
`L * ‖r i‖` accumulates to at most `2 * L * ε`, independently of the precision
and step count. Instantiate `L` with each canonical band profile, bounded at
`Kmax`, to obtain the manuscript's accumulated-size estimates.

This is a conditional bookkeeping theorem: the mixed product estimate, the
canonical update bounds, the normal comparison, and the inductive raw-tail
estimate remain explicit analytic premises. -/
theorem finite_mean_bounds {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    (Q₀ : Y →ₗ[ℝ] Y) (E E₀ : ℕ → Y →ₗ[ℝ] Y)
    (D : ℕ → Y →ₗ[ℝ] X) (B : X →ₗ[ℝ] X →ₗ[ℝ] Y)
    (p t : Seminorm ℝ X) (e : Y) (N : ℕ)
    {ε q C U V α β δ : ℝ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2)
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V) (hα : 0 ≤ α)
    (hbudget : α + 5 * C * U * V * ε ≤ (1 - β) * q)
    (hB : ∀ x y, ‖B x y‖ ≤ C * p x * t y)
    (hDp : ∀ l < N, ∀ x, p (D l x) ≤ U * ‖x‖)
    (hDt : ∀ l < N, ∀ x, t (D l x) ≤ V * ‖x‖)
    (hnormal : ∀ l < N, ∀ x, ‖(E₀ l - E l) (Q₀ x)‖ ≤ α * ‖x‖)
    (htail : ∀ l < N,
      (∀ i ≤ l, ‖(run Q₀ E D B e i).2‖ ≤ ε * q ^ i) →
      ‖(run Q₀ E D B e l).2 - E₀ l (Q₀ (run Q₀ E D B e l).2)‖ ≤
        β * ε * q ^ (l + 1))
    (hinit : ‖e‖ ≤ ε) (hprecision : q ^ N ≤ δ) :
    let r := fun i ↦ (run Q₀ E D B e i).2
    (∀ l ≤ N, ‖r l‖ ≤ ε * q ^ l) ∧
    ‖r N‖ ≤ ε * δ ∧
    (∑ i ∈ range N, ‖r i‖) ≤ 2 * ε ∧
    ∀ (P : Seminorm ℝ Z) (updates : ℕ → Z) (L : ℝ), 0 ≤ L →
      (∀ i < N, P (updates i) ≤ L * ‖r i‖) →
      P (∑ i ∈ range N, updates i) ≤ 2 * L * ε := by
  dsimp only
  have hgeom := residual_geometric_bound Q₀ E E₀ D B p t
    (fun i ↦ (run Q₀ E D B e i).2) N hε hq hqhalf hC hU hV hα hbudget
    hB hDp hDt hnormal htail hinit (fun l _ ↦ run_residual_recurrence Q₀ E D B e l)
  refine ⟨hgeom, (hgeom N le_rfl).trans
    (mul_le_mul_of_nonneg_left hprecision hε), ?_, ?_⟩
  · exact sum_le_two_mul hε hq hqhalf N (fun i hi ↦ hgeom i (by omega))
  · intro P updates L hL hupdates
    exact accumulated_seminorm_le P hε hq hqhalf hL N
      (fun i hi ↦ hgeom i (by omega)) hupdates

end JanetCartan.MeanRecurrence
