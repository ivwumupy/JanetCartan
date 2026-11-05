module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The adaptive staircase

The numerical schedule of `main:eq:staircase` in Section 9 of `paper.tex`.
First we treat a general scale sequence `R`, then specialize to `R₀ ^ (v ^ j)`.
Thresholds are real numbers, so each threshold is finite. The basic staircase
properties hold even without monotonicity of the threshold function; in particular
they apply to the manuscript's nondecreasing threshold function.
-/

@[expose] public noncomputable section

open Filter

namespace JanetCartan

/-- The adaptive order in `main:eq:staircase`, for a scale sequence `R`.
The order increases by one exactly when the next scale meets the next threshold. -/
def adaptiveSchedule (H R : ℕ → ℝ) (k₀ : ℕ) : ℕ → ℕ
  | 0 => k₀
  | j + 1 => adaptiveSchedule H R k₀ j +
      if H (adaptiveSchedule H R k₀ j + 1) ≤ R (j + 1) then 1 else 0

/-- The initial condition in `main:eq:staircase`. -/
@[simp] theorem adaptiveSchedule_zero (H R : ℕ → ℝ) (k₀ : ℕ) :
    adaptiveSchedule H R k₀ 0 = k₀ := rfl

/-- The recurrence in `main:eq:staircase`. -/
theorem adaptiveSchedule_succ (H R : ℕ → ℝ) (k₀ j : ℕ) :
    adaptiveSchedule H R k₀ (j + 1) = adaptiveSchedule H R k₀ j +
      if H (adaptiveSchedule H R k₀ j + 1) ≤ R (j + 1) then 1 else 0 := rfl

/-- Each step in `main:eq:staircase` either keeps the current order or raises it by one. -/
theorem adaptiveSchedule_step (H R : ℕ → ℝ) (k₀ j : ℕ) :
    adaptiveSchedule H R k₀ (j + 1) = adaptiveSchedule H R k₀ j ∨
      adaptiveSchedule H R k₀ (j + 1) = adaptiveSchedule H R k₀ j + 1 := by
  rw [adaptiveSchedule_succ]
  split <;> simp

/-- The orders in `main:eq:staircase` are nondecreasing. -/
theorem adaptiveSchedule_monotone (H R : ℕ → ℝ) (k₀ : ℕ) :
    Monotone (adaptiveSchedule H R k₀) := by
  apply monotone_nat_of_le_succ
  intro j
  rcases adaptiveSchedule_step H R k₀ j with h | h <;> omega

/-- The one-step upper bound used in `main:eq:metric-induction`. -/
theorem adaptiveSchedule_succ_le (H R : ℕ → ℝ) (k₀ j : ℕ) :
    adaptiveSchedule H R k₀ (j + 1) ≤ adaptiveSchedule H R k₀ j + 1 := by
  rcases adaptiveSchedule_step H R k₀ j with h | h <;> omega

/-- The staircase stays above the initial order, as required in Section 9. -/
theorem initialOrder_le_adaptiveSchedule (H R : ℕ → ℝ) (k₀ j : ℕ) :
    k₀ ≤ adaptiveSchedule H R k₀ j :=
  adaptiveSchedule_monotone H R k₀ (Nat.zero_le j)

/-- The staircase grows by at most the number of elapsed stages (`main:eq:staircase`). -/
theorem adaptiveSchedule_le_initialOrder_add (H R : ℕ → ℝ) (k₀ j : ℕ) :
    adaptiveSchedule H R k₀ j ≤ k₀ + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := adaptiveSchedule_succ_le H R k₀ j
    omega

/-- The threshold invariant following `main:eq:staircase`: an initial threshold
remains satisfied along a nondecreasing scale sequence. -/
theorem adaptiveSchedule_threshold {H R : ℕ → ℝ} {k₀ : ℕ}
    (hR : Monotone R) (h₀ : H k₀ ≤ R 0) (j : ℕ) :
    H (adaptiveSchedule H R k₀ j) ≤ R j := by
  induction j with
  | zero => exact h₀
  | succ j ih =>
    rw [adaptiveSchedule_succ]
    split
    · assumption
    · simpa only [Nat.add_zero] using ih.trans (hR (Nat.le_succ j))

/-- Finite thresholds cannot trap the staircase at a bounded order (Section 9,
following `main:eq:staircase`). No uniform upper bound on the thresholds is needed. -/
theorem adaptiveSchedule_tendsto_atTop {H R : ℕ → ℝ} (k₀ : ℕ)
    (hR : Tendsto R atTop atTop) :
    Tendsto (adaptiveSchedule H R k₀) atTop atTop := by
  apply (adaptiveSchedule_monotone H R k₀).tendsto_atTop_atTop
  intro n
  induction n with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨J, hJ⟩ := tendsto_atTop_atTop.mp hR (H (n + 1))
    let j := max i J
    have hj : n ≤ adaptiveSchedule H R k₀ j :=
      hi.trans (adaptiveSchedule_monotone H R k₀ (le_max_left i J))
    by_cases hn : n + 1 ≤ adaptiveSchedule H R k₀ j
    · exact ⟨j, hn⟩
    · have heq : adaptiveSchedule H R k₀ j = n := by omega
      have hnext : H (adaptiveSchedule H R k₀ j + 1) ≤ R (j + 1) := by
        rw [heq]
        exact hJ (j + 1) ((le_max_right i J).trans (Nat.le_succ j))
      refine ⟨j + 1, ?_⟩
      rw [adaptiveSchedule_succ, ite_eq_left hnext, heq]

/-- Nondecreasing thresholds remain nondecreasing along the adaptive orders (Section 9). -/
theorem adaptiveSchedule_threshold_monotone {H : ℕ → ℝ} (hH : Monotone H)
    (R : ℕ → ℝ) (k₀ : ℕ) :
    Monotone (fun j => H (adaptiveSchedule H R k₀ j)) :=
  hH.comp (adaptiveSchedule_monotone H R k₀)

/-- The scale sequence `R_j = R₀ ^ (v ^ j)` used in Section 9. -/
def iterationScale (R₀ v : ℝ) (j : ℕ) : ℝ := R₀ ^ (v ^ j)

/-- The scale sequence starts at `R₀` (Section 9). -/
@[simp] theorem iterationScale_zero (R₀ v : ℝ) : iterationScale R₀ v 0 = R₀ := by
  simp [iterationScale]

/-- The scale sequence is nondecreasing for bases and growth exponents at least one
(Section 9, `main:eq:staircase`). -/
theorem iterationScale_monotone {R₀ v : ℝ} (hR₀ : 1 ≤ R₀) (hv : 1 ≤ v) :
    Monotone (iterationScale R₀ v) :=
  (Real.monotone_rpow_of_base_ge_one hR₀).comp (pow_right_mono₀ hv)

/-- The scales tend to infinity when `R₀ > 1` and `v > 1` (Section 9).
In particular this applies to the manuscript's `R₀ ≥ 2`. -/
theorem iterationScale_tendsto_atTop {R₀ v : ℝ} (hR₀ : 1 < R₀) (hv : 1 < v) :
    Tendsto (iterationScale R₀ v) atTop atTop :=
  (tendsto_rpow_atTop_of_base_gt_one R₀ hR₀).comp
    (tendsto_pow_atTop_atTop_of_one_lt hv)

/-- The exact power-scale staircase of `main:eq:staircase`. -/
abbrev powerAdaptiveSchedule (H : ℕ → ℝ) (R₀ v : ℝ) (k₀ : ℕ) : ℕ → ℕ :=
  adaptiveSchedule H (iterationScale R₀ v) k₀

/-- The threshold invariant for the power-scale staircase (`main:eq:staircase`). -/
theorem powerAdaptiveSchedule_threshold {H : ℕ → ℝ} {R₀ v : ℝ} {k₀ : ℕ}
    (hR₀ : 1 ≤ R₀) (hv : 1 ≤ v) (h₀ : H k₀ ≤ R₀) (j : ℕ) :
    H (powerAdaptiveSchedule H R₀ v k₀ j) ≤ iterationScale R₀ v j :=
  adaptiveSchedule_threshold (iterationScale_monotone hR₀ hv) (by simpa using h₀) j

/-- The power-scale staircase tends to infinity (`main:eq:staircase`, Section 9). -/
theorem powerAdaptiveSchedule_tendsto_atTop (H : ℕ → ℝ) (k₀ : ℕ)
    {R₀ v : ℝ} (hR₀ : 1 < R₀) (hv : 1 < v) :
    Tendsto (powerAdaptiveSchedule H R₀ v k₀) atTop atTop :=
  adaptiveSchedule_tendsto_atTop k₀ (iterationScale_tendsto_atTop hR₀ hv)

end JanetCartan
