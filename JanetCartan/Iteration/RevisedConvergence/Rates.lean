module

public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised.StageLosses
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.Construction.Schedule

/-!
# Literal revised decay on the adaptive staircase

The numerical part of `main:eq:final-Cr` in §18 of `paper-v2.tex`.  The loss is
`RevisedScales.displacementLoss`, not the older displacement loss.  All orders
use the same initial scale and the same adaptive schedule.  The physical
Bernstein estimate and the actual compatible increments are separate inputs;
`derivative_bound_of_physical_bounds` combines their numerical conclusions
without changing the function, frequency, or accuracy.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace JanetCartan.RevisedConvergence

/-- `main:eq:final-Cr`: the literal revised fixed loss at derivative order `r`. -/
def derivativeLoss (n r : ℕ) : ℝ :=
  RevisedScales.displacementLoss n + 1 + bandExponent * ((r : ℝ) + (n : ℝ) / 2)

/-- `main:eq:final-Cr`: a derivative budget along the one adaptive staircase. -/
def derivativeBudget (n : ℕ) (H : ℕ → ℝ) (kMin : ℕ) (R₀ : ℝ)
    (C : ℕ → ℝ) (r j : ℕ) : ℝ :=
  C r * iterationScale R₀ growthExponent j ^
    (-(powerAdaptiveSchedule H R₀ growthExponent kMin j : ℝ) + derivativeLoss n r)

/-- `main:eq:final-Cr`: combine the physical Bernstein budget with the revised
L² budget of the **same** increment.  `Cband` and `C` have no accuracy index. -/
theorem derivative_bound_of_physical_bounds {n r k : ℕ}
    {R Cband C size derivative : ℝ} (hR : 0 < R) (hband : 0 ≤ Cband)
    (hC : 0 ≤ C)
    (hbernstein : derivative ≤ C * (Cband * R ^ bandExponent) ^
      ((r : ℝ) + (n : ℝ) / 2) * size)
    (hsize : size ≤ R ^ (-(k : ℝ) + RevisedScales.displacementLoss n + 1)) :
    derivative ≤ (C * Cband ^ ((r : ℝ) + (n : ℝ) / 2)) *
      R ^ (-(k : ℝ) + derivativeLoss n r) := by
  calc
    derivative ≤ C * (Cband * R ^ bandExponent) ^
        ((r : ℝ) + (n : ℝ) / 2) * size := hbernstein
    _ ≤ C * (Cband * R ^ bandExponent) ^ ((r : ℝ) + (n : ℝ) / 2) *
        R ^ (-(k : ℝ) + RevisedScales.displacementLoss n + 1) := by
      exact mul_le_mul_of_nonneg_left hsize
        (mul_nonneg hC (Real.rpow_nonneg (mul_nonneg hband (Real.rpow_nonneg hR.le _)) _))
    _ = _ := by
      rw [Real.mul_rpow hband (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le]
      rw [mul_assoc C, mul_assoc C, mul_assoc (Cband ^ ((r : ℝ) + (n : ℝ) / 2)),
        ← Real.rpow_add hR]
      have hexp : bandExponent * ((r : ℝ) + (n : ℝ) / 2) +
          (-(k : ℝ) + RevisedScales.displacementLoss n + 1) =
          -(k : ℝ) + derivativeLoss n r := by
        dsimp [derivativeLoss]
        ring
      rw [hexp]

/-- `main:eq:staircase`: every scale on this same revised staircase is at least one. -/
theorem one_le_scale {R₀ : ℝ} (hR₀ : 1 ≤ R₀) (j : ℕ) :
    1 ≤ iterationScale R₀ growthExponent j := by
  exact Real.one_le_rpow hR₀ (pow_nonneg (by norm_num [growthExponent]) j)

/-- `main:eq:final-Cr`: each fixed revised derivative budget is summable along the
same adaptive schedule, for arbitrary finite threshold function `H`. -/
theorem summable_derivativeBudget (n : ℕ) (H : ℕ → ℝ) (kMin : ℕ)
    {R₀ : ℝ} (hR₀ : 1 < R₀) (C : ℕ → ℝ) (r : ℕ) :
    Summable (derivativeBudget n H kMin R₀ C r) := by
  exact (summable_powerAdaptiveSchedule_bound H kMin hR₀
    (by norm_num [growthExponent]) (derivativeLoss n r)).mul_left (C r)

/-- The displayed inverse-scale tail after `main:eq:final-Cr`.  Only the start
of the estimate depends on `r`; the map, domain, and adaptive schedule do not. -/
theorem eventually_derivativeBudget_le_inverse (n : ℕ) (H : ℕ → ℝ) (kMin : ℕ)
    {R₀ : ℝ} (hR₀ : 1 < R₀) {C : ℕ → ℝ} (r : ℕ) (hC : 0 ≤ C r) :
    ∀ᶠ j in atTop, derivativeBudget n H kMin R₀ C r j ≤
      C r * (iterationScale R₀ growthExponent j)⁻¹ := by
  filter_upwards [eventually_rpow_order_bound (one_le_scale hR₀.le)
    (powerAdaptiveSchedule_tendsto_atTop (v := growthExponent) H kMin hR₀
      (by norm_num [growthExponent])) (derivativeLoss n r)] with j hj
  exact mul_le_mul_of_nonneg_left hj hC

/-- `main:eq:metric-induction`: the squared defects vanish on the same schedule
used in `derivativeBudget`, independently of all derivative orders. -/
theorem tendsto_metricBudget (H : ℕ → ℝ) (kMin : ℕ) {R₀ : ℝ} (hR₀ : 1 < R₀) :
    Tendsto (fun j ↦ (iterationScale R₀ growthExponent j ^
      (-(powerAdaptiveSchedule H R₀ growthExponent kMin j : ℝ))) ^ 2) atTop (𝓝 0) :=
  tendsto_powerAdaptiveSchedule_metricBudget H kMin hR₀ (by norm_num [growthExponent])

end JanetCartan.RevisedConvergence
