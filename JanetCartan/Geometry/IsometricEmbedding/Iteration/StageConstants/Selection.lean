module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.StageConstants.Components

/-!
# Finite numerical bounds for the stage

Section 9 chooses constants before the target dilation. Only the constants and
thresholds used by `main:thm:step` at the selected finite orders occur below.
-/

@[expose] public noncomputable section

namespace JanetCartan.StageConstants

/-- A nonnegative common coefficient for the two physical profiles in
`main:eq:joint-physical-profile`, at just one order. -/
def profileConstant (c : ComponentBounds) (r : ℕ) : ℝ :=
  max 0 (max (c.primarySobolev r) (c.secondarySobolev r))

/-- Constant in the C¹ consequence of `main:eq:joint-physical-profile`. -/
def derivativeConstant (n : ℕ) (c : ComponentBounds) : ℝ :=
  fourierInterpolationConstant n 1 (interpolationOrder n) *
    (profileConstant c 0 + profileConstant c (interpolationOrder n))

/-- Constant of the actual fixed-cutoff tail in `main:thm:step`. -/
def tailConstant (n t : ℕ) (c : ComponentBounds) : ℝ :=
  2 * (fourierInterpolationConstant n 1 (interpolationOrder n) *
    (profileConstant c t + profileConstant c (interpolationOrder n + t)))

/-- The finitely many constants consumed by the finite-stage assembler at
`main:thm:step`. The reference constant is handled separately. -/
def usedConstants (n t : ℕ) (c : ComponentBounds) : Finset ℝ :=
  {c.smoothing, c.strain, c.mean, c.pair, c.primaryL2, c.secondaryL2,
    derivativeConstant n c, tailConstant n t c}

/-- A common nonnegative constant for exactly the finite list in `main:thm:step`. -/
def componentConstant (n t : ℕ) (c : ComponentBounds) : ℝ :=
  (insert 0 (usedConstants n t c)).max' (by simp)

/-- Nonnegativity needed by `FiniteStage.correction_of_component_estimates`. -/
theorem componentConstant_nonneg (n t : ℕ) (c : ComponentBounds) :
    0 ≤ componentConstant n t c :=
  Finset.le_max' _ _ (by simp)

/-- Each actually consumed constant is bounded by the selected common constant
for `main:thm:step`. No bound uniform in all Sobolev orders is taken. -/
theorem le_componentConstant {n t : ℕ} {c : ComponentBounds} {x : ℝ}
    (hx : x ∈ usedConstants n t c) : x ≤ componentConstant n t c :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem hx)

/-- The finitely many analytic thresholds used by `main:thm:step`. -/
def usedThresholds (n t : ℕ) (τ : ComponentBounds) : Finset ℝ :=
  {τ.smoothing, τ.strain, τ.mean, τ.pair, τ.primaryL2, τ.secondaryL2, τ.reference} ∪
    (profileOrders n t).image τ.primarySobolev ∪
    (profileOrders n t).image τ.secondarySobolev

/-- Section 9's finite threshold at one accuracy; the later monotone envelope
and adaptive iteration are separate consumers. -/
def stageThreshold (n t : ℕ) (τ : ComponentBounds) : ℝ :=
  (insert 1 (usedThresholds n t τ)).max' (by simp)

/-- The finite threshold ensures the scale condition of `main:thm:step`. -/
theorem one_le_stageThreshold (n t : ℕ) (τ : ComponentBounds) :
    1 ≤ stageThreshold n t τ := Finset.le_max' _ _ (by simp)

/-- Each separate analytic threshold is met above the common threshold in
Section 9's uniform-constant selection. -/
theorem le_stageThreshold {n t : ℕ} {τ : ComponentBounds} {x : ℝ}
    (hx : x ∈ usedThresholds n t τ) : x ≤ stageThreshold n t τ :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem hx)

end JanetCartan.StageConstants
