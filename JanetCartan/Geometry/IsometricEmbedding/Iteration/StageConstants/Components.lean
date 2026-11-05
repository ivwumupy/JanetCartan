module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FiniteStage
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FiniteStage.Profiles

/-!
# Inputs for uniform finite-stage bookkeeping

These are the actual component fields and the lower-level estimates in
`main:thm:step`. They contain neither a correction nor a bound on its metric
error. The consumer is `StageConstants.exists_uniform_correction` and ultimately
`jc-uniform-history-step`. All norms retain the shared torus conventions.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.StageConstants

/-- Separate numerical inputs to `main:thm:step`. The same shape also records
separate thresholds. No uniformity in the Sobolev order is required. -/
structure ComponentBounds where
  smoothing : ℝ
  strain : ℝ
  mean : ℝ
  pair : ℝ
  primaryL2 : ℝ
  secondaryL2 : ℝ
  primarySobolev : ℕ → ℝ
  secondarySobolev : ℕ → ℝ
  reference : ℝ

/-- The actual fields in `main:eq:metric-ledger`, before the final cutoff.
A family index may encode the target parameter, scale, stage and finite history. -/
structure Fields (n N : ℕ) where
  R : ℝ
  δ : ℝ
  b : ℝ
  D : Set (Euclidean n)
  F : Euclidean n → Euclidean N
  P : Torus n → Euclidean N
  V : Euclidean n → Euclidean N
  S : Euclidean n → Euclidean N
  W : Torus n → Euclidean N
  g : MetricField n
  e : MetricField n
  eR : MetricField n
  H : MetricField n
  Hself : MetricField n
  Qoff : MetricField n
  Emean : MetricField n

/-- Exact identities and regularity used by `main:eq:metric-ledger`.
In particular the secondary field is literally `b² V + S`. -/
structure Identities {n N : ℕ} (a : Fields n N) : Prop where
  amplitude_pos : 0 < a.δ
  amplitude_le_one : a.δ ≤ 1
  b_ne_zero : a.b ≠ 0
  differentiable_F : ∀ x ∈ a.D, DifferentiableAt ℝ a.F x
  smooth_P : IsSmoothPeriodic a.P
  smooth_W : IsSmoothPeriodic a.W
  differentiable_V : ∀ x ∈ a.D, DifferentiableAt ℝ a.V x
  differentiable_S : ∀ x ∈ a.D, DifferentiableAt ℝ a.S x
  defect : Set.EqOn a.e (a.g - inducedMetric a.F) a.D
  secondary : periodicLift a.W = a.b ^ 2 • a.V + a.S
  self : Set.EqOn a.Hself (a.b ^ 2 • a.H) a.D
  off : Set.EqOn a.Qoff (inducedMetric (periodicLift a.P) - a.Hself) a.D
  mean : Set.EqOn a.Emean
    (linearizedMetric a.F a.V + a.H - (a.b ^ 2)⁻¹ • a.eR) a.D

/-- A single fixed Sobolev interpolation order for `main:eq:joint-physical-profile`.
It does not depend on accuracy or history. -/
def interpolationOrder (n : ℕ) : ℕ := n + 2

/-- Only these four profile orders are consumed in `main:thm:step`. -/
def profileOrders (n t : ℕ) : Finset ℕ := {0, interpolationOrder n, t, interpolationOrder n + t}

/-- The separate analytic inputs to `main:thm:step` at accuracy `Q = 2k`.
Each estimate has its own threshold. There are no derivative estimates for
`P`, `W`, their sum with `F`, or the final cutoff tail among the premises:
those will be derived from the finitely many physical Sobolev profiles.
The reference derivative exponent `Lref` is fixed before `k`. -/
structure ComponentEstimates {n N : ℕ} (c τ : ComponentBounds)
    (Lref : ℝ) (k q t : ℕ) (a : Fields n N) : Prop where
  smoothing : τ.smoothing ≤ a.R → ∀ x ∈ a.D,
    ‖a.eR x - a.e x‖ ≤ c.smoothing * a.δ * a.R ^ (-2 * (k : ℝ))
  strain : τ.strain ≤ a.R → ∀ x ∈ a.D,
    ‖linearizedMetric a.F (periodicLift a.P) x‖ ≤
      (c.strain * a.δ) * (a.R ^ (forcingExponent n + (1 + samplingSlack) / 2) *
        (a.R ^ carrierExponent) ^ (-(q : ℝ)))
  mean : τ.mean ≤ a.R → ∀ x ∈ a.D,
    ‖a.b ^ 2 • a.Emean x‖ ≤ c.mean * a.δ * a.R ^ (-2 * (k : ℝ))
  pair : τ.pair ≤ a.R → ∀ x ∈ a.D,
    ‖linearizedMetric a.F a.S x + a.Qoff x‖ ≤
      c.pair * a.δ * a.R ^ (-2 * (k : ℝ))
  primaryL2 : τ.primaryL2 ≤ a.R →
    periodicL2Norm a.P ≤ c.primaryL2 * a.δ * a.R ^ displacementLoss n
  secondaryL2 : τ.secondaryL2 ≤ a.R →
    periodicL2Norm a.W ≤ c.secondaryL2 * a.δ ^ 2 * a.R ^ displacementLoss n
  primarySobolev : ∀ r ∈ profileOrders n t, τ.primarySobolev r ≤ a.R →
    periodicSobolevNorm r a.P ≤ c.primarySobolev r * a.δ *
      a.R ^ displacementLoss n * (a.R ^ carrierExponent) ^ (r : ℝ)
  secondarySobolev : ∀ r ∈ profileOrders n t, τ.secondarySobolev r ≤ a.R →
    periodicSobolevNorm r a.W ≤ c.secondarySobolev r * a.δ ^ 2 *
      a.R ^ displacementLoss n * (a.R ^ carrierExponent) ^ (r : ℝ)
  reference : τ.reference ≤ a.R → ∀ x ∈ a.D,
    ‖fderiv ℝ a.F x‖ ≤ c.reference * a.R ^ Lref

/-- Fixed polynomial exponent for `d(F+P+W)` in the final-cutoff paragraph of
`main:thm:step`. In particular it is independent of `k`, `q`, and `t`. -/
def backgroundExponent (n : ℕ) (Lref : ℝ) : ℝ :=
  max 0 (max Lref
    (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)))

/-- The interpolation order exceeds `1+n/2`, as required for the C¹ estimates
in `main:thm:step`. -/
theorem interpolationOrder_gt (n : ℕ) : 1 + (n : ℝ) / 2 < interpolationOrder n := by
  simp only [interpolationOrder, Nat.cast_add, Nat.cast_ofNat]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `main:thm:step`: derive the background derivative bound from the reference
and the two component bounds. This supplies the background premise of the
finite-stage assembler without requesting it from the analytic producer. -/
theorem background_derivative_le {n N : ℕ} {a : Fields n N}
    (ha : Identities a) {C CF Lref : ℝ} (hC : 0 ≤ C) (hCF : 0 ≤ CF)
    (hR : 1 ≤ a.R)
    (hF : ∀ x ∈ a.D, ‖fderiv ℝ a.F x‖ ≤ CF * a.R ^ Lref)
    (hP : ∀ x ∈ a.D, ‖fderiv ℝ (periodicLift a.P) x‖ ≤ C * a.δ *
      a.R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)))
    (hW : ∀ x ∈ a.D, ‖fderiv ℝ (periodicLift a.W) x‖ ≤ C * a.δ ^ 2 *
      a.R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2))) :
    ∀ x ∈ a.D, ‖fderiv ℝ (a.F + periodicLift a.P + periodicLift a.W) x‖ ≤
      (CF + 2 * C) * a.R ^ backgroundExponent n Lref := by
  intro x hx
  have hPx := ha.smooth_P.2.differentiable (by simp) x
  have hWx := ha.smooth_W.2.differentiable (by simp) x
  rw [fderiv_add ((ha.differentiable_F x hx).add hPx) hWx,
    fderiv_add (ha.differentiable_F x hx) hPx]
  have hδsq : a.δ ^ 2 ≤ 1 := by nlinarith [ha.amplitude_pos, ha.amplitude_le_one]
  have heF : Lref ≤ backgroundExponent n Lref :=
    (le_max_left _ _).trans (le_max_right _ _)
  have heP : displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2) ≤
      backgroundExponent n Lref := (le_max_right _ _).trans (le_max_right _ _)
  have hf : CF * a.R ^ Lref ≤ CF * a.R ^ backgroundExponent n Lref := by
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR heF) hCF
  have hp : C * a.δ * a.R ^
      (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)) ≤
      C * a.R ^ backgroundExponent n Lref := by
    calc
      _ ≤ C * 1 * a.R ^ backgroundExponent n Lref := by
        gcongr
        exact ha.amplitude_le_one
      _ = _ := by ring
  have hw : C * a.δ ^ 2 * a.R ^
      (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)) ≤
      C * a.R ^ backgroundExponent n Lref := by
    calc
      _ ≤ C * 1 * a.R ^ backgroundExponent n Lref := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ (‖fderiv ℝ a.F x‖ + ‖fderiv ℝ (periodicLift a.P) x‖) +
        ‖fderiv ℝ (periodicLift a.W) x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (CF * a.R ^ backgroundExponent n Lref + C * a.R ^ backgroundExponent n Lref) +
        C * a.R ^ backgroundExponent n Lref :=
      add_le_add (add_le_add ((hF x hx).trans hf) ((hP x hx).trans hp)) ((hW x hx).trans hw)
    _ = _ := by ring

end JanetCartan.StageConstants
