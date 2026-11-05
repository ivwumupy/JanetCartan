module

public import JanetCartan.Analysis.Iteration.AdaptiveSchedule
public import JanetCartan.Geometry.IsometricEmbedding.Scales
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative induction for the two metric errors

Scalar estimates for `main:eq:step-error`, `main:eq:metric-two-errors`, and
`main:eq:metric-induction` in `paper.tex`. The finite-stage estimate is an explicit
input: this module does not construct the geometric correction.

The defect is bounded by the **square** of its amplitude. With accuracy `Q = 2k`,
the linear-accuracy and cubic terms are bounded by one common power. The strict
margin in `main:eq:k-cubic` absorbs their constants at finite, nondecreasing
thresholds. These thresholds may dominate any prescribed analytic thresholds.
The induction uses the existing `powerAdaptiveSchedule` without reconstructing it.

`exists_fixed_adaptive_metricError_induction` specializes to the manuscript's
fixed exponents and amplitude `R_j ^ (-k_j)`, retaining both initial-order
conditions. The more general results allow amplitude `ε * R_j ^ (-k_j)` for
`0 < ε ≤ 1`. Neither the finite-stage analytic estimate nor the initial defect
bound is proved here; both remain explicit inputs to the scalar induction.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- The margin in `main:eq:k-cubic` persists at every order above the initial order. -/
theorem cubicExponent_margin {v B : ℝ} {k₀ k : ℕ}
    (hv : v < 3 / 2) (hk : k₀ ≤ k)
    (hgap : B + 2 * v + 4 < (3 - 2 * v) * k₀) :
    4 < 3 * (k : ℝ) - B - 2 * v * ((k : ℝ) + 1) := by
  have hk' : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have := mul_le_mul_of_nonneg_left hk' (show 0 ≤ 3 - 2 * v by linarith)
  nlinarith

/-- The two terms in `main:eq:step-error` share the exponent `-3k + B` when
`Q ≥ 2k`. This also allows an actual amplitude below `ε R⁻ᵏ` (`main:eq:Q-choice`). -/
theorem twoMetricErrors_le {R C ε δ B k Q : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hδ : 0 ≤ δ) (hδk : δ ≤ ε * R ^ (-k)) (hB : 0 ≤ B) (hQ : 2 * k ≤ Q) :
    C * (δ * R ^ (-Q) + δ ^ 3 * R ^ B) ≤
      2 * C * ε * R ^ (-3 * k + B) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlin : δ * R ^ (-Q) ≤ ε * R ^ (-3 * k + B) := by
    calc
      δ * R ^ (-Q) ≤ (ε * R ^ (-k)) * R ^ (-Q) :=
        mul_le_mul_of_nonneg_right hδk (Real.rpow_nonneg hRpos.le _)
      _ = ε * R ^ (-k - Q) := by rw [sub_eq_add_neg, Real.rpow_add hRpos]; ring
      _ ≤ ε * R ^ (-3 * k + B) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) hε
  have hεcube : ε ^ 3 ≤ ε := by nlinarith [mul_nonneg hε (sub_nonneg.mpr hε₁)]
  have hcub : δ ^ 3 * R ^ B ≤ ε * R ^ (-3 * k + B) := by
    calc
      δ ^ 3 * R ^ B ≤ (ε * R ^ (-k)) ^ 3 * R ^ B :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ hδk 3)
          (Real.rpow_nonneg hRpos.le _)
      _ = ε ^ 3 * R ^ (-3 * k + B) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hRpos.le, mul_assoc,
          ← Real.rpow_add hRpos]
        congr 2
        push_cast
        ring
      _ ≤ ε * R ^ (-3 * k + B) :=
        mul_le_mul_of_nonneg_right hεcube (Real.rpow_nonneg hRpos.le _)
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hlin hcub) hC]

/-- A positive exponent gap absorbs a fixed constant at a finite scale threshold,
as used in `main:eq:metric-two-errors`. The target coefficient may be arbitrarily small. -/
theorem exists_rpow_absorption_threshold {a b η : ℝ} (C : ℝ)
    (hab : a < b) (hη : 0 < η) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ R : ℝ, T ≤ R → C * R ^ a ≤ η * R ^ b := by
  obtain ⟨T, hT⟩ := Filter.tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (sub_pos.mpr hab)) (C / η)
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  have hc : C ≤ η * R ^ (b - a) := by
    have := (div_le_iff₀ hη).mp (hT R ((le_max_right _ _).trans hR))
    linarith
  calc
    C * R ^ a ≤ (η * R ^ (b - a)) * R ^ a :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hRpos.le _)
    _ = η * R ^ b := by rw [mul_assoc, ← Real.rpow_add hRpos]; ring_nf

/-- The order bound `l ≤ k + 1` converts the worst next-step exponent into the
actual squared amplitude budget (`main:eq:metric-induction`), with next scale `R ^ v`. -/
theorem nextMetricBudget {R ε v : ℝ} {k l : ℕ}
    (hR : 1 ≤ R) (hv : 0 ≤ v) (hl : l ≤ k + 1) :
    ε ^ 2 * R ^ (-2 * v * ((k : ℝ) + 1)) ≤ (ε * (R ^ v) ^ (-(l : ℝ))) ^ 2 := by
  rw [mul_pow, ← Real.rpow_mul_natCast (Real.rpow_nonneg (by linarith) v),
    ← Real.rpow_mul (show 0 ≤ R by linarith)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ε)
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hl' : (l : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hl
  push_cast
  nlinarith

/-- At each fixed order, a positive cubic exponent margin supplies a finite threshold
for advancing the squared amplitude budget (`main:eq:metric-two-errors`). -/
theorem exists_twoMetricErrors_threshold {ε v B : ℝ} (C : ℝ) (k : ℕ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hv : 0 ≤ v) (hgap : B + 2 * v * ((k : ℝ) + 1) < 3 * k) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (R δ : ℝ) (l : ℕ), T ≤ R →
      0 ≤ δ → δ ≤ ε * R ^ (-(k : ℝ)) → l ≤ k + 1 →
      C * (δ * R ^ (-2 * (k : ℝ)) + δ ^ 3 * R ^ B) ≤
        (ε * (R ^ v) ^ (-(l : ℝ))) ^ 2 := by
  obtain ⟨T, hT, hbound⟩ := exists_rpow_absorption_threshold
    (a := -3 * k + B) (b := -2 * v * ((k : ℝ) + 1)) (2 * C * ε)
    (by linarith) (sq_pos_of_pos hε)
  refine ⟨T, hT, ?_⟩
  intro R δ l hR hδ hδk hl
  have hR₁ := hT.trans hR
  calc
    _ ≤ 2 * C * ε * R ^ (-3 * (k : ℝ) + B) :=
      by simpa only [neg_mul] using
        (twoMetricErrors_le hR₁ hC hε.le hε₁ hδ hδk hB (le_refl _))
    _ ≤ ε ^ 2 * R ^ (-2 * v * ((k : ℝ) + 1)) := hbound R hR
    _ ≤ _ := nextMetricBudget hR₁ hv hl

private def thresholdEnvelope (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => max 2 (f 0)
  | k + 1 => max (thresholdEnvelope f k) (f (k + 1))

private theorem thresholdEnvelope_monotone (f : ℕ → ℝ) :
    Monotone (thresholdEnvelope f) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

private theorem le_thresholdEnvelope (f : ℕ → ℝ) (k : ℕ) :
    f k ≤ thresholdEnvelope f k := by
  cases k <;> exact le_max_right _ _

/-- Finite nondecreasing thresholds for the two-error estimate, dominating any
prescribed analytic thresholds `H₀` (Section 9, `main:eq:metric-two-errors`).
The constants `C k` represent the finite-stage constants at accuracy `2k`. -/
theorem exists_metricError_thresholds {ε v B : ℝ} {k₀ : ℕ}
    (C H₀ : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hv : 0 ≤ v) (hv₁ : v < 3 / 2)
    (hB : 0 ≤ B) (hgap : B + 2 * v + 4 < (3 - 2 * v) * k₀) :
    ∃ H : ℕ → ℝ, Monotone H ∧ (∀ k, 2 ≤ H k ∧ H₀ k ≤ H k) ∧
      ∀ k, k₀ ≤ k → ∀ (R δ : ℝ) (l : ℕ), H k ≤ R →
        0 ≤ δ → δ ≤ ε * R ^ (-(k : ℝ)) → l ≤ k + 1 →
        C k * (δ * R ^ (-2 * (k : ℝ)) + δ ^ 3 * R ^ B) ≤
          (ε * (R ^ v) ^ (-(l : ℝ))) ^ 2 := by
  have hpoint : ∀ k : ℕ, ∃ T : ℝ, 1 ≤ T ∧ (k₀ ≤ k →
      ∀ (R δ : ℝ) (l : ℕ), T ≤ R →
        0 ≤ δ → δ ≤ ε * R ^ (-(k : ℝ)) → l ≤ k + 1 →
        C k * (δ * R ^ (-2 * (k : ℝ)) + δ ^ 3 * R ^ B) ≤
          (ε * (R ^ v) ^ (-(l : ℝ))) ^ 2) := by
    intro k
    by_cases hk : k₀ ≤ k
    · obtain ⟨T, hT, hbound⟩ := exists_twoMetricErrors_threshold (C k) k
        hε hε₁ (hC k) hB hv (by have := cubicExponent_margin hv₁ hk hgap; linarith)
      exact ⟨T, hT, fun _ => hbound⟩
    · exact ⟨1, le_refl _, fun h => (hk h).elim⟩
  choose T hT hbound using hpoint
  let f := fun k => max (T k) (H₀ k)
  refine ⟨thresholdEnvelope f, thresholdEnvelope_monotone f, ?_, ?_⟩
  · intro k
    exact ⟨(le_max_left 2 (f 0)).trans
      (thresholdEnvelope_monotone f (Nat.zero_le k)),
      (le_max_right _ _).trans (le_thresholdEnvelope f k)⟩
  · intro k hk R δ l hR hδ hδk hl
    exact hbound k hk R δ l
      ((le_max_left _ _).trans ((le_thresholdEnvelope f k).trans hR)) hδ hδk hl

/-- The manuscript's explicit last inequality in `main:eq:metric-two-errors`:
if `R ≥ 2` and the stage constant is at most `R`, the cubic margin absorbs both errors. -/
theorem metricTwoErrors_absorb {R C v B : ℝ} {k₀ k : ℕ}
    (hR : 2 ≤ R) (hC : C ≤ R) (hv : v < 3 / 2) (hk : k₀ ≤ k)
    (hgap : B + 2 * v + 4 < (3 - 2 * v) * k₀) :
    2 * C * R ^ (-3 * (k : ℝ) + B) ≤ R ^ (-2 * v * ((k : ℝ) + 1)) := by
  have hRpos : 0 < R := by linarith
  have hcoef : 2 * C ≤ R ^ 2 := by nlinarith
  calc
    _ ≤ R ^ 2 * R ^ (-3 * (k : ℝ) + B) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hRpos.le _)
    _ = R ^ (-3 * (k : ℝ) + B + 2) := by
      rw [Real.rpow_add hRpos (-3 * (k : ℝ) + B) 2, Real.rpow_two]
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith)
      (by have := cubicExponent_margin hv hk hgap; linarith)

/-- The exact scale recurrence used in `main:eq:metric-induction`. -/
theorem iterationScale_succ_rpow {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (v : ℝ) (j : ℕ) :
    iterationScale R₀ v (j + 1) = (iterationScale R₀ v j) ^ v := by
  simp only [iterationScale, pow_succ, Real.rpow_mul hR₀]

/-- Conditional metric-defect induction for `main:eq:metric-induction`.
Thresholds are constructed here. The analytic input `hstep` is precisely the
finite-stage bound `main:eq:step-error` with `Q = 2k`; the initial defect is also
an input. Here `E j` is the metric defect, while `δ j` is its prescribed amplitude. -/
theorem exists_adaptive_metricError_induction {ε v B : ℝ} {k₀ : ℕ}
    (C H₀ : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hv : 1 ≤ v) (hv₁ : v < 3 / 2)
    (hB : 0 ≤ B) (hgap : B + 2 * v + 4 < (3 - 2 * v) * k₀) :
    ∃ H : ℕ → ℝ, Monotone H ∧ (∀ k, 2 ≤ H k ∧ H₀ k ≤ H k) ∧
      ∀ (R₀ : ℝ) (E : ℕ → ℝ), H k₀ ≤ R₀ →
        E 0 ≤ (ε * R₀ ^ (-(k₀ : ℝ))) ^ 2 →
        (let R := iterationScale R₀ v
         let k := powerAdaptiveSchedule H R₀ v k₀
         let δ := fun j => ε * R j ^ (-(k j : ℝ))
         (∀ j, E j ≤ (δ j) ^ 2 →
           E (j + 1) ≤ C (k j) *
             (δ j * R j ^ (-2 * (k j : ℝ)) + (δ j) ^ 3 * R j ^ B)) →
         ∀ j, E j ≤ (δ j) ^ 2) := by
  obtain ⟨H, hH, hH₀, hbound⟩ := exists_metricError_thresholds C H₀ hC
    hε hε₁ (by linarith) hv₁ hB hgap
  refine ⟨H, hH, hH₀, ?_⟩
  intro R₀ E hR₀ hE₀
  dsimp only
  intro hstep j
  have hR₀₁ : 1 ≤ R₀ := by have := (hH₀ k₀).1.trans hR₀; linarith
  have hRpos (i : ℕ) : 0 ≤ iterationScale R₀ v i :=
    Real.rpow_nonneg (by linarith) _
  induction j with
  | zero => simpa using hE₀
  | succ j ih =>
    apply (hstep j ih).trans
    have h := hbound (powerAdaptiveSchedule H R₀ v k₀ j)
      (initialOrder_le_adaptiveSchedule H (iterationScale R₀ v) k₀ j)
      (iterationScale R₀ v j)
      (ε * iterationScale R₀ v j ^ (-(powerAdaptiveSchedule H R₀ v k₀ j : ℝ)))
      (powerAdaptiveSchedule H R₀ v k₀ (j + 1))
      (powerAdaptiveSchedule_threshold hR₀₁ hv hR₀ j)
      (mul_nonneg hε.le (Real.rpow_nonneg (hRpos j) _))
      (le_refl _) (adaptiveSchedule_succ_le H (iterationScale R₀ v) k₀ j)
    simpa only [iterationScale_succ_rpow (show 0 ≤ R₀ by linarith)] using h

/-- Nonnegativity of the fixed loss `B₃` in `main:eq:step-error`, needed to bound
the linear-accuracy error by the same power as the cubic error. -/
theorem cubicLoss_nonneg (n : ℕ) : 0 ≤ cubicLoss n := by
  unfold cubicLoss displacementLoss forcingExponent meanDerivativeLoss
    meanSlack samplingSlack carrierExponent
  positivity

/-- Verification of `main:eq:k-cubic` at the fixed growth exponent from `Scales`. -/
theorem fixed_cubicExponent_margin {n k₀ k : ℕ} (hk : k₀ ≤ k)
    (hgap : cubicLoss n + 2 * growthExponent + 4 <
      (3 - 2 * growthExponent) * k₀) :
    4 < 3 * (k : ℝ) - cubicLoss n - 2 * growthExponent * ((k : ℝ) + 1) :=
  cubicExponent_margin (by norm_num [growthExponent]) hk hgap

/-- The scalar induction of `main:eq:metric-induction` with the manuscript's fixed
exponents, `Q(k) = 2k`, and `δ_j = R_j⁻ᵏʲ`. The chosen initial order satisfies both
`main:eq:k-cubic` and `main:eq:k-history`. The remaining inputs are the initial
metric bound and the finite-stage analytic error estimate, not the induction conclusion. -/
theorem exists_fixed_adaptive_metricError_induction (n r : ℕ)
    (C H₀ : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) :
    ∃ k₀ : ℕ,
      cubicLoss n + 2 * growthExponent + 4 < (3 - 2 * growthExponent) * k₀ ∧
      displacementLoss n + bandExponent * (r + (n : ℝ) / 2) + 2 < k₀ ∧
      ∃ H : ℕ → ℝ, Monotone H ∧ (∀ k, 2 ≤ H k ∧ H₀ k ≤ H k) ∧
        ∀ (R₀ : ℝ) (E : ℕ → ℝ), H k₀ ≤ R₀ →
          E 0 ≤ (R₀ ^ (-(k₀ : ℝ))) ^ 2 →
          (let R := iterationScale R₀ growthExponent
           let k := powerAdaptiveSchedule H R₀ growthExponent k₀
           let δ := fun j => R j ^ (-(k j : ℝ))
           (∀ j, E j ≤ (δ j) ^ 2 →
             E (j + 1) ≤ C (k j) *
               (δ j * R j ^ (-2 * (k j : ℝ)) + (δ j) ^ 3 * R j ^ cubicLoss n)) →
           ∀ j, E j ≤ (δ j) ^ 2) := by
  obtain ⟨k₀, hcubic, hhistory⟩ := exists_initial_order n r
  refine ⟨k₀, hcubic, hhistory, ?_⟩
  simpa only [one_mul] using exists_adaptive_metricError_induction
    (ε := 1) C H₀ hC zero_lt_one (le_refl _) (by norm_num [growthExponent])
    (by norm_num [growthExponent]) (cubicLoss_nonneg n) hcubic

/-- The amplitude lies in `(0, 1]`, as required by the finite-stage theorem,
for the budgets used in `main:eq:metric-induction`. -/
theorem metricErrorAmplitude_pos_le_one {ε R : ℝ} (k : ℕ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hR : 1 ≤ R) :
    0 < ε * R ^ (-(k : ℝ)) ∧ ε * R ^ (-(k : ℝ)) ≤ 1 := by
  have hRpos : 0 < R := by linarith
  refine ⟨mul_pos hε (Real.rpow_pos_of_pos hRpos _), ?_⟩
  have hp : R ^ (-(k : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hR
      (show -(k : ℝ) ≤ 0 from neg_nonpos.mpr (Nat.cast_nonneg k))
  exact (mul_le_mul_of_nonneg_left hp hε.le).trans (by simpa using hε₁)

/-- The squared metric budget yields the corresponding amplitude bound
(`main:eq:metric-induction`). No nonnegativity assumption on the scalar defect is needed. -/
theorem metricError_sqrt_le {E ε R : ℝ} {k : ℕ}
    (hε : 0 ≤ ε) (hR : 0 ≤ R) (hE : E ≤ (ε * R ^ (-(k : ℝ))) ^ 2) :
    Real.sqrt E ≤ ε * R ^ (-(k : ℝ)) :=
  Real.sqrt_le_iff.mpr ⟨mul_nonneg hε (Real.rpow_nonneg hR _), hE⟩

/-- Amplitude form of `main:eq:metric-induction`: a nonnegative sequence `δ_j`
remains below `ε R_j⁻ᵏʲ` when its next square satisfies the finite-stage two-error
bound. This theorem constructs the thresholds and discharges the scalar step estimate. -/
theorem exists_adaptive_amplitude_induction {ε v B : ℝ} {k₀ : ℕ}
    (C H₀ : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hv : 1 ≤ v) (hv₁ : v < 3 / 2)
    (hB : 0 ≤ B) (hgap : B + 2 * v + 4 < (3 - 2 * v) * k₀) :
    ∃ H : ℕ → ℝ, Monotone H ∧ (∀ k, 2 ≤ H k ∧ H₀ k ≤ H k) ∧
      ∀ (R₀ : ℝ) (δ : ℕ → ℝ), H k₀ ≤ R₀ → (∀ j, 0 ≤ δ j) →
        δ 0 ≤ ε * R₀ ^ (-(k₀ : ℝ)) →
        (let R := iterationScale R₀ v
         let k := powerAdaptiveSchedule H R₀ v k₀
         (∀ j, δ j ≤ ε * R j ^ (-(k j : ℝ)) →
           (δ (j + 1)) ^ 2 ≤ C (k j) *
             (δ j * R j ^ (-2 * (k j : ℝ)) + (δ j) ^ 3 * R j ^ B)) →
         ∀ j, δ j ≤ ε * R j ^ (-(k j : ℝ))) := by
  obtain ⟨H, hH, hH₀, hbound⟩ := exists_metricError_thresholds C H₀ hC
    hε hε₁ (by linarith) hv₁ hB hgap
  refine ⟨H, hH, hH₀, ?_⟩
  intro R₀ δ hR₀ hδ hδ₀
  dsimp only
  intro hstep j
  have hR₀₁ : 1 ≤ R₀ := by have := (hH₀ k₀).1.trans hR₀; linarith
  have hRpos (i : ℕ) : 0 ≤ iterationScale R₀ v i :=
    Real.rpow_nonneg (by linarith) _
  induction j with
  | zero => simpa using hδ₀
  | succ j ih =>
    apply (sq_le_sq₀ (hδ (j + 1))
      (mul_nonneg hε.le (Real.rpow_nonneg (hRpos (j + 1)) _))).mp
    apply (hstep j ih).trans
    have h := hbound (powerAdaptiveSchedule H R₀ v k₀ j)
      (initialOrder_le_adaptiveSchedule H (iterationScale R₀ v) k₀ j)
      (iterationScale R₀ v j) (δ j)
      (powerAdaptiveSchedule H R₀ v k₀ (j + 1))
      (powerAdaptiveSchedule_threshold hR₀₁ hv hR₀ j)
      (hδ j) ih (adaptiveSchedule_succ_le H (iterationScale R₀ v) k₀ j)
    simpa only [iterationScale_succ_rpow (show 0 ≤ R₀ by linarith)] using h

/-- The fixed growth exponent has positive cubic gap `1/12` (`main:eq:k-cubic`). -/
theorem fixed_metricError_exponents :
    1 < growthExponent ∧ growthExponent < 3 / 2 ∧
      3 - 2 * growthExponent = 1 / 12 := by
  norm_num [growthExponent]

/-- Exact arithmetic form of `main:eq:k-cubic` for the fixed exponent `v = 35/24`. -/
theorem fixed_cubic_order_iff (n k : ℕ) :
    cubicLoss n + 2 * growthExponent + 4 < (3 - 2 * growthExponent) * k ↔
      12 * cubicLoss n + 83 < k := by
  norm_num only [growthExponent] at *
  constructor <;> intro h <;> linarith

end JanetCartan
