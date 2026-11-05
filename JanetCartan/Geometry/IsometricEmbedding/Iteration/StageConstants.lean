module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.StageConstants.Assembly

/-!
# Uniform finite-stage constants

For Section 9 (`main:sec:convergence`), apply `main:thm:step` at `Q=2k`.
Select the finite primary and cutoff orders, then dominate the finitely used
component constants and thresholds. Every numerical input and every choice
precedes the arbitrary family index (target parameter, initial scale, stage,
and admissible finite history). The outside powers and the support constant 2
are unchanged; the polynomial background exponent is independent of accuracy.

This is a conditional deduction for `jc-uniform-history-step`, not the analytic
producer or a proof of local existence. That consumer must construct the actual
fields, their identities, and the separate uniform smoothing, primary strain,
mean, pair, L², physical Sobolev, and reference derivative estimates. In
particular, no Euclidean/Lebesgue data are identified with torus data here.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.StageConstants

/-- Section 9's finite selection before the target dilation, using
`main:thm:step` at `Q=2k`. Numerical data may depend on the requested accuracy
and the selected proof orders, but never on the family index. Only four Sobolev
orders enter the maximum at any fixed accuracy.

The family can encode any collection of admissible histories. Its analytic
inputs are precisely `Identities` and `ComponentEstimates`; the derivative and
actual cutoff-tail premises of the finite-stage assembler are derived, not
assumed. Instantiation of those analytic inputs belongs to
`jc-uniform-history-step` and its component producers. -/
theorem exists_uniform_correction (n N : ℕ) (Lref : ℝ)
    (c τ : ℕ → ℕ → ℕ → ComponentBounds) (q₀ t₀ : ℕ → ℕ) :
    ∃ (q t : ℕ → ℕ) (C T : ℕ → ℝ),
      (∀ k, q₀ k ≤ q k ∧ t₀ k ≤ t k ∧ 0 < t k ∧ 0 ≤ C k ∧ 1 ≤ T k ∧
        C k = correctionConstant n (t k) (c k (q k) (t k)) ∧
        T k = stageThreshold n (t k) (τ k (q k) (t k))) ∧
      ∀ (k : ℕ) {ι : Type*} (a : ι → Fields n N) (i : ι),
        Identities (a i) →
        ComponentEstimates (c k (q k) (t k)) (τ k (q k) (t k)) Lref k (q k) (t k) (a i) →
        T k ≤ (a i).R →
        ∃ U : Torus n → Euclidean N,
          U = FiniteStage.increment (a i).R (a i).P (a i).W ∧ IsSmoothPeriodic U ∧
          cNorm (a i).D 0 (inducedMetric ((a i).F + periodicLift U) - (a i).g) ≤
            C k * ((a i).δ * (a i).R ^ (-2 * (k : ℝ)) +
              (a i).δ ^ 3 * (a i).R ^ cubicLoss n) ∧
          periodicL2Norm U ≤ C k * (a i).δ * (a i).R ^ displacementLoss n ∧
          HasFourierSupport (2 * (a i).R ^ bandExponent) U ∧
          ∀ r : ℕ, cNorm (fundamentalCell n) r (periodicLift U) ≤
            FiniteStage.crConstant n r (componentConstant n (t k) (c k (q k) (t k))) *
              (a i).δ * ((a i).R ^
                (displacementLoss n + bandExponent * ((r : ℝ) + (n : ℝ) / 2))) := by
  choose q t hq₀ ht₀ htpos hq ht using
    fun (k : ℕ) ↦ FiniteStage.exists_orders n (2 * (k : ℝ))
      (backgroundExponent n Lref) (q₀ k) (t₀ k)
  refine ⟨q, t, (fun k ↦ correctionConstant n (t k) (c k (q k) (t k))),
    (fun k ↦ stageThreshold n (t k) (τ k (q k) (t k))), ?_, ?_⟩
  · intro k
    exact ⟨hq₀ k, ht₀ k, htpos k, correctionConstant_nonneg _ _ _,
      one_le_stageThreshold _ _ _, rfl, rfl⟩
  · intro k ι a i ha he hT
    exact correction_of_profiles _ _ Lref k (q k) (t k) (hq k) (ht k) (a i) ha he hT

end JanetCartan.StageConstants
