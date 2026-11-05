module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FiniteStage.Fourier
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FiniteStage.Metric

/-!
# Conditional finite-stage correction

This module assembles `main:thm:step` from the preceding analytic estimates.
It constructs one real global increment `periodicCutoff (R^b_*) (P + W₂)` and
proves all four conclusions for that same increment, including every Cʳ order.
The constants B₀, B₃ and b_* and the support constant 2 do not depend on Q.

The hypotheses below are deliberately component estimates: the mean equation,
self/off splitting, smoothing error, primary strain, product response, the L²
and differential profiles of the two cut fields, polynomial background growth,
and the finite-order differential tail of the fixed Fourier cutoff. The latter
two derivative profiles are the Fourier consequences of
`main:eq:joint-physical-profile` used in the manuscript. Their construction from
the wave, sampling, mean and response hypotheses is **not** proved here. No
hypothesis asserts the final increment's metric, L², support, or Cʳ bounds.

Finite proof orders are selected independently of the scale. All real requested
accuracies are covered by using max(Q,0) internally. For families of analytic
inputs valid above a threshold, the result applies at every scale above that
same threshold (and 1), with constants depending only on the input constants.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FiniteStage

variable {n N : ℕ}

/-- `main:thm:step`: choose the primary and final-cutoff proof orders before
choosing R. The extra loss L is the polynomial derivative size of F+P+W₂. -/
theorem exists_orders (n : ℕ) (Q L : ℝ) (q₀ k₀ : ℕ) :
    ∃ q k : ℕ, q₀ ≤ q ∧ k₀ ≤ k ∧ 0 < k ∧
      forcingExponent n + (1 + samplingSlack) / 2 + max Q 0 ≤ carrierExponent * q ∧
      displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2) +
        (max Q 0 + L) ≤ (carrierExponent * cutoffSlack) * k := by
  obtain ⟨q, hq₀, hq, _⟩ := exists_primary_strain_order n (max Q 0) q₀
  obtain ⟨k, hk₀, hkpos, hk, _⟩ := exists_step_cutoff_order n L (max Q 0) k₀
  exact ⟨q, k, hq₀, hk₀, hkpos, hq.le, by linarith⟩

/-- `main:eq:step-error` and `main:eq:step-L2`: a common nonnegative constant
for the metric and displacement estimates. -/
def stageConstant (n : ℕ) (C CF : ℝ) : ℝ := errorConstant n C CF + 2 * C

/-- Conditional `main:thm:step`, with the actual preceding component estimates
as explicit premises. The finite-order primary strain and cutoff tail are
absorbed here, and the exact ledger supplies the residual of the single output.
`exists_orders` supplies q,k for every requested real Q and every fixed loss L.
The analytic construction supplying these component premises remains separate. -/
theorem correction_of_component_estimates
    {F V S : Euclidean n → Euclidean N} {P W : Torus n → Euclidean N}
    {g e eR H Hself Qoff Emean : MetricField n} {D : Set (Euclidean n)}
    {b C CF δ R L Q : ℝ} {q k : ℕ}
    (hC : 0 ≤ C) (hCF : 0 ≤ CF) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : 1 ≤ R) (hL : 0 ≤ L) (hb : b ≠ 0)
    (hq : forcingExponent n + (1 + samplingSlack) / 2 + max Q 0 ≤ carrierExponent * q)
    (hk : displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2) +
      (max Q 0 + L) ≤ (carrierExponent * cutoffSlack) * k)
    (hF : ∀ x ∈ D, DifferentiableAt ℝ F x)
    (hP : IsSmoothPeriodic P) (hW : IsSmoothPeriodic W)
    (hV : ∀ x ∈ D, DifferentiableAt ℝ V x)
    (hS : ∀ x ∈ D, DifferentiableAt ℝ S x)
    (he : Set.EqOn e (g - inducedMetric F) D)
    (hW₂ : periodicLift W = b ^ 2 • V + S)
    (hself : Set.EqOn Hself (b ^ 2 • H) D)
    (hoff : Set.EqOn Qoff (inducedMetric (periodicLift P) - Hself) D)
    (hmean : Set.EqOn Emean (linearizedMetric F V + H - (b ^ 2)⁻¹ • eR) D)
    (hsmoothing : ∀ x ∈ D, ‖eR x - e x‖ ≤ C * δ * R ^ (-max Q 0))
    (hstrain : ∀ x ∈ D, ‖linearizedMetric F (periodicLift P) x‖ ≤
      (C * δ) * (R ^ (forcingExponent n + (1 + samplingSlack) / 2) *
        (R ^ carrierExponent) ^ (-(q : ℝ))))
    (hmeanBound : ∀ x ∈ D, ‖b ^ 2 • Emean x‖ ≤ C * δ * R ^ (-max Q 0))
    (hpair : ∀ x ∈ D, ‖linearizedMetric F S x + Qoff x‖ ≤ C * δ * R ^ (-max Q 0))
    (hPL2 : periodicL2Norm P ≤ C * δ * R ^ displacementLoss n)
    (hWL2 : periodicL2Norm W ≤ C * δ ^ 2 * R ^ displacementLoss n)
    (hDP : ∀ x ∈ D, ‖fderiv ℝ (periodicLift P) x‖ ≤
      C * δ * R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)))
    (hDW : ∀ x ∈ D, ‖fderiv ℝ (periodicLift W) x‖ ≤
      C * δ ^ 2 * R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)))
    (hbackground : ∀ x ∈ D,
      ‖fderiv ℝ (F + periodicLift P + periodicLift W) x‖ ≤ CF * R ^ L)
    (htail : ∀ x ∈ D,
      ‖fderiv ℝ (periodicLift (increment R P W) - (periodicLift P + periodicLift W)) x‖ ≤
        (C * δ) * (R ^ displacementLoss n * (R ^ carrierExponent) ^
          (meanDerivativeLoss n + 1 / 2 - cutoffSlack * k))) :
    ∃ U : Torus n → Euclidean N,
      U = increment R P W ∧ IsSmoothPeriodic U ∧
      0 ≤ stageConstant n C CF ∧
      cNorm D 0 (inducedMetric (F + periodicLift U) - g) ≤
        stageConstant n C CF * (δ * R ^ (-Q) + δ ^ 3 * R ^ cubicLoss n) ∧
      periodicL2Norm U ≤ stageConstant n C CF * δ * R ^ displacementLoss n ∧
      HasFourierSupport (2 * R ^ bandExponent) U ∧
      ∀ r : ℕ, cNorm (fundamentalCell n) r (periodicLift U) ≤
        crConstant n r C * δ *
          R ^ (displacementLoss n + bandExponent * ((r : ℝ) + (n : ℝ) / 2)) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hU := isSmoothPeriodic_periodicCutoff (R ^ bandExponent) (P + W)
  have hstrain' : ∀ x ∈ D, ‖linearizedMetric F (periodicLift P) x‖ ≤
      C * δ * R ^ (-max Q 0) := fun x hx ↦
    carrier_error_le_of_order hR hC hδ.le hq (hstrain x hx)
  have htail' : ∀ x ∈ D,
      ‖fderiv ℝ (periodicLift (increment R P W) - (periodicLift P + periodicLift W)) x‖ ≤
        C * δ * R ^ (-max Q 0 - L) := by
    intro x hx
    have h := cutoff_error_le_of_order hR hC hδ.le hk (htail x hx)
    simpa only [neg_add, sub_eq_add_neg] using h
  have hmetric := metric_error_le hC hCF hδ hδ1 hR hL (le_max_right Q 0) hb
    hF (fun x _ ↦ hP.2.differentiable (by simp) x) hV hS
    (fun x _ ↦ hU.2.differentiable (by simp) x)
    he hW₂ hself hoff hmean hsmoothing hstrain' hmeanBound hpair hDP hDW hbackground htail'
  have herr : 0 ≤ errorConstant n C CF := by unfold errorConstant; positivity
  have hstage : errorConstant n C CF ≤ stageConstant n C CF := by
    unfold stageConstant
    linarith
  refine ⟨increment R P W, rfl, hU, by unfold stageConstant; positivity, ?_, ?_,
    increment_support hP.1 hW.1 hR0, fun r ↦ increment_cNorm_le hP.1 hW.1 hC hδ hδ1 hR
      hPL2 hWL2 r⟩
  · apply hmetric.trans
    apply mul_le_mul hstage
    · apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (le_max_left Q 0))) hδ.le
    · positivity
    · unfold stageConstant
      positivity
  · apply (increment_l2_le hP.1 hW.1 hC hδ hδ1 hR hPL2 hWL2).trans
    gcongr
    unfold stageConstant
    linarith

/-- `main:thm:step`: for every finite real accuracy, choose finite internal
orders and then construct the correction from the preceding analytic estimates.
All order inequalities are discharged here. The universal scale quantifier comes
after the order choice, and the same output satisfies all the displayed bounds.
The remaining premises are exactly the conditional analytic scope described above. -/
theorem exists_correction_of_component_estimates (n N : ℕ) (Q L : ℝ)
    (hL : 0 ≤ L) (q₀ k₀ : ℕ) :
    ∃ q k : ℕ, q₀ ≤ q ∧ k₀ ≤ k ∧ 0 < k ∧
      ∀ {F V S : Euclidean n → Euclidean N} {P W : Torus n → Euclidean N}
        {g e eR H Hself Qoff Emean : MetricField n} {D : Set (Euclidean n)}
        {b C CF δ R : ℝ}
        (_hC : 0 ≤ C) (_hCF : 0 ≤ CF) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
        (_hR : 1 ≤ R) (_hb : b ≠ 0)
        (_hF : ∀ x ∈ D, DifferentiableAt ℝ F x)
        (_hP : IsSmoothPeriodic P) (_hW : IsSmoothPeriodic W)
        (_hV : ∀ x ∈ D, DifferentiableAt ℝ V x)
        (_hS : ∀ x ∈ D, DifferentiableAt ℝ S x)
        (_he : Set.EqOn e (g - inducedMetric F) D)
        (_hW₂ : periodicLift W = b ^ 2 • V + S)
        (_hself : Set.EqOn Hself (b ^ 2 • H) D)
        (_hoff : Set.EqOn Qoff (inducedMetric (periodicLift P) - Hself) D)
        (_hmean : Set.EqOn Emean (linearizedMetric F V + H - (b ^ 2)⁻¹ • eR) D)
        (_hsmoothing : ∀ x ∈ D, ‖eR x - e x‖ ≤ C * δ * R ^ (-max Q 0))
        (_hstrain : ∀ x ∈ D, ‖linearizedMetric F (periodicLift P) x‖ ≤
          (C * δ) * (R ^ (forcingExponent n + (1 + samplingSlack) / 2) *
            (R ^ carrierExponent) ^ (-(q : ℝ))))
        (_hmeanBound : ∀ x ∈ D, ‖b ^ 2 • Emean x‖ ≤ C * δ * R ^ (-max Q 0))
        (_hpair : ∀ x ∈ D, ‖linearizedMetric F S x + Qoff x‖ ≤ C * δ * R ^ (-max Q 0))
        (_hPL2 : periodicL2Norm P ≤ C * δ * R ^ displacementLoss n)
        (_hWL2 : periodicL2Norm W ≤ C * δ ^ 2 * R ^ displacementLoss n)
        (_hDP : ∀ x ∈ D, ‖fderiv ℝ (periodicLift P) x‖ ≤
          C * δ * R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)))
        (_hDW : ∀ x ∈ D, ‖fderiv ℝ (periodicLift W) x‖ ≤
          C * δ ^ 2 * R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)))
        (_hbackground : ∀ x ∈ D,
          ‖fderiv ℝ (F + periodicLift P + periodicLift W) x‖ ≤ CF * R ^ L)
        (_htail : ∀ x ∈ D,
          ‖fderiv ℝ (periodicLift (increment R P W) - (periodicLift P + periodicLift W)) x‖ ≤
            (C * δ) * (R ^ displacementLoss n * (R ^ carrierExponent) ^
              (meanDerivativeLoss n + 1 / 2 - cutoffSlack * k))),
        ∃ U : Torus n → Euclidean N,
          U = increment R P W ∧ IsSmoothPeriodic U ∧
          0 ≤ stageConstant n C CF ∧
          cNorm D 0 (inducedMetric (F + periodicLift U) - g) ≤
            stageConstant n C CF * (δ * R ^ (-Q) + δ ^ 3 * R ^ cubicLoss n) ∧
          periodicL2Norm U ≤ stageConstant n C CF * δ * R ^ displacementLoss n ∧
          HasFourierSupport (2 * R ^ bandExponent) U ∧
          ∀ r : ℕ, cNorm (fundamentalCell n) r (periodicLift U) ≤
            crConstant n r C * δ *
              R ^ (displacementLoss n + bandExponent * ((r : ℝ) + (n : ℝ) / 2)) := by
  obtain ⟨q, k, hq₀, hk₀, hkpos, hq, hk⟩ := exists_orders n Q L q₀ k₀
  refine ⟨q, k, hq₀, hk₀, hkpos, ?_⟩
  intro F V S P W g e eR H Hself Qoff Emean D b C CF δ R
    hC hCF hδ hδ1 hR hb hF hP hW hV hS he hW₂ hself hoff hmean
    hsmoothing hstrain hmeanBound hpair hPL2 hWL2 hDP hDW hbackground htail
  exact correction_of_component_estimates hC hCF hδ hδ1 hR hL hb hq hk
    hF hP hW hV hS he hW₂ hself hoff hmean hsmoothing hstrain hmeanBound hpair
    hPL2 hWL2 hDP hDW hbackground htail

end JanetCartan.FiniteStage
