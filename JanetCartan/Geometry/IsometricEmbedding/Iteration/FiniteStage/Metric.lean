module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricLedger
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricRemainder
public import JanetCartan.Analysis.Iteration.FiniteAccuracy

/-!
# Summing the finite-stage metric errors

This is the conditional metric part of `main:thm:step`. Its inputs are the
individual smoothing, primary strain, mean, product, and derivative estimates.
The exact ledger and actual quadratic tensors produce the final residual.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FiniteStage

variable {n N : ℕ}

/-- `main:eq:step-error`: the constant after summing the four linear errors,
the cubic interaction, and the final metric cutoff error. -/
def errorConstant (n : ℕ) (C CF : ℝ) : ℝ :=
  4 * C + 3 * n * C ^ 2 + n * (2 * CF * C + C ^ 2)

/-- `main:eq:metric-ledger` implies `main:eq:step-error`. The hypotheses refer
to the separate constructed fields and their actual derivatives, never to the
final metric residual. The cutoff tail includes the background growth loss L. -/
theorem metric_error_le
    {F P V S W U : Euclidean n → Euclidean N}
    {g e eR H Hself Qoff Emean : MetricField n} {D : Set (Euclidean n)}
    {b C CF δ R L Q : ℝ}
    (hC : 0 ≤ C) (hCF : 0 ≤ CF) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : 1 ≤ R) (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hb : b ≠ 0)
    (hF : ∀ x ∈ D, DifferentiableAt ℝ F x)
    (hP : ∀ x ∈ D, DifferentiableAt ℝ P x)
    (hV : ∀ x ∈ D, DifferentiableAt ℝ V x)
    (hS : ∀ x ∈ D, DifferentiableAt ℝ S x)
    (hU : ∀ x ∈ D, DifferentiableAt ℝ U x)
    (he : Set.EqOn e (g - inducedMetric F) D)
    (hW : W = b ^ 2 • V + S)
    (hself : Set.EqOn Hself (b ^ 2 • H) D)
    (hoff : Set.EqOn Qoff (inducedMetric P - Hself) D)
    (hmean : Set.EqOn Emean (linearizedMetric F V + H - (b ^ 2)⁻¹ • eR) D)
    (hsmoothing : ∀ x ∈ D, ‖eR x - e x‖ ≤ C * δ * R ^ (-Q))
    (hstrain : ∀ x ∈ D, ‖linearizedMetric F P x‖ ≤ C * δ * R ^ (-Q))
    (hmeanBound : ∀ x ∈ D, ‖b ^ 2 • Emean x‖ ≤ C * δ * R ^ (-Q))
    (hpair : ∀ x ∈ D, ‖linearizedMetric F S x + Qoff x‖ ≤ C * δ * R ^ (-Q))
    (hDP : ∀ x ∈ D, ‖fderiv ℝ P x‖ ≤
      C * δ * R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)))
    (hDW : ∀ x ∈ D, ‖fderiv ℝ W x‖ ≤
      C * δ ^ 2 * R ^ (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)))
    (hbackground : ∀ x ∈ D, ‖fderiv ℝ (F + P + W) x‖ ≤ CF * R ^ L)
    (htail : ∀ x ∈ D, ‖fderiv ℝ (U - (P + W)) x‖ ≤ C * δ * R ^ (-Q - L)) :
    cNorm D 0 (inducedMetric (F + U) - g) ≤
      errorConstant n C CF * (δ * R ^ (-Q) + δ ^ 3 * R ^ cubicLoss n) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  apply cNorm_zero_le_of_norm_bound (by unfold errorConstant; positivity)
  intro x hx
  have hWx : DifferentiableAt ℝ W x := hW ▸ ((hV x hx).const_smul _).add (hS x hx)
  have hEx := (hU x hx).sub ((hP x hx).add hWx)
  have hBx := ((hF x hx).add (hP x hx)).add hWx
  have hcut : ‖metricRemainder (F + P + W) (U - (P + W)) x‖ ≤
      n * (2 * CF * C + C ^ 2) * δ * R ^ (-Q) := by
    have hc := cNorm_metric_cutoff_le (s := {x})
      (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hBx)
      (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hEx)
      hCF hC hδ hδ1 hR hL hQ
      (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using hbackground x hx)
      (fun y hy ↦ by simpa only [Set.mem_singleton_iff.mp hy] using htail x hx)
    simpa only [cNorm_order_zero, Set.image_singleton, csSup_singleton, Pi.sub_apply,
      inducedMetric_add_sub_eq_metricRemainder hBx hEx] using hc
  have hcubic : ‖metricRemainder P W x‖ ≤
      3 * n * C ^ 2 * δ ^ 3 * R ^ cubicLoss n := by
    have h := norm_metricRemainder_le_rpow hC hδ hδ1 hR0.le (hDP x hx) (hDW x hx)
    have heq : 2 * (displacementLoss n + carrierExponent * (meanDerivativeLoss n + 1 / 2)) =
        cubicLoss n := by unfold cubicLoss; ring
    rwa [heq] at h
  have hledger := inducedMetric_metricLedger_cutoff (hF x hx) (hP x hx)
    (hV x hx) (hS x hx) hEx hb (he hx) hW (hself hx) (hoff hx) (hmean hx) rfl
  have hgroup : inducedMetric (F + U) x - g x =
      ((((eR x - e x) + linearizedMetric F P x) + b ^ 2 • Emean x) +
        (linearizedMetric F S x + Qoff x)) + metricRemainder P W x +
        metricRemainder (F + P + W) (U - (P + W)) x := by
    rw [hledger]
    simp only [metricRemainder, Pi.add_apply]
    abel
  change ‖inducedMetric (F + U) x - g x‖ ≤ _
  rw [hgroup]
  have h01 := (norm_add_le (eR x - e x) (linearizedMetric F P x)).trans
    (add_le_add (hsmoothing x hx) (hstrain x hx))
  have h012 := (norm_add_le _ (b ^ 2 • Emean x)).trans
    (add_le_add h01 (hmeanBound x hx))
  have h0123 := (norm_add_le _ (linearizedMetric F S x + Qoff x)).trans
    (add_le_add h012 (hpair x hx))
  have h01234 := (norm_add_le _ (metricRemainder P W x)).trans
    (add_le_add h0123 hcubic)
  apply ((norm_add_le _ _).trans (add_le_add h01234 hcut)).trans
  dsimp only [errorConstant]
  have ha : 0 ≤ δ * R ^ (-Q) := by positivity
  have hb' : 0 ≤ δ ^ 3 * R ^ cubicLoss n := by positivity
  nlinarith [mul_nonneg (show 0 ≤ 4 * C + n * (2 * CF * C + C ^ 2) by positivity) hb',
    mul_nonneg (show 0 ≤ 3 * n * C ^ 2 by positivity) ha]

end JanetCartan.FiniteStage
