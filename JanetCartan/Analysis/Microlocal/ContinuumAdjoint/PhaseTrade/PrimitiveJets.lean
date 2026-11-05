module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.PrimitiveJets.PullbackBound

/-!
# Primitive jets for rectangular phase trading

For `app:ch_background:eq:bg-derivative-trade`, both actual rectangular inputs
are bounded by one additive high norm of the primitive phase and carrier.
The fixed reserve is three derivatives, with primitive C³ bounds as the only
low-norm hypotheses. The estimate includes order zero, so the rational inverse
estimates in `PhaseTrade.Literal` can obtain their low-range bounds from it.

The proof combines fixed linear extraction from the differentiated pulled-back
phase gradient with its primitive composition bound. Instantiating the smooth
Hamilton phase, carrier graph and primitive budgets remains the responsibility
of the continuum initial-adjoint construction.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint

/-- Uniform one-high bound for the actual rectangular phase inputs, using only
primitive phase and carrier norms. The constant is chosen before `S` and `ζ`,
and the fixed reserve three also applies at `k = 0`. This supplies the input
jets and low-range bounds for the rational coefficient estimates in
`PhaseTrade.Literal`. Sources: `app:ch_background:eq:bg-derivative-trade` and
`app:ch_regular_base:lem:buffered-interpolation`. -/
theorem exists_cNorm_transversePhaseInputs_le_primitives
    {n p : ℕ} (q₀ : Euclidean n × Euclidean p) {ρ R : ℝ}
    (hρ : 0 < ρ) (a : Euclidean n × Euclidean (n - 1)) (hR : 0 < R)
    {M : ℝ} (hM : 0 ≤ M) (k : ℕ) :
    ∃ C > 0, ∀ (S : Euclidean n → Euclidean (n - 1) → ℝ)
      (ζ : Euclidean p → Euclidean (n - 1)),
      ContDiff ℝ ∞ (Function.uncurry S) → ContDiff ℝ ∞ ζ →
      Set.MapsTo (fun q ↦ (q.1, ζ q.2)) (Metric.closedBall q₀ ρ)
        (Metric.closedBall a R) →
      cNorm (Metric.closedBall a R) 3 (Function.uncurry S) ≤ M →
      cNorm (Metric.closedBall q₀.2 ρ) 3 ζ ≤ M →
      cNorm (Metric.closedBall q₀ ρ) k (fun q ↦ transversePhaseMatrix S q.1 (ζ q.2)) +
        cNorm (Metric.closedBall q₀ ρ) k (transversePhaseInputs S ζ) ≤
        C * (1 + cNorm (Metric.closedBall a R) (k + 3) (Function.uncurry S) +
          cNorm (Metric.closedBall q₀.2 ρ) (k + 3) ζ) := by
  obtain ⟨C₁, hC₁, hinputs⟩ := exists_cNorm_transversePhaseInputs_le_gradientPullback n p k
  obtain ⟨C₂, hC₂, hpullback⟩ :=
    exists_cNorm_transversePhaseGradientPullback_le_primitives q₀ hρ a hR hM k
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro S ζ hS hζ hmap hSlow hζlow
  calc
    _ ≤ C₁ * cNorm (Metric.closedBall q₀ ρ) (k + 1)
        (transversePhaseGradientPullback S ζ) :=
      hinputs _ (isCompact_closedBall q₀ ρ) S ζ hS hζ
    _ ≤ C₁ * (C₂ * (1 + cNorm (Metric.closedBall a R) (k + 3) (Function.uncurry S) +
        cNorm (Metric.closedBall q₀.2 ρ) (k + 3) ζ)) :=
      mul_le_mul_of_nonneg_left (hpullback S ζ hS hζ hmap hSlow hζlow) hC₁.le
    _ = _ := (mul_assoc _ _ _).symm

end JanetCartan.ContinuumAdjoint
