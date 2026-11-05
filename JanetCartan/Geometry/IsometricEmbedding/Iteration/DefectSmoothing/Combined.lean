module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.HighTail
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.Normalization

/-!
# Combining the two actual smoothing tails

The geometric mean in `main:eq:smoothing-combined` uses the independently proved
small tail and high tail of the same operator. No minimum-tail bound is assumed.
The conclusion directly supplies the accuracy `Q = 2k` of the finite-stage step.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan.DefectSmoothing

private theorem geometric_mean_tail {E A B δ R : ℝ} {k : ℕ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hR : 0 < R)
    (hsmall : E ≤ A * δ ^ 2) (hhigh : E ≤ B * R ^ (-4 * (k : ℝ))) :
    E ≤ Real.sqrt (A * B) * δ * R ^ (-2 * (k : ℝ)) := by
  have hsquare : (R ^ (-2 * (k : ℝ))) ^ 2 = R ^ (-4 * (k : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hR.le]
    congr 1
    ring
  apply (sq_le_sq₀ hE (by positivity)).mp
  calc
    E ^ 2 ≤ (A * δ ^ 2) * (B * R ^ (-4 * (k : ℝ))) := by
      simpa only [pow_two] using mul_le_mul hsmall hhigh hE (mul_nonneg hA (sq_nonneg δ))
    _ = (Real.sqrt (A * B) * δ * R ^ (-2 * (k : ℝ))) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hA hB), hsquare]
      ring

/-- `main:eq:smoothing-combined` at `Q = 2k`, for the actual locally dilated
target and finite history. The order `smoothingTailOrder k = 140k` is fixed
before the history. Both tails are proved from primitive data; only genuine
zeroth-defect smallness and admissible-history budgets remain quantitative inputs.
This stronger version allows every nonnegative `δ`, hence in particular `R^(-k)`. -/
theorem exists_history_combined_tail_bound {n : ℕ}
    (D : LocalDomain) (G : FlatReference n) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : ContDiffOn ℝ ∞ g U) (hg0 : g 0 = 1)
    {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ s ∈ Icc (0 : ℝ) s₀, ∀ x ∈ D.closureChart n, (s * ρ) • x ∈ U) ∧
      ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
        ∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
          ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
            (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
            ∀ δ : ℝ, 0 ≤ δ →
            cNorm (D.core n) 0
              (historyDefect (fun x ↦ g ((s * ρ) • x)) G.map u) ≤ δ ^ 2 →
            let R := iterationScale R₀ growthExponent j
            cNorm (D.core n) 0
              (historyDefect (fun x ↦ g ((s * ρ) • x)) G.map u -
                periodicLift (smoothedHistoryDefect D R
                  (fun x ↦ g ((s * ρ) • x)) G.map u)) ≤
              C k * δ * R ^ (-2 * (k : ℝ)) := by
  obtain ⟨s₀, hs₀, hs₁, hmaps, B, hB, hhigh⟩ :=
    exists_history_high_tail_bound D G hρ hU h0 hg hg0 horder
  obtain ⟨A, hA, hsmall⟩ := exists_smoothTensor_small_tail_bound (n := n) D
  refine ⟨s₀, hs₀, hs₁, hmaps, fun k ↦ Real.sqrt (A * B (smoothingTailOrder k)),
    fun _ ↦ Real.sqrt_nonneg _, ?_⟩
  intro k s hs R₀ hR₀ j u ell hu δ hδ hdefect
  let R := iterationScale R₀ growthExponent j
  have hR1 : 1 ≤ R := Real.one_le_rpow (by linarith)
    (pow_nonneg (by norm_num [growthExponent]) _)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have ht : ContDiffOn ℝ ∞ (fun x ↦ g ((s * ρ) • x)) (D.chart n) :=
    hg.comp (contDiff_id.const_smul (s * ρ)).contDiffOn
      (fun x hx ↦ hmaps s hs x (Metric.ball_subset_closedBall hx))
  have hsmall' := hsmall R hR1 _ (contDiffOn_historyDefect ht G.contDiff hu) δ hdefect
  have hhigh' := hhigh s hs R₀ hR₀ j u ell hu (smoothingTailOrder k)
  dsimp only at hhigh'
  rw [smoothingTailOrder_scale hR k] at hhigh'
  exact geometric_mean_tail (cNorm_nonneg _ _ _) hA (hB _) hδ hR hsmall' hhigh'

end JanetCartan.DefectSmoothing
