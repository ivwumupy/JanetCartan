module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.TimeIntegral
public import JanetCartan.Analysis.ODE.PositiveTransport.Basic

/-!
# One-high bound for the actual characteristic exponential

The factor in `app:ch_waves:eq:joint-tame` is the literal `transportFactor`.
Its integral, smoothness and exponential estimates are proved here from the
coefficient and a fixed zeroth-order budget. The same ball is used at every
order, and every constant precedes the coefficient and its high norms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.NullTransport.AmplitudeTame

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `app:ch_waves:thm:leading`: joint smoothness of the same literal integral
on a neighborhood of the compact ball. It is derived from the parameter
integral theorem, including at time zero and at the compact boundary. -/
theorem exists_timeIntegral_smooth_near_ball (p : E) {σ : ℝ} (hσ : 0 < σ)
    {U : Set (ℝ × E)} (hU : IsOpen U) (hball : closedBall (0, p) σ ⊆ U)
    {c : ℝ × E → ℝ} (hc : ContDiffOn ℝ ∞ c U) :
    ∃ W : Set (ℝ × E), IsOpen W ∧ closedBall (0, p) σ ⊆ W ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) W := by
  obtain ⟨W, hW, hKW, ha⟩ := exists_timeAverage_smooth_near_ball p hσ hU hball hc
  refine ⟨W, hW, hKW, ?_⟩
  apply (contDiffOn_fst.mul ha).congr
  intro q _
  exact timeIntegral_eq_time_mul_average c q

/-- `app:ch_waves:eq:joint-tame`: the actual flow exponential is bounded
linearly in the coefficient's high norm. The only fixed low budget is `C⁰`
of the coefficient; no bound for the integral or exponential is assumed.
There is no derivative loss, and the compact domain is fixed at all orders. -/
theorem exists_cNorm_transportFactor_le_same_ball (p : E) {σ : ℝ} (hσ : 0 < σ)
    (m : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (ℝ × E)), IsOpen U → closedBall (0, p) σ ⊆ U →
      ∀ c : ℝ × E → ℝ, ContDiffOn ℝ ∞ c U → cNorm (closedBall (0, p) σ) 0 c ≤ M →
        cNorm (closedBall (0, p) σ) m
            (fun q : ℝ × E ↦ transportFactor (fun s ↦ c (s, q.2)) 0 q.1) ≤
          C * (1 + cNorm (closedBall (0, p) σ) m c) := by
  obtain ⟨C₀, hC₀, hI₀⟩ := exists_cNorm_timeIntegral_le_same_ball p hσ 0
  obtain ⟨Cₘ, hCₘ, hIₘ⟩ := exists_cNorm_timeIntegral_le_same_ball p hσ m
  obtain ⟨Cₑ, hCₑ, hE⟩ := exists_cNorm_exp_neg_le_joint_tame_closedBall
    ((0 : ℝ), p) hσ m (C₀ * M)
  refine ⟨Cₑ * (1 + Cₘ), mul_pos hCₑ (by linarith), ?_⟩
  intro U hU hball c hc hcM
  obtain ⟨W, hW, hKW, hI⟩ := exists_timeIntegral_smooth_near_ball p hσ hU hball hc
  have hlow : cNorm (closedBall (0, p) σ) 0
      (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) ≤ C₀ * M :=
    (hI₀ U hU hball c hc).trans (mul_le_mul_of_nonneg_left hcM hC₀.le)
  have hhigh := hIₘ U hU hball c hc
  apply (hE W hW hKW _ hI hlow).trans
  have hnonneg := cNorm_nonneg (closedBall ((0 : ℝ), p) σ) m c
  have hh : 1 + cNorm (closedBall (0, p) σ) m
      (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) ≤
        (1 + Cₘ) * (1 + cNorm (closedBall (0, p) σ) m c) := by nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hCₑ.le

/-- `app:ch_waves:eq:joint-tame`: one sequence of constants, fixed before
the coefficient and all orders, controls the same characteristic exponential
on the same compact ball. Its actual coefficient along the forward flow is
supplied by composition from the local amplitude construction. -/
theorem exists_transportFactor_cNorm_bounds (p : E) {σ : ℝ} (hσ : 0 < σ) (M : ℝ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (U : Set (ℝ × E)), IsOpen U → closedBall (0, p) σ ⊆ U →
      ∀ c : ℝ × E → ℝ, ContDiffOn ℝ ∞ c U → cNorm (closedBall (0, p) σ) 0 c ≤ M →
      ∀ m, cNorm (closedBall (0, p) σ) m
          (fun q : ℝ × E ↦ transportFactor (fun s ↦ c (s, q.2)) 0 q.1) ≤
        C m * (1 + cNorm (closedBall (0, p) σ) m c) := by
  choose C hC hb using fun m ↦ exists_cNorm_transportFactor_le_same_ball p hσ m M
  exact ⟨C, hC, fun U hU hball c hc hM m ↦ hb m U hU hball c hc hM⟩

end JanetCartan.NullTransport.AmplitudeTame
