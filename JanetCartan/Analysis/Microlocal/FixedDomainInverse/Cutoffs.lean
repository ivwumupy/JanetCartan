module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Correction

/-!
# Fixed cutoffs and one localized Neumann inverse

Conditional assembly for `app:ch_regular:thm:exact-correction` in `paper.tex`.
One support choice works uniformly for every complete residual having the given
L²-to-Lᵖ bound. The inverse is the same base-space Neumann series at every order;
the exact one-gain estimate is the input to the graded conclusion.

The actual regular-sector construction, its complete residual estimates, the
concrete Sobolev interpretation, and the phase/symbol estimates of
`app:ch_regular:thm:fixed-high` are not proved in this module. In particular, this
conditional theorem is not a proof of either full manuscript theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace JanetCartan.FixedDomainInverse

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

open SmallSupport

/-- Conditional fixed-domain assembly of `app:ch_regular:thm:exact-correction`.
The smooth nested cutoffs and nonempty open core are chosen before the residual,
the graded scale, the coefficient profile, and the order. For the actual sector
family, the L²-to-Lᵖ and `HasOneGain` premises must still be discharged from the
complete residual theorem. The inverse-tame shift is exactly the input shift `b`.
-/
theorem exists_fixed_cutoffs_neumannInverse
    [Measure.OuterRegular μ] [NullSingletonClass μ]
    (hp : 2 < p) {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (C₀ : ℝ)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ χ₂ χ₃ : ContDiffBump x,
      tsupport (χ₂ : E → ℝ) ⊆ U ∧ tsupport (χ₃ : E → ℝ) ⊆ U ∧
      (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) ∧
      (Metric.ball x χ₂.rIn).Nonempty ∧
      IsOpen (Metric.ball x χ₂.rIn) ∧ Metric.ball x χ₂.rIn ⊆ U ∧
      (∀ y ∈ Metric.ball x χ₂.rIn, χ₂ y = 1) ∧
      ∀ R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U), ‖R‖ ≤ C₀ →
        let K := localizedResidual hp.le χ₂ χ₃ hU.measurableSet R
        let T := neumannInverse K
        ‖K‖ ≤ θ ∧ HasSum (fun j : ℕ ↦ (-K) ^ j) T ∧
        (1 + K) * T = 1 ∧ T * (1 + K) = 1 ∧ ‖T‖ ≤ (1 - θ)⁻¹ ∧
        ∀ (G : GradedScale (Lp F 2 μ)) (C a : ℕ → ℝ) (b : ℕ),
          (∀ s, 0 ≤ C s) → (∀ s, 0 ≤ a s) → Monotone a →
          G.HasOneGain K C a b →
          ∀ (s : ℕ) (f : Lp F 2 μ), f ∈ G.level s →
            T f ∈ G.level s ∧
            G.gradeNorm s (T f) ≤ inverseTameConstant θ C s *
              (G.gradeNorm s f + (1 + a (s + b)) * ‖f‖) := by
  obtain ⟨χ₂, χ₃, h₂, h₃, hnest, hsmall⟩ :=
    exists_local_cutoffs_norm_lt (F := F) (μ := μ) hp hU hx C₀ hθ₀
  have hplateau : ∀ y ∈ Metric.ball x χ₂.rIn, χ₂ y = 1 :=
    fun _ hy ↦ χ₂.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hcore : Metric.ball x χ₂.rIn ⊆ U := by
    intro y hy
    apply h₂
    apply subset_tsupport (χ₂ : E → ℝ)
    show χ₂ y ≠ 0
    rw [hplateau y hy]
    exact one_ne_zero
  refine ⟨χ₂, χ₃, h₂, h₃, hnest,
    ⟨x, Metric.mem_ball_self χ₂.rIn_pos⟩, Metric.isOpen_ball, hcore, hplateau, ?_⟩
  intro R hR
  let K := localizedResidual hp.le χ₂ χ₃ hU.measurableSet R
  have hKθ : ‖K‖ ≤ θ := (hsmall R hR).le
  have hK : ‖K‖ < 1 := hKθ.trans_lt hθ₁
  refine ⟨hKθ, hasSum_neumannInverse K hK, add_mul_neumannInverse K hK,
    neumannInverse_mul_add K hK, norm_neumannInverse_le K hKθ hθ₁, ?_⟩
  intro G C a b hC ha hmono hgain s f hf
  exact ⟨G.neumannInverse_mem K hK hgain.regularity s hf,
    G.neumannInverse_gradeNorm_le K hKθ hθ₁ hC ha hmono hgain s hf⟩

end JanetCartan.FixedDomainInverse
