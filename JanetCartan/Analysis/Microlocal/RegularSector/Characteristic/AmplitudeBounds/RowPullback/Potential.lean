module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.RowPullback.Coordinates

/-!
# Pulling the physical potential onto the characteristic

The coefficient in the literal row is `c ∘ C`, not `c`. For
`app:ch_regular_base:lem:characteristic-kernel`, this module derives its
single-high bound from the physical potential and the autonomous flow.
The consuming row estimate has the same fixed reserve two.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds.RowPullback

open NullTransport.AmplitudeTame

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Single-high bound for the actual characteristic coefficient, with one
fixed reserve and constants preceding all functions and charts. The physical
potential's bounds are produced by the physical calculus applied to the
transported primitives; the parent must instantiate those inputs
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_chartPotential_cNorm_bounds (t₀ : ℝ) (p x : E × E)
    {σ τ R S : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hσR : σ < R) (hτS : τ < S)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
      ∀ (c : TwoTimePoint E → ℝ) (Φ : RootState E × ℝ → RootState E)
        (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)),
      (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ →
      ContDiffOn ℝ ∞ c (ball (t₀, (t₀, x)) S) →
      ContDiffOn ℝ ∞ Φ (ball ((t₀, p), 0) (2 * R)) →
      MapsTo C (closedBall (t₀, (t₀, p)) σ) (closedBall (t₀, (t₀, x)) τ) →
      cNorm (closedBall (t₀, (t₀, x)) τ) 1 c ≤ M →
      cNorm (closedBall ((t₀, p), 0) (2 * σ)) 1 Φ ≤ M →
      ∀ m, cNorm (closedBall (t₀, (t₀, p)) σ) m (c ∘ C) ≤
        D m * (1 + cNorm (closedBall (t₀, (t₀, x)) τ) (m + 2) c +
          cNorm (closedBall ((t₀, p), 0) (2 * σ)) (m + 2) Φ) := by
  let K := closedBall (t₀, (t₀, p)) σ
  let T := fun m ↦ cNorm K m (projectionBaseLinear (E := E))
  let L := fun m ↦ ‖projectionFlowLinear (E := E)‖ *
    linearNormCost (elapsedInputLinear (E := E)) m
  have hT m : 0 ≤ T m := cNorm_nonneg _ _ _
  have hL m : 0 ≤ L m := mul_nonneg (norm_nonneg _) (linearNormCost_pos _ _).le
  choose A hA hb using fun m ↦ exists_cNorm_comp_le_uniform_local
    (G := ℝ) (t₀, (t₀, p)) (t₀, (t₀, x)) hσ hτ m
    (add_nonneg (hT 1) (mul_nonneg (hL 1) hM)) hM
  refine ⟨fun m ↦ A m * (1 + T (m + 2) + L (m + 2)),
    fun m ↦ mul_pos (hA m) (by linarith [hT (m + 2), hL (m + 2)]), ?_⟩
  intro c Φ C hC hc hΦ hmap hcl hΦl m
  have hCf : ContDiffOn ℝ ∞ (C : TwoTimePoint E → TwoTimePoint E)
      (ball (t₀, (t₀, p)) R) := by
    rw [hC]
    exact contDiffOn_twoTimeProjection_ball t₀ p (hσ.trans hσR) hΦ
  have hn j : cNorm K j (C : TwoTimePoint E → TwoTimePoint E) ≤
      T j + L j * cNorm (closedBall ((t₀, p), 0) (2 * σ)) j Φ := by
    rw [hC]
    exact cNorm_twoTimeProjection_le t₀ p hσ hσR hΦ j
  have hCl : cNorm K 1 (C : TwoTimePoint E → TwoTimePoint E) ≤ T 1 + L 1 * M :=
    (hn 1).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hΦl (hL 1)))
  have hh := hb m _ _ isOpen_ball isOpen_ball (closedBall_subset_ball hσR)
    (closedBall_subset_ball hτS) C c hCf hc hmap hCl hcl
  apply hh.trans
  have hcp := cNorm_nonneg (closedBall (t₀, (t₀, x)) τ) (m + 2) c
  have hφp := cNorm_nonneg (closedBall ((t₀, p), 0) (2 * σ)) (m + 2) Φ
  have hs : 1 + cNorm K (m + 2) (C : TwoTimePoint E → TwoTimePoint E) +
      cNorm (closedBall (t₀, (t₀, x)) τ) (m + 2) c ≤
      (1 + T (m + 2) + L (m + 2)) *
        (1 + cNorm (closedBall (t₀, (t₀, x)) τ) (m + 2) c +
          cNorm (closedBall ((t₀, p), 0) (2 * σ)) (m + 2) Φ) := by
    nlinarith [hn (m + 2), hT (m + 2), hL (m + 2),
      mul_nonneg (hT (m + 2)) hcp, mul_nonneg (hT (m + 2)) hφp,
      mul_nonneg (hL (m + 2)) hcp]
  exact (mul_le_mul_of_nonneg_left hs (hA m).le).trans_eq (by ring)

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds.RowPullback
