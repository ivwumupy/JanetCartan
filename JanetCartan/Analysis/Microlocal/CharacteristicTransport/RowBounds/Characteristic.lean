module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.RowBounds.Integral

/-!
# Tame estimates for the literal signed characteristic row

The datum in `app:ch_regular_base:lem:characteristic-kernel` is a finite real
row of arbitrary sign. Its lift by the label projection and the actual
exponential are combined with the existing tame bilinear estimate. Orders
zero and one use only the fixed low budgets. Thus the reserve is zero at
every order, on the same balls, and no derivative of the row is assumed.
The concrete consumer is `W₀ = k a` and its differentiated complete residual
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.CharacteristicTransport.RowBounds

open RegularSector.Characteristic NullTransport.AmplitudeTame
  FullPhaseCharts.InverseEstimates

variable {P ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [Fintype ι]

private theorem exists_signed_product_bound (p : P) {σ R : ℝ}
    (hσ : 0 < σ) (hσR : σ < R) (m : ℕ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ × (ℝ × P) → ℝ) (g : ℝ × (ℝ × P) → ι → ℝ),
      ContDiffOn ℝ ∞ f (ball (0, (0, p)) R) →
      ContDiffOn ℝ ∞ g (ball (0, (0, p)) R) →
      cNorm (closedBall (0, (0, p)) σ) 1 f ≤ M →
      cNorm (closedBall (0, (0, p)) σ) 1 g ≤ N →
      cNorm (closedBall (0, (0, p)) σ) m (fun q ↦ f q • g q) ≤
        C * (1 + cNorm (closedBall (0, (0, p)) σ) m f +
          cNorm (closedBall (0, (0, p)) σ) m g) := by
  let B : ℝ →L[ℝ] (ι → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
  by_cases hm : m ≤ 1
  · let A : ℝ := ∑ j ∈ Finset.range (1 + 1), ‖B‖ *
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hAMN : 0 ≤ A * M * N := mul_nonneg (mul_nonneg hA hM) hN
    refine ⟨1 + A * M * N, by positivity, ?_⟩
    intro f g hf hg hfM hgN
    have hb := cNorm_bilinear_le_on B (isCompact_closedBall (0, (0, p)) σ)
      isOpen_ball (closedBall_subset_ball hσR) hf hg 1
    have hl : cNorm (closedBall (0, (0, p)) σ) m (fun q ↦ f q • g q) ≤ A * M * N := by
      apply (cNorm_mono_order hm).trans (hb.trans ?_)
      change A * cNorm (closedBall (0, (0, p)) σ) 1 f *
        cNorm (closedBall (0, (0, p)) σ) 1 g ≤ _
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfM hA) hgN
        (cNorm_nonneg _ _ _) (mul_nonneg hA hM)
    have hf0 := cNorm_nonneg (closedBall (0, (0, p)) σ) m f
    have hg0 := cNorm_nonneg (closedBall (0, (0, p)) σ) m g
    exact hl.trans (by nlinarith [mul_nonneg hAMN (add_nonneg hf0 hg0)])
  · exact exists_cNorm_bilinear_le_additive_oneHigh B (0, (0, p)) hσ
      isOpen_ball (closedBall_subset_ball hσR) (by omega) hM hN

/-- Smoothness of the published signed row on the buffered joint ball.
No positivity assumption on the datum is used
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_rowTransport_ball (p : P) {R : ℝ} (hR : 0 < R)
    {c : ℝ × (ℝ × P) → ℝ} {r : ℝ × P → ι → ℝ}
    (hc : ContDiffOn ℝ ∞ c (ball (0, (0, p)) R))
    (hr : ContDiffOn ℝ ∞ r (ball (0, p) R)) :
    ContDiffOn ℝ ∞ (rowTransport c r) (ball (0, (0, p)) R) := by
  have hf : ContDiffOn ℝ ∞
      (fun q : ℝ × (ℝ × P) ↦ transportFactor (fun u ↦ c (u, q.2)) q.2.1 q.1)
      (ball (0, (0, p)) R) := (contDiffOn_rowIntegral hR hc).neg.exp
  apply hf.smul (hr.comp contDiffOn_snd ?_)
  intro q hq
  rw [← ball_prod_same] at hq
  exact hq.2

/-- All joint characteristic-coordinate norms of the *published* signed row
are additive in the primitive high norms, with reserve `μ = 0`. The entire
positive constant sequence is chosen before `c,r`; the only low inputs are
their `C¹` norms. All balls and the open enlargement are fixed independently
of the differentiating order. This is the row estimate needed for `W₀ = k a`
in `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`.

The regular-sector construction must supply its actual potential and signed
datum on these domains; this conditional estimate does not construct them. -/
theorem exists_rowTransport_cNorm_bounds (p : P) {σ R : ℝ}
    (hσ : 0 < σ) (hσR : σ < R) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (c : ℝ × (ℝ × P) → ℝ) (r : ℝ × P → ι → ℝ),
      ContDiffOn ℝ ∞ c (ball (0, (0, p)) R) →
      ContDiffOn ℝ ∞ r (ball (0, p) R) →
      cNorm (closedBall (0, (0, p)) σ) 1 c ≤ M →
      cNorm (closedBall (0, p) σ) 1 r ≤ M →
      ∀ m, cNorm (closedBall (0, (0, p)) σ) m (rowTransport c r) ≤
        C m * (1 + cNorm (closedBall (0, (0, p)) σ) m c +
          cNorm (closedBall (0, p) σ) m r) := by
  let L := ContinuousLinearMap.snd ℝ ℝ (ℝ × P)
  let D := fun j ↦ linearNormCost L j
  have hD j : 0 < D j := linearNormCost_pos _ _
  choose A hA hfactor using fun j ↦ exists_cNorm_rowFactor_le p hσ j M
  choose B hB hprod using fun j ↦ exists_signed_product_bound (ι := ι) p hσ hσR j
    (mul_nonneg (hA 1).le (by linarith : 0 ≤ 1 + M)) (mul_nonneg (hD 1).le hM)
  let C := fun j ↦ B j * (1 + A j + D j)
  refine ⟨C, fun j ↦ mul_pos (hB j) (by linarith [hA j, hD j]), ?_⟩
  intro c r hc hr hcM hrM m
  let K := closedBall ((0 : ℝ), ((0 : ℝ), p)) σ
  let Kr := closedBall ((0 : ℝ), p) σ
  let f := fun q : ℝ × (ℝ × P) ↦ transportFactor (fun u ↦ c (u, q.2)) q.2.1 q.1
  let g := r ∘ L
  have hf : ContDiffOn ℝ ∞ f (ball (0, (0, p)) R) :=
    (contDiffOn_rowIntegral (hσ.trans hσR) hc).neg.exp
  have hg : ContDiffOn ℝ ∞ g (ball (0, (0, p)) R) :=
    hr.comp L.contDiff.contDiffOn (by
      intro q hq
      rw [← ball_prod_same] at hq
      exact hq.2)
  have hn j : cNorm K j g ≤ D j * cNorm Kr j r :=
    cNorm_comp_linear_le L (isCompact_closedBall (0, p) σ) isOpen_ball
      (closedBall_subset_ball hσR) hr (by
        intro q hq
        dsimp [K] at hq
        rw [← closedBall_prod_same] at hq
        exact hq.2) j
  have hfn j : cNorm K j f ≤ A j * (1 + cNorm K j c) :=
    hfactor j R hσR c hc ((cNorm_mono_order (by omega : 0 ≤ 1)).trans hcM)
  have hfl : cNorm K 1 f ≤ A 1 * (1 + M) :=
    (hfn 1).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hcM) (hA 1).le)
  have hgl : cNorm K 1 g ≤ D 1 * M :=
    (hn 1).trans (mul_le_mul_of_nonneg_left hrM (hD 1).le)
  have hh := hprod m f g hf hg hfl hgl
  change cNorm K m (rowTransport c r) ≤ _ at hh
  apply hh.trans
  have hb : 1 + cNorm K m f + cNorm K m g ≤
      (1 + A m + D m) * (1 + cNorm K m c + cNorm Kr m r) := by
    have hc0 := cNorm_nonneg K m c
    have hr0 := cNorm_nonneg Kr m r
    nlinarith [hfn m, hn m, hA m, hD m,
      mul_nonneg (hA m).le hr0, mul_nonneg (hD m).le hc0]
  exact (mul_le_mul_of_nonneg_left hb (hB m).le).trans_eq (by dsimp [C]; ring)

end JanetCartan.CharacteristicTransport.RowBounds
