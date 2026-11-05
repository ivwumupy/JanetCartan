module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.RowBounds.Characteristic

/-!
# Joint tame estimates after the actual inverse-flow pullback

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, retain the
published `physicalRowTransport` and the same two-time inverse chart. The
primitive `C¹` budgets control the low composition, while the existing
additive tame composition theorem controls orders at least two. The reserve
is zero, independently of the order. The regular-sector construction still
has to produce the inverse chart, its image containment, and these primitive
budgets for `W₀ = k a` and `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.CharacteristicTransport.RowBounds

open RegularSector.Characteristic FullPhaseCharts.InverseEstimates

variable {P X ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [Fintype ι]

private theorem exists_row_pullback_bound (x : X) (p : P) {ρ σ Rx R : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hρRx : ρ < Rx) (hσR : σ < R)
    (m : ℕ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℝ × (ℝ × X) → ℝ × (ℝ × P)) (g : ℝ × (ℝ × P) → ι → ℝ),
      ContDiffOn ℝ ∞ f (ball (0, (0, x)) Rx) →
      ContDiffOn ℝ ∞ g (ball (0, (0, p)) R) →
      MapsTo f (closedBall (0, (0, x)) ρ) (closedBall (0, (0, p)) σ) →
      cNorm (closedBall (0, (0, x)) ρ) 1 f ≤ M →
      cNorm (closedBall (0, (0, p)) σ) 1 g ≤ N →
      cNorm (closedBall (0, (0, x)) ρ) m (g ∘ f) ≤
        C * (1 + cNorm (closedBall (0, (0, x)) ρ) m f +
          cNorm (closedBall (0, (0, p)) σ) m g) := by
  by_cases hm : m ≤ 1
  · have hmult : 0 ≤ compositionMultiplicity 1 := by
      unfold compositionMultiplicity
      positivity
    let B := compositionMultiplicity 1 * N * (1 + M)
    have hB : 0 ≤ B := mul_nonneg (mul_nonneg hmult hN) (by linarith)
    refine ⟨1 + B, by positivity, ?_⟩
    intro f g hf hg hmap hfM hgN
    have hfl : ∀ z ∈ closedBall (0, (0, x)) ρ, ContDiffAt ℝ 1 f z :=
      fun z hz ↦ (hf.contDiffAt
        (isOpen_ball.mem_nhds (closedBall_subset_ball hρRx hz))).of_le (by simp)
    have hgl : ∀ z ∈ closedBall (0, (0, p)) σ, ContDiffAt ℝ 1 g z :=
      fun z hz ↦ (hg.contDiffAt
        (isOpen_ball.mem_nhds (closedBall_subset_ball hσR hz))).of_le (by simp)
    have hh := cNorm_comp_le_polynomial hfl (fun z hz ↦ hgl (f z) (hmap hz))
      (fun j hj ↦ bddAbove_norm_iteratedFDeriv_of_contDiffAt
        (isCompact_closedBall _ _) hfl hj) hN
      (fun j hj z hz ↦ (norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (isCompact_closedBall _ _) hgl (hmap hz) hj).trans hgN)
    simp only [pow_one] at hh
    have hl : cNorm (closedBall (0, (0, x)) ρ) m (g ∘ f) ≤ B :=
      (cNorm_mono_order hm).trans (hh.trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hfM) (mul_nonneg hmult hN)))
    have hf0 := cNorm_nonneg (closedBall (0, (0, x)) ρ) m f
    have hg0 := cNorm_nonneg (closedBall (0, (0, p)) σ) m g
    exact hl.trans (by nlinarith [mul_nonneg hB (add_nonneg hf0 hg0)])
  · exact exists_cNorm_comp_le_additive_oneHigh
      (0, (0, x)) (0, (0, p)) hρ hσ isOpen_ball isOpen_ball
      (closedBall_subset_ball hρRx) (closedBall_subset_ball hσR) (by omega) hM hN

omit [FiniteDimensional ℝ X] in
/-- The literal physical row is smooth on an open neighborhood of the entire
working ball, from primitive smoothness and the inverse chart's actual image
containment (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_physicalRowTransport_smooth_near_ball (x : X) (p : P)
    {ρ σ Rx R : ℝ} (hσ : 0 < σ) (hρRx : ρ < Rx) (hσR : σ < R)
    {c : ℝ × (ℝ × P) → ℝ} {r : ℝ × P → ι → ℝ} {Y : ℝ × (ℝ × X) → P}
    (hc : ContDiffOn ℝ ∞ c (ball (0, (0, p)) R))
    (hr : ContDiffOn ℝ ∞ r (ball (0, p) R))
    (hY : ContDiffOn ℝ ∞ Y (ball (0, (0, x)) Rx))
    (hmap : MapsTo (fun q ↦ (q.1, (q.2.1, Y q)))
      (closedBall (0, (0, x)) ρ) (closedBall (0, (0, p)) σ)) :
    ∃ W : Set (ℝ × (ℝ × X)), IsOpen W ∧ closedBall (0, (0, x)) ρ ⊆ W ∧
      ContDiffOn ℝ ∞ (physicalRowTransport c r Y) W := by
  let Z := fun q : ℝ × (ℝ × X) ↦ (q.1, (q.2.1, Y q))
  have hZ : ContDiffOn ℝ ∞ Z (ball (0, (0, x)) Rx) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk hY)
  refine ⟨ball (0, (0, x)) Rx ∩ Z ⁻¹' ball (0, (0, p)) R,
    hZ.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball,
    fun q hq ↦ ⟨closedBall_subset_ball hρRx hq, closedBall_subset_ball hσR (hmap hq)⟩,
    ?_⟩
  exact (contDiffOn_rowTransport_ball p (hσ.trans hσR) hc hr).comp
    (hZ.mono inter_subset_left) (fun _ hz ↦ hz.2)

/-- All joint norms of the published physical signed row have an additive
primitive bound with `μ = 0`. Constants precede `c,r,Y`; only their fixed `C¹`
budgets are assumed. All output-time, source-time, and label derivatives are
included, on fixed positive balls and fixed open enlargements.

The producer is the actual two-time Hamilton/inverse-flow construction of
`jc-regular-sector`. It must establish the displayed image containment,
smoothness and primitive bounds. The consumer is the symbol estimate for
`W₀ = k a`, `W₁`, and `P W₁` in
`app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_physicalRowTransport_cNorm_bounds (x : X) (p : P)
    {ρ σ Rx R : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hρRx : ρ < Rx) (hσR : σ < R)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (c : ℝ × (ℝ × P) → ℝ) (r : ℝ × P → ι → ℝ) (Y : ℝ × (ℝ × X) → P),
      ContDiffOn ℝ ∞ c (ball (0, (0, p)) R) →
      ContDiffOn ℝ ∞ r (ball (0, p) R) →
      ContDiffOn ℝ ∞ Y (ball (0, (0, x)) Rx) →
      MapsTo (fun q ↦ (q.1, (q.2.1, Y q)))
        (closedBall (0, (0, x)) ρ) (closedBall (0, (0, p)) σ) →
      cNorm (closedBall (0, (0, p)) σ) 1 c ≤ M →
      cNorm (closedBall (0, p) σ) 1 r ≤ M →
      cNorm (closedBall (0, (0, x)) ρ) 1 Y ≤ M →
      ∀ m, cNorm (closedBall (0, (0, x)) ρ) m (physicalRowTransport c r Y) ≤
        C m * (1 + cNorm (closedBall (0, (0, p)) σ) m c +
          cNorm (closedBall (0, p) σ) m r + cNorm (closedBall (0, (0, x)) ρ) m Y) := by
  let Kx := closedBall ((0 : ℝ), ((0 : ℝ), x)) ρ
  let K := closedBall ((0 : ℝ), ((0 : ℝ), p)) σ
  let Kr := closedBall ((0 : ℝ), p) σ
  let T := fun j ↦ cNorm Kx j (Prod.fst : ℝ × (ℝ × X) → ℝ) +
    cNorm Kx j (fun q : ℝ × (ℝ × X) ↦ q.2.1)
  have hT j : 0 ≤ T j := add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)
  obtain ⟨A, hA, hrow⟩ := exists_rowTransport_cNorm_bounds (ι := ι) p hσ hσR hM
  choose B hB hcomp using fun j ↦ exists_row_pullback_bound (ι := ι)
    x p hρ hσ hρRx hσR j (add_nonneg (hT 1) hM)
      (mul_nonneg (hA 1).le (by linarith : 0 ≤ 1 + M + M))
  let C := fun j ↦ B j * (1 + T j + A j)
  refine ⟨C, fun j ↦ mul_pos (hB j) (by linarith [hT j, hA j]), ?_⟩
  intro c r Y hc hr hY hmap hcM hrM hYM m
  let Z := fun q : ℝ × (ℝ × X) ↦ (q.1, (q.2.1, Y q))
  have hZ : ContDiffOn ℝ ∞ Z (ball (0, (0, x)) Rx) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk hY)
  have hn j : cNorm Kx j Z ≤ T j + cNorm Kx j Y := by
    have hYj : ∀ q ∈ Kx, ContDiffAt ℝ j Y q := fun q hq ↦
      (hY.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hρRx hq))).of_le (by simp)
    have hinner := cNorm_prodMk_le_on Kx (isCompact_closedBall _ _) j
      (fun _ _ ↦ contDiffAt_snd.fst) hYj
    have houter := cNorm_prodMk_le_on Kx (isCompact_closedBall _ _) j
      (fun _ _ ↦ contDiffAt_fst) (fun q hq ↦ contDiffAt_snd.fst.prodMk (hYj q hq))
    exact houter.trans (by dsimp [T]; linarith)
  have hrowhigh j := hrow c r hc hr hcM hrM j
  have hrowlow : cNorm K 1 (rowTransport c r) ≤ A 1 * (1 + M + M) :=
    (hrowhigh 1).trans (mul_le_mul_of_nonneg_left (by linarith) (hA 1).le)
  have hh := hcomp m Z (rowTransport c r) hZ
    (contDiffOn_rowTransport_ball p (hσ.trans hσR) hc hr) hmap
    ((hn 1).trans (add_le_add le_rfl hYM)) hrowlow
  change cNorm Kx m (physicalRowTransport c r Y) ≤ _ at hh
  apply hh.trans
  have hb : 1 + cNorm Kx m Z + cNorm K m (rowTransport c r) ≤
      (1 + T m + A m) * (1 + cNorm K m c + cNorm Kr m r + cNorm Kx m Y) := by
    have hc0 := cNorm_nonneg K m c
    have hr0 := cNorm_nonneg Kr m r
    have hy0 := cNorm_nonneg Kx m Y
    nlinarith [hn m, hrowhigh m, hT m, hA m,
      mul_nonneg (hT m) hc0, mul_nonneg (hT m) hr0, mul_nonneg (hT m) hy0,
      mul_nonneg (hA m).le hy0]
  exact (mul_le_mul_of_nonneg_left hb (hB m).le).trans_eq (by dsimp [C]; ring)

end JanetCartan.CharacteristicTransport.RowBounds
