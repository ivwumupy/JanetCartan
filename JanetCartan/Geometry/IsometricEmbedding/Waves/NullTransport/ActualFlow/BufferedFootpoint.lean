module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.Reversal

/-!
# An explicit buffered inverse chart from backwards characteristics

The open flow tube in `app:ch_waves:thm:leading` contains a fixed product
box. Every inverse identity follows from the ODE; no inverse or successful
transport is assumed. `exists_actual_buffered_flow_chart` supplies the
constructed flow for the literal null direction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff NNReal Topology
namespace JanetCartan.NullTransport.ActualFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restrict the autonomous flow to the adapted zero section
(`app:ch_waves:thm:leading`). -/
def forwardFromLift (Ψ : (ℝ × E) × ℝ → ℝ × E) (q : ℝ × E) : E :=
  (Ψ ((0, q.2), q.1)).2

/-- Evolve backwards by the adapted time to recover the initial label
(`app:ch_waves:thm:leading`). -/
def footpointFromLift (Ψ : (ℝ × E) × ℝ → ℝ × E) (q : ℝ × E) : E :=
  (Ψ (q, -q.1)).2

/-- Construct both sides of the inverse chart on explicit buffers using
only the low field bounds. The time radius is `R / (16 * (M + 1))`;
the initial, containing, and covered label radii are `R/8`, `R/4`, and
`R/32`. The consumer `exists_actual_buffered_flow_chart` discharges all
flow hypotheses by Picard construction (`app:ch_waves:thm:leading`). -/
theorem buffered_footpoint_chart
    {V : ℝ × E → ℝ × E} {Ψ : (ℝ × E) × ℝ → ℝ × E}
    {p₀ : E} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hunit : ∀ q, (V q).1 = 1)
    (hlip : LipschitzOnWith ⟨M, hM⟩ V (closedBall (0, p₀) R))
    (hv : ∀ q ∈ closedBall (0, p₀) R, ‖V q‖ ≤ M)
    (hΨ : ContDiffOn ℝ ∞ Ψ
      (ball (0, p₀) (R / 2) ×ˢ Ioo (-existenceTime R M) (existenceTime R M)))
    (hi : ∀ q ∈ closedBall (0, p₀) (R / 2), Ψ (q, 0) = q)
    (hd : ∀ q ∈ closedBall (0, p₀) (R / 2),
      ∀ t ∈ Ioo (-existenceTime R M) (existenceTime R M),
      HasDerivAt (fun s ↦ Ψ (q, s)) (V (Ψ (q, t))) t)
    (hr : ∀ q ∈ closedBall (0, p₀) (R / 2),
      ∀ t ∈ Ioo (-existenceTime R M) (existenceTime R M),
      Ψ (q, t) ∈ closedBall (0, p₀) R) :
    let τ := existenceTime R M / 4
    let I := Ioo (-τ) τ
    let Φ := forwardFromLift Ψ
    let Y := footpointFromLift Ψ
    ∃ D : Set (ℝ × E), IsOpen D ∧
      I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
      D = (fun q ↦ (q.1, Φ q)) '' (I ×ˢ ball p₀ (R / 8)) ∧
      ContDiffOn ℝ ∞ Φ (I ×ˢ ball p₀ (R / 8)) ∧
      ContDiffOn ℝ ∞ Y (I ×ˢ ball p₀ (R / 4)) ∧
      MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ ball p₀ (R / 8)) D ∧
      MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ ball p₀ (R / 8)) ∧
      (∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p) ∧
      (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
      (∀ q ∈ D, Φ (q.1, Y q) = q.2) := by
  let ε := existenceTime R M
  let τ := ε / 4
  let I := Ioo (-τ) τ
  let B := I ×ˢ ball p₀ (R / 4)
  let Φ := forwardFromLift Ψ
  let Y := footpointFromLift Ψ
  have hε : 0 < ε := existenceTime_pos hR hM
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hb := existenceTime_le hR hM
  have hτR : τ ≤ R / 16 := by dsimp [τ, ε]; linarith [hb.1]
  have hMτ : M * τ ≤ R / 16 := by dsimp [τ, ε]; nlinarith [hb.2]
  have ht {t : ℝ} (ht : t ∈ I) : t ∈ Ioo (-ε) ε := by
    change -τ < t ∧ t < τ at ht
    constructor <;> dsimp [τ] at * <;> linarith [ht.1, ht.2]
  have htHalf {t : ℝ} (ht : t ∈ I) : t ∈ Ioo (-ε / 2) (ε / 2) := by
    change -τ < t ∧ t < τ at ht
    constructor <;> dsimp [τ] at * <;> linarith [ht.1, ht.2]
  have htneg {t : ℝ} (ht : t ∈ I) : -t ∈ I := by
    change -τ < -t ∧ -t < τ
    constructor <;> linarith [ht.1, ht.2]
  have htAbs {t : ℝ} (ht : t ∈ I) : |t| < τ := abs_lt.mpr ht
  have hsection {p : E} (hp : p ∈ ball p₀ (R / 8)) :
      ((0 : ℝ), p) ∈ ball (0, p₀) (R / 2) := by
    simpa using (ball_subset_ball (by linarith : R / 8 ≤ R / 2) hp)
  have hB {q : ℝ × E} (hq : q ∈ B) : q ∈ ball (0, p₀) (R / 2) := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa only [Real.dist_eq, sub_zero] using
      (htAbs hq.1).trans_le (by linarith : τ ≤ R / 2),
      (mem_ball.mp hq.2).trans (by linarith)⟩
  have htime (q) (hq : q ∈ closedBall (0, p₀) (R / 2)) (t) (ht : t ∈ Ioo (-ε) ε) :
      (Ψ (q, t)).1 = t + q.1 := by
    have hdt (s) (hs : s ∈ Ioo (-ε) ε) :
        HasDerivAt (fun s ↦ (Ψ (q, s)).1) 1 s := by
      have h : HasDerivAt (fun s ↦ (Ψ (q, s)).1) (V (Ψ (q, s))).1 s :=
        (hd q hq s hs).fst
      rwa [hunit] at h
    exact isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (fun s hs ↦ (hdt s hs).differentiableAt.differentiableWithinAt)
      (differentiable_id.add_const _).differentiableOn
      (fun s hs ↦ by rw [(hdt s hs).deriv, ((hasDerivAt_id s).add_const _).deriv])
      (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨neg_neg_of_pos hε, hε⟩)
      (by rw [hi q hq]; simp) ht
  have hdis (q) (hq : q ∈ closedBall (0, p₀) (R / 2)) (t) (htI : t ∈ I) :
      dist (Ψ (q, t)) q ≤ R / 16 := by
    exact (flow_displacement_le hε hv hi hd hr hq (ht htI)).trans
      ((mul_le_mul_of_nonneg_left (htAbs htI).le hM).trans hMτ)
  have hforward (p) (hp : p ∈ ball p₀ (R / 8)) (t) (htI : t ∈ I) :
      Ψ ((0, p), t) = (t, Φ (t, p)) := by
    exact Prod.ext (by simpa using htime (0, p) (ball_subset_closedBall (hsection hp)) t (ht htI)) rfl
  have hbackward (q) (hq : q ∈ B) : Ψ (q, -q.1) = (0, Y q) := by
    refine Prod.ext ?_ ?_
    · simpa using htime q (ball_subset_closedBall (hB hq)) (-q.1) (ht (htneg hq.1))
    · rfl
  have hfB (p) (hp : p ∈ ball p₀ (R / 8)) (t) (htI : t ∈ I) : (t, Φ (t, p)) ∈ B := by
    refine ⟨htI, ?_⟩
    have hdist := hdis (0, p) (ball_subset_closedBall (hsection hp)) t htI
    rw [hforward p hp t htI, Prod.dist_eq] at hdist
    have hp' := mem_ball.mp hp
    have htri := dist_triangle (Φ (t, p)) p p₀
    exact show dist (Φ (t, p)) p₀ < R / 4 by
      have := le_max_right (dist t 0) (dist (Φ (t, p)) p)
      linarith
  have hYΦ (p) (hp : p ∈ ball p₀ (R / 8)) (t) (htI : t ∈ I) :
      Y (t, Φ (t, p)) = p := by
    have hf := hfB p hp t htI
    have heq := reverse_flow_eq hε hlip hi hd hr
      (ball_subset_closedBall (hsection hp)) (htHalf htI)
      (show Ψ ((0, p), t) ∈ closedBall (0, p₀) (R / 2) by
        rw [hforward p hp t htI]; exact ball_subset_closedBall (hB hf))
    rw [hforward p hp t htI] at heq
    exact congrArg Prod.snd heq
  have hY : ContDiffOn ℝ ∞ Y B :=
    hΨ.snd.comp (contDiffOn_id.prodMk contDiffOn_fst.neg)
      (fun q hq ↦ ⟨hB hq, ht (htneg hq.1)⟩)
  let D := B ∩ Y ⁻¹' ball p₀ (R / 8)
  have hΦY (q) (hq : q ∈ D) : Φ (q.1, Y q) = q.2 := by
    have heq := reverse_flow_eq hε hlip hi hd hr
      (ball_subset_closedBall (hB hq.1)) (htHalf (htneg hq.1.1))
      (show Ψ (q, -q.1) ∈ closedBall (0, p₀) (R / 2) by
        rw [hbackward q hq.1]; exact ball_subset_closedBall (hsection hq.2))
    rw [hbackward q hq.1, neg_neg] at heq
    exact congrArg Prod.snd heq
  have hmap : MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ ball p₀ (R / 8)) D := by
    rintro ⟨t, p⟩ ⟨htI, hp⟩
    exact ⟨hfB p hp t htI, by change Y (t, Φ (t, p)) ∈ ball p₀ (R / 8); rw [hYΦ p hp t htI]; exact hp⟩
  refine ⟨D, hY.continuousOn.isOpen_inter_preimage (isOpen_Ioo.prod isOpen_ball) isOpen_ball,
    ?_, inter_subset_left, ?_, ?_, hY, hmap,
    (fun q hq ↦ ⟨hq.1.1, hq.2⟩), ?_, hYΦ, hΦY⟩
  · rintro ⟨t, p⟩ ⟨htI, hp⟩
    have hq : (t, p) ∈ B := ⟨htI, ball_subset_ball (by linarith) hp⟩
    refine ⟨hq, ?_⟩
    have hh := hdis (t, p) (ball_subset_closedBall (hB hq)) (-t) (htneg htI)
    rw [hbackward (t, p) hq, Prod.dist_eq] at hh
    have htri := dist_triangle (Y (t, p)) p p₀
    have := le_max_right (dist (0 : ℝ) t) (dist (Y (t, p)) p)
    have hp' := mem_ball.mp hp
    exact show dist (Y (t, p)) p₀ < R / 8 by linarith
  · apply Subset.antisymm
    · intro q hq
      exact ⟨(q.1, Y q), ⟨hq.1.1, hq.2⟩, Prod.ext rfl (hΦY q hq)⟩
    · exact image_subset_iff.mpr hmap
  · exact hΨ.snd.comp ((contDiffOn_const.prodMk contDiffOn_snd).prodMk contDiffOn_fst)
      (fun q hq ↦ ⟨hsection hq.2, ht hq.1⟩)
  · intro p hp
    exact congrArg Prod.snd (hi (0, p) (ball_subset_closedBall (hsection hp)))
end JanetCartan.NullTransport.ActualFlow
