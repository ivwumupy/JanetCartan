module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Shoulders

/-!
# Finite-depth propagation of comparison-graph errors

The metric induction used by the protected finite-chain paragraph of
`app:ch_regular:lem:finite-chain`. Until the first characteristic step a point
stays close to the original source. Thereafter its error from one fixed scaled
comparison graph satisfies a scalar recurrence. This includes every diagonal
step and the last closed shoulder. The actual transport producer is
`GraphTransport.Construction`; source coverage and its fixed neighborhood are
instantiated by the physical propagation assembly.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open ProtectedFlow

variable {d : ℕ}

/-- Error amplification through finitely many closed shoulders. The two
constants are the actual transport loss and the spatial graph Lipschitz cost
(`app:ch_regular:lem:finite-chain`). -/
def bufferedGraphError (L K : ℝ) : ℕ → ℝ
  | 0 => K
  | n + 1 => L * bufferedGraphError L K n + K

/-- The error budget is nonnegative (`app:ch_regular:lem:finite-chain`). -/
theorem bufferedGraphError_nonneg {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (n : ℕ) :
    0 ≤ bufferedGraphError L K n := by
  induction n with
  | zero => exact hK
  | succ n ih => exact add_nonneg (mul_nonneg hL ih) hK

/-- A fixed final depth controls all earlier error budgets
(`app:ch_regular:lem:finite-chain`). -/
theorem bufferedGraphError_mono {L K : ℝ} (hL : 1 ≤ L) (hK : 0 ≤ K) :
    Monotone (bufferedGraphError L K) := by
  apply monotone_nat_of_le_succ
  intro n
  have hn := bufferedGraphError_nonneg (zero_le_one.trans hL) hK n
  dsimp only [bufferedGraphError]
  nlinarith

/-- A fixed compact physical envelope also controls the bases of closed
shoulders. This allows the induction to use the retained comparison ball
with its original physical buffer (`app:ch_regular:lem:finite-chain`). -/
theorem bufferedReachableAt_fst_subset
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    (hR : IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | R pq.1 pq.2})
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    {B : Set (Euclidean (d + 1))} (hSB : ∀ p ∈ S, p.1 ∈ B)
    (hRB : ∀ p q, R p q → q.1 ∈ B) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ n, ∀ p ∈ cthickening δ (bufferedReachableAt R S δ n),
      p.1 ∈ cthickening (((n : ℝ) + 1) * δ) B := by
  have step (n : ℕ)
      (hn : ∀ p ∈ bufferedReachableAt R S δ n,
        p.1 ∈ cthickening ((n : ℝ) * δ) B) :
      ∀ p ∈ cthickening δ (bufferedReachableAt R S δ n),
        p.1 ∈ cthickening (((n : ℝ) + 1) * δ) B := by
    intro p hp
    rw [(isCompact_bufferedReachableAt hR hS δ n).cthickening_eq_biUnion_closedBall hδ] at hp
    obtain ⟨q, hq, hqp⟩ := mem_iUnion₂.mp hp
    have hd : dist p.1 q.1 ≤ δ := (le_max_left _ _).trans hqp
    have hp' := mem_cthickening_of_dist_le _ _ _ _ (hn q hq) hd
    have := cthickening_cthickening_subset hδ (mul_nonneg (Nat.cast_nonneg n) hδ) B hp'
    have heq : δ + (n : ℝ) * δ = ((n : ℝ) + 1) * δ := by ring
    exact heq ▸ this
  have reach : ∀ n, ∀ p ∈ bufferedReachableAt R S δ n,
      p.1 ∈ cthickening ((n : ℝ) * δ) B := by
    intro n
    induction n with
    | zero => exact fun p hp ↦ self_subset_cthickening _ (hSB p hp)
    | succ n ih =>
      rintro q ⟨p, hp, hc⟩
      cases hc with
      | tail hs hc =>
        cases hc
        rcases hs with rfl | hs
        · simpa only [Nat.cast_add, Nat.cast_one] using step n ih p hp
        · exact self_subset_cthickening _ (hRB _ _ hs)
  exact fun n ↦ step n (reach n)

/-- Moving both physical variables by at most `δ` increases the scaled graph
defect by at most `(1 + β * Lx) * δ`. This is the closed-shoulder cost in
`app:ch_regular:lem:finite-chain`. -/
theorem scaled_graph_defect_dist_le {P : Type*}
    (g : P → Euclidean (d + 1) → Euclidean (d + 1))
    {B : Set (Euclidean (d + 1))} {Lx β scale δ : ℝ}
    (hLx : 0 ≤ Lx) (hs : 0 ≤ scale) (hsβ : scale ≤ β)
    (hgraph : ∀ η x, x ∈ B → ∀ y ∈ B, ‖g η x - g η y‖ ≤ Lx * dist x y)
    (η : P) {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hp : p.1 ∈ B) (hq : q.1 ∈ B) (hd : dist q p ≤ δ) :
    ‖q.2 - scale • g η q.1‖ ≤
      ‖p.2 - scale • g η p.1‖ + (1 + β * Lx) * δ := by
  have hx : dist q.1 p.1 ≤ δ := (le_max_left _ _).trans hd
  have hξ : ‖q.2 - p.2‖ ≤ δ := by
    rw [← dist_eq_norm]
    exact (le_max_right _ _).trans hd
  have hg : ‖scale • (g η q.1 - g η p.1)‖ ≤ β * Lx * δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    calc
      scale * ‖g η q.1 - g η p.1‖ ≤ scale * (Lx * dist q.1 p.1) :=
        mul_le_mul_of_nonneg_left (hgraph η _ hq _ hp) hs
      _ ≤ β * (Lx * δ) := mul_le_mul hsβ
        (mul_le_mul_of_nonneg_left hx hLx) (mul_nonneg hLx (dist_nonneg))
        (hs.trans hsβ)
      _ = β * Lx * δ := by ring
  calc
    ‖q.2 - scale • g η q.1‖ =
        ‖(q.2 - p.2) + (p.2 - scale • g η p.1) -
          scale • (g η q.1 - g η p.1)‖ := by congr 1; module
    _ ≤ ‖q.2 - p.2‖ + ‖p.2 - scale • g η p.1‖ +
        ‖scale • (g η q.1 - g η p.1)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖p.2 - scale • g η p.1‖ + (1 + β * Lx) * δ := by linarith

/-- Every closed shoulder is either close to an as yet unpropagated source
or close to one fixed scaled comparison graph. The source-cover premise is
needed only at the first actual relation step; elliptic and diagonal branches
are retained. `Propagation` supplies its neighborhood before the coefficient
field, and supplies `htransport` from the actual root/phase producers. This
deduction alone does not assert existence of those inputs
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:thm:no-return`). -/
theorem bufferedReachableAt_graph_error {P : Type*}
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    (hR : IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | R pq.1 pq.2})
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    (g : P → Euclidean (d + 1) → Euclidean (d + 1))
    {B : Set (Euclidean (d + 1))} {α β L Lx δ : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hL : 1 ≤ L) (hLx : 0 ≤ Lx) (hδ : 0 ≤ δ)
    (N : ℕ)
    (hbase : ∀ n ≤ N, ∀ p ∈ cthickening δ (bufferedReachableAt R S δ n), p.1 ∈ B)
    (hgraph : ∀ η x, x ∈ B → ∀ y ∈ B, ‖g η x - g η y‖ ≤ Lx * dist x y)
    (hstart : ∀ p ∈ cthickening (((N : ℝ) + 1) * δ) S, ∀ q, R p q →
      ∃ η scale, scale ∈ Icc α β ∧ p.2 = scale • g η p.1)
    (htransport : ∀ η scale, scale ∈ Icc α β → ∀ p q, R p q →
      ‖q.2 - scale • g η q.1‖ ≤ L * ‖p.2 - scale • g η p.1‖) :
    ∀ n ≤ N, ∀ q ∈ cthickening δ (bufferedReachableAt R S δ n),
      q ∈ cthickening (((n : ℝ) + 1) * δ) S ∨
        ∃ η scale, scale ∈ Icc α β ∧
          ‖q.2 - scale • g η q.1‖ ≤ bufferedGraphError L (1 + β * Lx) n * δ := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hβ : 0 ≤ β := hα.le.trans hαβ
  have hK : 0 ≤ 1 + β * Lx := by positivity
  intro n
  induction n with
  | zero =>
    intro _ q hq
    exact Or.inl (by simpa only [Nat.cast_zero, zero_add, one_mul, bufferedReachableAt] using hq)
  | succ n ih =>
    intro hn q hq
    have hnN : n ≤ N := (Nat.le_succ n).trans hn
    rw [(isCompact_bufferedReachableAt hR hS δ (n + 1)).cthickening_eq_biUnion_closedBall hδ]
      at hq
    obtain ⟨v, hv, hvq⟩ := mem_iUnion₂.mp hq
    have hv' : v ∈ cthickening δ (bufferedReachableAt R S δ (n + 1)) :=
      self_subset_cthickening _ hv
    have hq' : q ∈ cthickening δ (bufferedReachableAt R S δ (n + 1)) :=
      mem_cthickening_of_dist_le _ _ _ _ hv hvq
    obtain ⟨u, hu, hstep⟩ := hv
    have huv : u = v ∨ R u v := by
      cases hstep with
      | tail hs hc => cases hc; exact hs
    have active (η : P) (scale : ℝ) (hs : scale ∈ Icc α β)
        (he : ‖v.2 - scale • g η v.1‖ ≤
          L * bufferedGraphError L (1 + β * Lx) n * δ) :
        ∃ η scale, scale ∈ Icc α β ∧
          ‖q.2 - scale • g η q.1‖ ≤
            bufferedGraphError L (1 + β * Lx) (n + 1) * δ := by
      refine ⟨η, scale, hs, ?_⟩
      have hd := scaled_graph_defect_dist_le g hLx (hα.le.trans hs.1) hs.2
        hgraph η (hbase _ hn v hv') (hbase _ hn q hq') hvq
      dsimp only [bufferedGraphError]
      nlinarith only [hd, he]
    rcases ih hnN u hu with hsource | ⟨η, scale, hs, he⟩
    · rcases huv with rfl | huv
      · left
        have hqS : q ∈ cthickening δ
            (cthickening (((n : ℝ) + 1) * δ) S) :=
          mem_cthickening_of_dist_le _ _ _ _ hsource hvq
        have := cthickening_cthickening_subset hδ
          (mul_nonneg (by positivity) hδ) S hqS
        have heq : δ + ((n : ℝ) + 1) * δ = ((↑(n + 1) : ℝ) + 1) * δ := by
          push_cast
          ring
        exact heq ▸ this
      · right
        have huS : u ∈ cthickening (((N : ℝ) + 1) * δ) S :=
          cthickening_mono (mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.add_le_add_right hnN 1) hδ) S hsource
        obtain ⟨η, scale, hs, heq⟩ := hstart u huS v huv
        apply active η scale hs
        have he := htransport η scale hs u v huv
        rw [heq, sub_self, norm_zero, mul_zero] at he
        exact he.trans (mul_nonneg
          (mul_nonneg hL0 (bufferedGraphError_nonneg hL0 hK n)) hδ)
    · right
      apply active η scale hs
      rcases huv with rfl | huv
      · have hnonneg := bufferedGraphError_nonneg hL0 hK n
        have := mul_le_mul_of_nonneg_right hL (mul_nonneg hnonneg hδ)
        nlinarith only [he, this]
      · exact (htransport η scale hs u v huv).trans
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hL0)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
