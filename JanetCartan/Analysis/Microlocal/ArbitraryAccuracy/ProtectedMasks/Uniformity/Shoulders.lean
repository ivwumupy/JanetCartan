module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Nesting

/-!
# Enlarged reachable sets for uniform nested masks

The sets below are explicit recursive images of closed shoulders. They are
not records assuming a successful mask construction. The remaining uniform
propagation deduction must keep their final closed thickening in the protected
physical region, with a positive width chosen before the current field.

Consumer: the finite-depth mask assembly for `app:ch_regular:lem:finite-chain`.
Smooth cutoff construction from a given width is independent of this uniform
propagation obligation.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open ProtectedFlow

variable {d : ℕ}

/-- At each step enlarge the entire previous image by the same closed
shoulder, then take one actual relation or full diagonal step. The original
elapsed interval is part of `R` and does not change with depth
(`app:ch_regular:lem:finite-chain`). -/
def bufferedReachableAt
    (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) (δ : ℝ) :
    ℕ → Set (Euclidean (d + 1) × Euclidean (d + 1))
  | 0 => S
  | n + 1 => reachableAt R (cthickening δ (bufferedReachableAt R S δ n)) 1

/-- The complete image of a closed shoulder belongs to the next explicit
buffered reachable set (`app:ch_regular:lem:finite-chain`). -/
theorem mem_bufferedReachableAt_succ_of_step
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} {δ : ℝ} {n : ℕ}
    {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hp : p ∈ cthickening δ (bufferedReachableAt R S δ n)) (hpq : p = q ∨ R p q) :
    q ∈ bufferedReachableAt R S δ (n + 1) :=
  ⟨p, hp, .tail hpq (.refl q)⟩

/-- Diagonal branches make the enlarged reachable sets increasing with
depth (`app:ch_regular:lem:finite-chain`). -/
theorem bufferedReachableAt_mono_depth
    (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) (δ : ℝ) :
    Monotone (bufferedReachableAt R S δ) := by
  apply monotone_nat_of_le_succ
  intro n p hp
  exact mem_bufferedReachableAt_succ_of_step
    (self_subset_cthickening (δ := δ) _ hp) (Or.inl rfl)

/-- Each explicit enlarged image is compact for a compact actual relation.
`isCompact_physicalDirectRelation` produces the graph input from the original
root/flow buffers; no coefficient-class compactness is used
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_bufferedReachableAt
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    (hR : IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | R pq.1 pq.2})
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    (δ : ℝ) (n : ℕ) : IsCompact (bufferedReachableAt R S δ n) := by
  induction n with
  | zero => exact hS
  | succ n ih => exact isCompact_reachableAt_of_compact_relation hR ih.cthickening 1

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
