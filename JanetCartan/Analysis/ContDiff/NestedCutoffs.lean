module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

import Mathlib.Tactic.Linarith

/-!
# One smooth cutoff family for nested balls

The geometric cutoff construction in `app:setup:domains`,
`app:eq:global-domain-chain`, and `app:eq:global-cutoff-plateaus` of paper.tex.
For each gap between positive radii we put the plateau and support radii at
one third and two thirds of the gap. Thus the closed inner ball lies in the
interior of the plateau, and the closed support is compact inside the outer ball.

`nestedBallCutoffs` works for any finite strictly increasing list of positive
radii. `LocalDomain.cutoffRadii` supplies such a list between the existing core
and chart radii. The cutoffs do not depend on a derivative order; their common
finite-order bounds follow from the existing compact-set derivative seminorms.

These results construct the ball cutoffs once their geometric validity domains
are available. They do not assert the existence of the response operators or
their identity cores in the rest of Setup `app:setup:domains`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan

/-- `app:eq:global-cutoff-plateaus`: a bump with positive buffers on both sides
of its transition region. -/
def bufferedBallBump {n : ℕ} (c : Euclidean n) (r R : ℝ)
    (hr : 0 < r) (h : r < R) : ContDiffBump c where
  rIn := (2 * r + R) / 3
  rOut := (r + 2 * R) / 3
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- `app:eq:global-cutoff-plateaus`: the previous closed ball is inside the
interior of the region where the cutoff is one. -/
theorem bufferedBallBump_plateau {n : ℕ} (c : Euclidean n) (r R : ℝ)
    (hr : 0 < r) (h : r < R) :
    closedBall c r ⊆ interior {x | bufferedBallBump c r R hr h x = 1} := by
  apply subset_interior_iff.mpr
  refine ⟨ball c ((2 * r + R) / 3), isOpen_ball,
    closedBall_subset_ball (by linarith), ?_⟩
  intro x hx
  exact (bufferedBallBump c r R hr h).one_of_mem_closedBall (ball_subset_closedBall hx)

/-- `app:eq:global-domain-chain`: even the closed support is inside the next
open ball, with a positive radial buffer. -/
theorem bufferedBallBump_tsupport_subset {n : ℕ} (c : Euclidean n) (r R : ℝ)
    (hr : 0 < r) (h : r < R) :
    tsupport (bufferedBallBump c r R hr h) ⊆ ball c R := by
  rw [(bufferedBallBump c r R hr h).tsupport_eq]
  apply closedBall_subset_ball
  change (r + 2 * R) / 3 < R
  linarith

/-- `app:setup:domains`: one family of bumps for a finite chain of concentric
balls. No derivative order enters this definition. -/
def nestedBallCutoffs {m n : ℕ} (ρ : Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 < ρ i) (hmono : StrictMono ρ) (i : Fin m) :
    Euclidean n → ℝ :=
  bufferedBallBump 0 (ρ i.castSucc) (ρ i.succ) (hpos _) (hmono Fin.castSucc_lt_succ)

/-- `app:setup:domains`: every cutoff in the common family is smooth. -/
theorem nestedBallCutoffs_contDiff {m n : ℕ} (ρ : Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 < ρ i) (hmono : StrictMono ρ) (i : Fin m) :
    ContDiff ℝ ∞ (nestedBallCutoffs (n := n) ρ hpos hmono i) :=
  (bufferedBallBump (0 : Euclidean n) (ρ i.castSucc) (ρ i.succ)
    (hpos _) (hmono Fin.castSucc_lt_succ)).contDiff

/-- `app:setup:domains`: all cutoff values belong to `[0,1]`. -/
theorem nestedBallCutoffs_mem_Icc {m n : ℕ} (ρ : Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 < ρ i) (hmono : StrictMono ρ) (i : Fin m) (x : Euclidean n) :
    nestedBallCutoffs ρ hpos hmono i x ∈ Icc (0 : ℝ) 1 :=
  ⟨(bufferedBallBump 0 (ρ i.castSucc) (ρ i.succ)
    (hpos _) (hmono Fin.castSucc_lt_succ)).nonneg,
    (bufferedBallBump 0 (ρ i.castSucc) (ρ i.succ)
    (hpos _) (hmono Fin.castSucc_lt_succ)).le_one⟩

/-- `app:eq:global-domain-chain`: every cutoff has compact closed support. -/
theorem nestedBallCutoffs_hasCompactSupport {m n : ℕ} (ρ : Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 < ρ i) (hmono : StrictMono ρ) (i : Fin m) :
    HasCompactSupport (nestedBallCutoffs (n := n) ρ hpos hmono i) :=
  (bufferedBallBump (0 : Euclidean n) (ρ i.castSucc) (ρ i.succ)
    (hpos _) (hmono Fin.castSucc_lt_succ)).hasCompactSupport

/-- `app:eq:global-domain-chain`: the support is compactly contained in the
next open ball, using `hasCompactSupport` together with this inclusion. -/
theorem nestedBallCutoffs_tsupport_subset {m n : ℕ} (ρ : Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 < ρ i) (hmono : StrictMono ρ) (i : Fin m) :
    tsupport (nestedBallCutoffs (n := n) ρ hpos hmono i) ⊆ ball 0 (ρ i.succ) :=
  bufferedBallBump_tsupport_subset 0 _ _ (hpos _) (hmono Fin.castSucc_lt_succ)

/-- `app:eq:global-cutoff-plateaus`: each previous closed ball has a
neighborhood on which its cutoff is one. -/
theorem nestedBallCutoffs_plateau {m n : ℕ} (ρ : Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 < ρ i) (hmono : StrictMono ρ) (i : Fin m) :
    closedBall (0 : Euclidean n) (ρ i.castSucc) ⊆
      interior {x | nestedBallCutoffs ρ hpos hmono i x = 1} :=
  bufferedBallBump_plateau 0 _ _ (hpos _) (hmono Fin.castSucc_lt_succ)

/-- `app:eq:global-cutoff-plateaus`: the closed support of any earlier cutoff
lies inside the open plateau of any later cutoff. -/
theorem nestedBallCutoffs_tsupport_subset_plateau {m n : ℕ} (ρ : Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 < ρ i) (hmono : StrictMono ρ) {i j : Fin m} (hij : i < j) :
    tsupport (nestedBallCutoffs (n := n) ρ hpos hmono i) ⊆
      interior {x | nestedBallCutoffs ρ hpos hmono j x = 1} := by
  have hle : i.succ ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_of_lt hij
  exact (nestedBallCutoffs_tsupport_subset ρ hpos hmono i).trans
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall (hmono.monotone hle))).trans
      (nestedBallCutoffs_plateau ρ hpos hmono j))

/-- `app:setup:domains`: at every finite order the same finite family has a
common derivative bound on any compact measurement set. -/
theorem nestedBallCutoffs_derivative_bounds {m n : ℕ} (ρ : Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 < ρ i) (hmono : StrictMono ρ)
    {s : Set (Euclidean n)} (hs : IsCompact s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : Fin m, ∀ j ≤ k, ∀ x ∈ s,
      ‖iteratedFDeriv ℝ j (nestedBallCutoffs ρ hpos hmono i) x‖ ≤ C := by
  refine ⟨∑ i, cNorm s k (nestedBallCutoffs ρ hpos hmono i),
    Finset.sum_nonneg (fun i _ ↦ cNorm_nonneg _ _ _), ?_⟩
  intro i j hj x hx
  apply (norm_iteratedFDeriv_le_cNorm hs
    ((nestedBallCutoffs_contDiff ρ hpos hmono i).of_le (by simp)) hx hj).trans
  exact Finset.single_le_sum (fun i _ ↦ cNorm_nonneg s k
    (nestedBallCutoffs ρ hpos hmono i)) (Finset.mem_univ i)

namespace LocalDomain

/-- `app:eq:global-domain-chain`: an arbitrary finite subdivision of the
buffer between the existing closed core and open chart. -/
def cutoffRadii (D : LocalDomain) (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  D.coreRadius + (i.val : ℝ) * ((D.chartRadius - D.coreRadius) / (m + 1))

/-- `app:eq:global-domain-chain`: the subdivision starts at the core radius. -/
@[simp] theorem cutoffRadii_zero (D : LocalDomain) (m : ℕ) :
    D.cutoffRadii m 0 = D.coreRadius := by
  simp [cutoffRadii]

/-- `app:eq:global-domain-chain`: the subdivision ends at the chart radius. -/
@[simp] theorem cutoffRadii_last (D : LocalDomain) (m : ℕ) :
    D.cutoffRadii m (Fin.last (m + 1)) = D.chartRadius := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  simp only [cutoffRadii, Fin.val_last, Nat.cast_add, Nat.cast_one]
  rw [mul_div_cancel₀ _ hm]
  ring

/-- `app:eq:global-domain-chain`: each subdivision gap is positive. -/
theorem cutoffRadii_strictMono (D : LocalDomain) (m : ℕ) :
    StrictMono (D.cutoffRadii m) := by
  intro i j hij
  dsimp only [cutoffRadii]
  apply add_lt_add_right
  apply mul_lt_mul_of_pos_right
  · exact_mod_cast hij
  · exact div_pos (sub_pos.mpr D.coreRadius_lt_chartRadius) (by positivity)

/-- `app:setup:domains`: every subdivision radius is positive. -/
theorem cutoffRadii_pos (D : LocalDomain) (m : ℕ) (i : Fin (m + 2)) :
    0 < D.cutoffRadii m i := by
  have h := (D.cutoffRadii_strictMono m).monotone (Fin.zero_le i)
  rw [D.cutoffRadii_zero] at h
  exact D.coreRadius_pos.trans_le h

/-- `app:setup:domains`: the common smooth cutoff family inside a `LocalDomain`. -/
def cutoffs (D : LocalDomain) (n m : ℕ) : Fin (m + 1) → Euclidean n → ℝ :=
  nestedBallCutoffs (D.cutoffRadii m) (D.cutoffRadii_pos m) (D.cutoffRadii_strictMono m)

/-- `app:eq:global-domain-chain`: the closed intermediate balls are compact
and lie strictly inside the next open ball. -/
theorem cutoffRadii_compactly_nested (D : LocalDomain) (n m : ℕ) (i : Fin (m + 1)) :
    IsCompact (closedBall (0 : Euclidean n) (D.cutoffRadii m i.castSucc)) ∧
      closedBall (0 : Euclidean n) (D.cutoffRadii m i.castSucc) ⊆
        ball 0 (D.cutoffRadii m i.succ) :=
  ⟨isCompact_closedBall _ _,
    closedBall_subset_ball (D.cutoffRadii_strictMono m Fin.castSucc_lt_succ)⟩

/-- `app:eq:global-cutoff-plateaus`: every member of the constructed family is
smooth, takes values in `[0,1]`, has compact support inside the next domain,
and equals one on a neighborhood of the previous closed ball. -/
theorem cutoffs_spec (D : LocalDomain) (n m : ℕ) (i : Fin (m + 1)) :
    ContDiff ℝ ∞ (D.cutoffs n m i) ∧
    (∀ x, D.cutoffs n m i x ∈ Icc (0 : ℝ) 1) ∧
    HasCompactSupport (D.cutoffs n m i) ∧
    tsupport (D.cutoffs n m i) ⊆ ball 0 (D.cutoffRadii m i.succ) ∧
    closedBall 0 (D.cutoffRadii m i.castSucc) ⊆
      interior {x | D.cutoffs n m i x = 1} :=
  ⟨nestedBallCutoffs_contDiff _ _ _ i, nestedBallCutoffs_mem_Icc _ _ _ i,
    nestedBallCutoffs_hasCompactSupport _ _ _ i,
    nestedBallCutoffs_tsupport_subset _ _ _ i, nestedBallCutoffs_plateau _ _ _ i⟩

/-- `app:eq:global-cutoff-plateaus`: all closed supports stay inside the
existing chart, and all plateaus contain a neighborhood of its closed core. -/
theorem cutoffs_core_chart (D : LocalDomain) (n m : ℕ) (i : Fin (m + 1)) :
    tsupport (D.cutoffs n m i) ⊆ D.chart n ∧
      D.core n ⊆ interior {x | D.cutoffs n m i x = 1} := by
  have hupper := (D.cutoffRadii_strictMono m).monotone (Fin.le_last i.succ)
  rw [D.cutoffRadii_last] at hupper
  have hlower := (D.cutoffRadii_strictMono m).monotone (Fin.zero_le i.castSucc)
  rw [D.cutoffRadii_zero] at hlower
  exact ⟨(D.cutoffs_spec n m i).2.2.2.1.trans (ball_subset_ball hupper),
    (closedBall_subset_closedBall hlower).trans (D.cutoffs_spec n m i).2.2.2.2⟩

/-- `app:eq:global-cutoff-plateaus`: each later cutoff is one on an open
neighborhood of every earlier cutoff's closed support. -/
theorem cutoffs_tsupport_subset_plateau (D : LocalDomain) (n m : ℕ)
    {i j : Fin (m + 1)} (hij : i < j) :
    tsupport (D.cutoffs n m i) ⊆ interior {x | D.cutoffs n m j x = 1} :=
  nestedBallCutoffs_tsupport_subset_plateau _ _ _ hij

/-- `app:setup:domains`: all finite derivative orders are bounded for the
single chosen cutoff family on each compact set. -/
theorem cutoffs_derivative_bounds (D : LocalDomain) (n m : ℕ)
    {s : Set (Euclidean n)} (hs : IsCompact s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : Fin (m + 1), ∀ j ≤ k, ∀ x ∈ s,
      ‖iteratedFDeriv ℝ j (D.cutoffs n m i) x‖ ≤ C :=
  nestedBallCutoffs_derivative_bounds _ _ _ hs k

end LocalDomain

end JanetCartan
