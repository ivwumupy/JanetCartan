module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Uniform physical cutoffs for a fixed shoulder width

The proof-mask grades in `app:ch_regular:lem:finite-chain` and
`app:ch_regular:eq:chain-tail` require derivative bounds fixed before the
current compact reachable set. A finite cover of the fixed envelope gives
finitely many subcollections of balls. We prepare a smooth compact cutoff
for each subcollection, then bound all of their derivatives together.

Consumer: the coefficient-uniform finite-depth nested masks in `Uniformity`.
The parent must supply a compact envelope and a positive shoulder width from
the uniform shoulder-propagation construction, and instantiate the compact
sets `bufferedReachableAt` from `Uniformity/Shoulders`. Coordinate transport is
already provided by `Uniformity/CanonicalBounds`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open FiniteChain.Graph

variable {d : ℕ}

/-- For a fixed compact physical envelope and positive width, choose all-order
derivative bounds BEFORE the varying compact set. Every compact subset,
including the empty set, admits a smooth `[0,1]` localizer whose open plateau
contains its closed `δ / 4` shoulder and whose closed support lies in its closed
`δ` shoulder. Neither the cutoffs nor the bounds depend on requested accuracy
(`app:ch_regular:lem:finite-chain`, proof-mask grades for
`app:ch_regular:eq:chain-tail`). -/
theorem exists_uniform_physicalLocalizer_cutoffs
    {B : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hB : IsCompact B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ H : ℕ → ℝ, (∀ k, 0 ≤ H k) ∧
      ∀ K : Set (Euclidean (d + 1) × Euclidean (d + 1)),
        IsCompact K → K ⊆ B →
        ∃ m : LocalizerSymbol (d + 1),
          ContDiff ℝ ∞ m ∧ (∀ p, m p ∈ Icc (0 : ℝ) 1) ∧
          HasCompactSupport m ∧
          cthickening (δ / 4) K ⊆ interior {p | m p = 1} ∧
          tsupport m ⊆ cthickening δ K ∧
          ∀ k p, ‖iteratedFDeriv ℝ k m p‖ ≤ H k := by
  classical
  obtain ⟨C, _, hC, hcover⟩ := hB.finite_cover_balls (by positivity : 0 < δ / 8)
  let : Fintype C := hC.fintype
  -- All subcollections and their cutoffs are fixed before the compact set varies.
  have hcutoff (s : Finset C) :
      ∃ m : LocalizerSymbol (d + 1),
        ContDiff ℝ ∞ m ∧ (∀ p, m p ∈ Icc (0 : ℝ) 1) ∧
        HasCompactSupport m ∧
        tsupport m ⊆ ⋃ c ∈ s, ball (c : Euclidean (d + 1) × Euclidean (d + 1))
          (3 * δ / 4) ∧
        (⋃ c ∈ s, closedBall (c : Euclidean (d + 1) × Euclidean (d + 1)) (δ / 2)) ⊆
          interior {p | m p = 1} := by
    apply CompatibleResponse.exists_compact_family_cutoff
      (s.isCompact_biUnion fun _ _ ↦ isCompact_closedBall _ _)
      (isOpen_biUnion fun _ _ ↦ isOpen_ball)
    exact iUnion₂_mono fun c _ ↦ closedBall_subset_ball (by linarith)
  choose m hsmooth hrange hcompact hsupp hplateau using hcutoff
  choose G hG hbound using fun (s : Finset C) (k : ℕ) ↦
    (hcompact s).exists_bound_iteratedFDeriv (hsmooth s) k
  refine ⟨fun k ↦ ∑ s : Finset C, G s k,
    fun k ↦ Finset.sum_nonneg (fun s _ ↦ hG s k), ?_⟩
  intro K hK hKB
  let s : Finset C := Finset.univ.filter fun c ↦ ∃ x ∈ K,
    dist x (c : Euclidean (d + 1) × Euclidean (d + 1)) < δ / 8
  refine ⟨m s, hsmooth s, hrange s, hcompact s, ?_, ?_, ?_⟩
  · intro p hp
    rw [hK.cthickening_eq_biUnion_closedBall (by positivity)] at hp
    obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.mp hp
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcover (hKB hx))
    have hcs : (⟨c, hc⟩ : C) ∈ s := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hxc⟩
    apply hplateau s
    apply mem_iUnion₂.mpr
    refine ⟨⟨c, hc⟩, hcs, ?_⟩
    change dist p c ≤ δ / 2
    have htri := dist_triangle p x c
    change dist p x ≤ δ / 4 at hpx
    change dist x c < δ / 8 at hxc
    linarith
  · intro p hp
    obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp (hsupp s hp)
    obtain ⟨x, hx, hxc⟩ := (Finset.mem_filter.mp hc).2
    apply closedBall_subset_cthickening hx δ
    change dist p x ≤ δ
    change dist p (c : Euclidean (d + 1) × Euclidean (d + 1)) < 3 * δ / 4 at hpc
    have htri := dist_triangle p (c : Euclidean (d + 1) × Euclidean (d + 1)) x
    rw [dist_comm (c : Euclidean (d + 1) × Euclidean (d + 1)) x] at htri
    linarith
  · intro k p
    exact (hbound s k k le_rfl p).trans
      (Finset.single_le_sum (fun t _ ↦ hG t k) (Finset.mem_univ s))

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
