module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.ZeroSelection
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.FiveSelection
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Nodes

/-!
# Nonexceptional detecting pair selection

Step 1 of `app:ch_seed:prop:seed-frozen-menu`, with the exact dimension
hypothesis and only the five-dimensional node lines excluded.
-/

@[expose] public noncomputable section
namespace JanetCartan.CubeCarrier

/-- Every direction in dimension at least six admits detecting pairs for each
nonzero kernel stress (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_ge_six {n : ℕ} (hn : 6 ≤ n)
    {k s : Euclidean n} (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  by_cases hk : ∀ i, k i ≠ 0
  · exact exists_pairCriterion_of_nonzero_ge_six hn hk hs hker
  · push Not at hk
    exact exists_pairCriterion_of_zero_coordinate (by omega) hs hker hk

/-- The full nonexceptional pair-selection assertion in Step 1 of
`app:ch_seed:prop:seed-frozen-menu`. Only node lines in dimension five are
excluded; their carriers are constructed separately in Step 2. -/
theorem exists_pairCriterion_of_nonexceptional {n : ℕ} (hn : 5 ≤ n)
    {k s : Euclidean n} (hk : k ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hnode : n = 5 → ¬ ∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, k = t • cubeVector a b) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  by_cases hn5 : n = 5
  · subst n
    by_cases hkcoord : ∀ i, k i ≠ 0
    · apply exists_pairCriterion_of_nonzero_five hkcoord hs hker
      intro hq
      apply hnode rfl
      apply (cube_quadratic_zero_iff_node (by decide) hk).mp
      intro i
      exact congrArg (fun v : Euclidean 5 ↦ v i) hq
    · push Not at hkcoord
      exact exists_pairCriterion_of_zero_coordinate (by decide) hs hker hkcoord
  · exact exists_pairCriterion_ge_six (by omega) hs hker

end JanetCartan.CubeCarrier
