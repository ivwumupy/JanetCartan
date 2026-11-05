module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Family

/-! # Exhaustion of sampled quadratic terms

The case split in `app:rem:exhaustive-signed-pairs`. Injectivity of the full
group/parameter sample identifier is precisely what excludes a distinct-index
zero beat within one group; distinct groups need no parameter separation.
-/

@[expose] public noncomputable section

namespace JanetCartan.SignedPairs

variable {ι Z J E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : ι → Set Z}

/-- Every sampled plus term, including a doubled phase, is represented among
the protected pairs (`app:rem:exhaustive-signed-pairs`). -/
theorem sample_plus_represented (group : J → ι) (z : J → Z)
    (hz : ∀ j, z j ∈ S (group j)) (j k : J) :
    ∃ q : Pair ι Z S, ∀ f : ι → Z → E,
      q.vector f = f (group j) (z j) + f (group k) (z k) := by
  by_cases h : group j = group k
  · refine ⟨.sum (group j) ⟨z j, hz j⟩ ⟨z k, ?_⟩, ?_⟩
    · simpa only [h] using hz k
    · intro f
      simp only [Pair.vector, h]
  · refine ⟨.cross (group j) (group k) h ⟨z j, hz j⟩ ⟨z k, hz k⟩
      1 1 (by norm_num) (by norm_num), ?_⟩
    intro f
    simp only [Pair.vector, one_smul]

/-- Every distinct-index sampled minus term is protected. The injective
full sample identifier rules out literal copies in a common group; repeated
indices are intentionally outside the statement
(`app:rem:exhaustive-signed-pairs`). -/
theorem sample_minus_represented (group : J → ι) (z : J → Z)
    (hz : ∀ j, z j ∈ S (group j))
    (hinj : Function.Injective (fun j ↦ (group j, z j)))
    {j k : J} (hjk : j ≠ k) :
    ∃ q : Pair ι Z S, ∀ f : ι → Z → E,
      q.vector f = f (group j) (z j) - f (group k) (z k) := by
  by_cases h : group j = group k
  · have hzk : z k ∈ S (group j) := by simpa only [h] using hz k
    have hne : (⟨z j, hz j⟩ : S (group j)) ≠ ⟨z k, hzk⟩ := by
      intro he
      exact hjk (hinj (Prod.ext h (congrArg Subtype.val he)))
    refine ⟨.difference (group j) ⟨z j, hz j⟩ ⟨z k, hzk⟩ hne, ?_⟩
    intro f
    simp only [Pair.vector, h]
  · refine ⟨.cross (group j) (group k) h ⟨z j, hz j⟩ ⟨z k, hz k⟩
      1 (-1) (by norm_num) (by norm_num), ?_⟩
    intro f
    simp only [Pair.vector, one_smul, neg_smul, sub_eq_add_neg]

end JanetCartan.SignedPairs
