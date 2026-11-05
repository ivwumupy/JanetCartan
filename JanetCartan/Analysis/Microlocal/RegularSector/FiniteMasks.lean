module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.ZeroExclusion

/-!
# Fixed finite masks and the elliptic complement

Construct the finite smooth masks used to sum the local parametrices in
`app:ch_regular_base:thm:sector` of `paper.tex` and in the finite-cover paragraph
of `paper-v2.tex`, `app:ch_regular:sec:preliminaries`. The masks are chosen from
the fixed open charts before the current coefficients. Their sum is one on a
neighborhood of the protected compact set, and their closed supports stay
inside the selected charts. For a cover of the frozen characteristic set,
the complete complementary mask has a uniform elliptic gap, including its
shoulders, for every sufficiently close current scalar symbol.

The actual chart constructors still supply the open cover. These results
construct masks and a gap, not local parametrices or operator estimates.
-/

@[expose] public noncomputable section

open Set Function Filter
open scoped Topology ContDiff Manifold

namespace JanetCartan.RegularSector.FiniteMasks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*}

/-- Construct a fixed finite smooth partition near a compact set with compact
closed supports in the original open charts. The sum is at most one globally,
so its literal complement remains nonnegative. Consumer: the finite source
partition in `app:ch_regular_base:thm:sector`. -/
theorem exists_finite_patch_masks {K : Set E} (hK : IsCompact K)
    (O : ι → Set E) (hO : ∀ i, IsOpen (O i)) (hcover : K ⊆ ⋃ i, O i) :
    ∃ (s : Finset ι) (χ : s → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i x, χ i x ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ O i) ∧
      (∀ x, ∑ i, χ i x ≤ 1) ∧
      K ⊆ interior {x | ∑ i, χ i x = 1} := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hO hcover
  let U : Set E := ⋃ i : s, O i
  have hU : IsOpen U := isOpen_iUnion fun i ↦ hO i
  have hKU : K ⊆ U := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨W, hW, hKW, hWU, hcW⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V, hV, hKV, hVW, hcV⟩ :=
    exists_open_between_and_isCompact_closure hK hW hKW
  have hsub : closure V ⊆ ⋃ i : s, O i ∩ W := by
    intro x hx
    have hxW := hVW hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hWU (subset_closure hxW))
    exact mem_iUnion.mpr ⟨i, hi, hxW⟩
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) isClosed_closure (fun i : s ↦ O i ∩ W)
    (fun i ↦ (hO i).inter hW) hsub
  refine ⟨s, fun i ↦ χ i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact contMDiff_iff_contDiff.mp (χ i).contMDiff
  · exact fun i x ↦ ⟨χ.nonneg i x, χ.le_one i x⟩
  · intro i
    exact hcW.of_isClosed_subset (isClosed_tsupport _)
      (fun x hx ↦ subset_closure (hχ i hx).2)
  · exact fun i x hx ↦ (hχ i hx).1
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using χ.sum_le_one x
  · exact hKV.trans (interior_maximal (fun x hx ↦ by
      simpa only [mem_ofPred_eq, finsum_eq_sum_of_fintype] using
        χ.sum_eq_one (subset_closure hx)) hV)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The closed support of the complementary mask misses every partition
plateau, including all cutoff shoulders (`app:ch_regular_base:prop:complete-residual`). -/
theorem complement_tsupport_disjoint_plateau {κ : Type*} [Fintype κ]
    (χ : κ → E → ℝ) :
    Disjoint (interior {x | ∑ i, χ i x = 1})
      (tsupport (fun x ↦ 1 - ∑ i, χ i x)) := by
  apply disjoint_left.mpr
  intro x hx
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact sub_eq_zero.mpr (interior_subset hy).symm

/-- Construct characteristic-patch masks before the varying scalar symbol.
The entire complementary closed support in the fixed compact set is uniformly
elliptic. In particular every nearby characteristic point lies in the same
partition plateau; it need not be a frozen characteristic point.
Consumer: the elliptic summand of `app:ch_regular_base:thm:sector`. -/
theorem exists_finite_characteristic_masks {K : Set E} {f : E → ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (O : ι → Set E) (hO : ∀ i, IsOpen (O i))
    (hcover : ∀ x ∈ K, f x = 0 → ∃ i, x ∈ O i) :
    ∃ (s : Finset ι) (χ : s → E → ℝ) (δ : ℝ), 0 < δ ∧
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i x, χ i x ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ O i) ∧
      (∀ x, ∑ i, χ i x ≤ 1) ∧
      (∀ g : E → ℝ, (∀ x ∈ K, |g x - f x| < δ) →
        (∀ x ∈ K ∩ tsupport (fun x ↦ 1 - ∑ i, χ i x), δ ≤ |g x|) ∧
        (∀ x ∈ K, g x = 0 → x ∈ interior {y | ∑ i, χ i y = 1})) := by
  have hZ : IsCompact {x ∈ K | f x = 0} := by
    obtain ⟨F, hF, he⟩ := continuousOn_iff_isClosed.mp hf {0} isClosed_singleton
    have he' : {x ∈ K | f x = 0} = f ⁻¹' {0} ∩ K := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, and_comm]
    rw [he', he]
    exact hK.inter_left hF
  obtain ⟨s, χ, hsmooth, hrange, hcompact, hsupport, hsum, hplateau⟩ :=
    exists_finite_patch_masks hZ O hO (by
      intro x hx
      obtain ⟨i, hi⟩ := hcover x hx.1 hx.2
      exact mem_iUnion.mpr ⟨i, hi⟩)
  obtain ⟨δ, hδ, hgap⟩ := ProtectedFlow.PhaseCover.exists_positive_frozen_gap
    hK isOpen_interior hf (fun x hx hz ↦ hplateau ⟨hx, hz⟩)
  refine ⟨s, χ, δ / 2, by positivity, hsmooth, hrange, hcompact, hsupport, hsum, ?_⟩
  intro g hg
  have hcurrent : ∀ x ∈ K \ interior {y | ∑ i, χ i y = 1}, δ / 2 ≤ |g x| := by
    intro x hx
    have htri : |f x| ≤ |g x - f x| + |g x| := by
      calc
        |f x| = |-(g x - f x) + g x| := by congr 1; ring
        _ ≤ |-(g x - f x)| + |g x| := abs_add_le _ _
        _ = |g x - f x| + |g x| := by rw [abs_neg]
    have := hgap x hx
    have := hg x hx.1
    linarith
  constructor
  · intro x hx
    exact hcurrent x ⟨hx.1, fun hp ↦
      disjoint_left.mp (complement_tsupport_disjoint_plateau χ) hp hx.2⟩
  · intro x hx hz
    by_contra hp
    have := hcurrent x ⟨hx, hp⟩
    rw [hz, abs_zero] at this
    linarith

end JanetCartan.RegularSector.FiniteMasks
