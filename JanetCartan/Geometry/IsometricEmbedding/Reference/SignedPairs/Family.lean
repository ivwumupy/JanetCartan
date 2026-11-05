module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Compact

/-! # Exhaustive signed pairs on parameter cubes

The labels are full group identifiers from `app:rem:exhaustive-signed-pairs`.
The functions supplied below already include their fixed positive radial labels.
No identification of equal carrier specifications or equal covectors is made.
-/

@[expose] public noncomputable section

namespace JanetCartan.SignedPairs

/-- All protected terms of `app:rem:exhaustive-signed-pairs`. The repeated-index
minus term is explicitly excluded. The plus term permits equal parameters;
cross-group pairs permit equal parameters and both independent signs. -/
inductive Pair (ι Z : Type*) (S : ι → Set Z) where
  | difference (i : ι) (z w : S i) (hne : z ≠ w)
  | sum (i : ι) (z w : S i)
  | cross (i j : ι) (hne : i ≠ j) (z : S i) (w : S j)
      (s t : ℝ) (hs : |s| = 1) (ht : |t| = 1)

variable {ι Z E X : Type*} {S : ι → Set Z}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact covector of a signed term in `app:rem:exhaustive-signed-pairs`.
Here `f i` includes the fixed radial label of group `i`. -/
def Pair.vector (f : ι → Z → E) : Pair ι Z S → E
  | .difference i z w _ => f i z - f i w
  | .sum i z w => f i z + f i w
  | .cross i j _ z w s t _ _ => s • f i z + t • f j w

/-- The true beat divided by the global frequency in
`app:rem:exhaustive-signed-pairs`; radial labels stay in the fixed constants. -/
def Pair.beat : Pair ι Z S → ℝ
  | .difference _ z w _ => ‖(z : Z) - (w : Z)‖
  | .sum .. => 1
  | .cross .. => 1

omit [NormedSpace ℝ Z] in
/-- Every protected term has strictly positive beat; there is no diagonal
zero difference (`app:rem:exhaustive-signed-pairs`). -/
theorem Pair.beat_pos (q : Pair ι Z S) : 0 < q.beat := by
  cases q with
  | difference i z w hne =>
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h ↦ hne (Subtype.ext h)))
  | sum => exact zero_lt_one
  | cross => exact zero_lt_one

/-- Uniform `C¹` errors give an error proportional to the true beat for every
protected signed term (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem Pair.vector_error (hS : ∀ i, Convex ℝ (S i))
    {f g : ι → Z → E} {f' g' : ι → Z → Z →L[ℝ] E} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf : ∀ i z, z ∈ S i → HasFDerivWithinAt (f i) (f' i z) (S i) z)
    (hg : ∀ i z, z ∈ S i → HasFDerivWithinAt (g i) (g' i z) (S i) z)
    (he : ∀ i z, z ∈ S i → ‖g' i z - f' i z‖ ≤ ε)
    (hv : ∀ i z, z ∈ S i → ‖g i z - f i z‖ ≤ ε)
    (q : Pair ι Z S) : ‖q.vector g - q.vector f‖ ≤ (2 * ε) * q.beat := by
  cases q with
  | difference i z w hne =>
    have h := chord_error_of_derivative_error (hS i) (hf i) (hg i) (he i)
      z.property w.property
    change ‖(g i z - g i w) - (f i z - f i w)‖ ≤ (2 * ε) * ‖(z : Z) - w‖
    nlinarith [norm_nonneg ((z : Z) - w)]
  | sum i z w =>
    simpa only [Pair.vector, Pair.beat, mul_one] using sum_error
      (hv i z z.property) (hv i w w.property)
  | cross i j hne z w s t hs ht =>
    simpa only [Pair.vector, Pair.beat, mul_one, one_smul, one_add_one_eq_two] using
      radial_signed_error (r := 1) (R := 1) zero_le_one zero_le_one hs ht
        (hv i z z.property) (hv j w w.property)

/-- All normalized actual signed directions, before taking limiting chords
(`app:ch_seed:prop:seed-actual-menu`, Step 2). The physical index type can
include both physical points and the entire permitted family of immersions. -/
def directionSet (g : X → ι → Z → E) (S : ι → Set Z) : Set E :=
  {v | ∃ x q, v = NormedSpace.normalize ((q : Pair ι Z S).vector (g x))}

/-- The complete stability argument with quantitative *frozen* pair geometry
as input (`app:ch_seed:prop:seed-actual-menu`, Step 2). The only actual-field
inputs are within-derivatives and uniform value/derivative errors. Both signs
and all arbitrarily short chords have one common compact angular set.

The norm comparisons retain `q.beat`, hence the frequency is `lam * ‖z-w‖`
for differences and `lam` for sums and cross-group pairs. -/
theorem signed_family_stability {n : ℕ} (hn : 5 ≤ n)
    (hS : ∀ i, Convex ℝ (S i))
    {f : ι → Z → Euclidean n} {g : X → ι → Z → Euclidean n}
    {f' : ι → Z → Z →L[ℝ] Euclidean n}
    {g' : X → ι → Z → Z →L[ℝ] Euclidean n} {c C ε : ℝ}
    (hε : 0 ≤ ε) (hc : 2 * ε < c) (hC : 0 < C)
    (hf : ∀ i z, z ∈ S i → HasFDerivWithinAt (f i) (f' i z) (S i) z)
    (hg : ∀ x i z, z ∈ S i → HasFDerivWithinAt (g x i) (g' x i z) (S i) z)
    (he : ∀ x i z, z ∈ S i → ‖g' x i z - f' i z‖ ≤ ε)
    (hv : ∀ x i z, z ∈ S i → ‖g x i z - f i z‖ ≤ ε)
    (hl : ∀ q : Pair ι Z S, ∀ L ∈ cubeBadSubspaces n,
      c * q.beat ≤ ‖projectAway L (q.vector f)‖)
    (hu : ∀ q : Pair ι Z S, ‖q.vector f‖ ≤ C * q.beat) :
    let γ := (c - 2 * ε) / (C + 2 * ε)
    0 < γ ∧ IsCompact (angularSet n γ) ∧
      (∀ v ∈ angularSet n γ, -v ∈ angularSet n γ) ∧
      closure (directionSet g S) ⊆ angularSet n γ ∧
      (∀ v ∈ angularSet n γ, ∀ w ∈ cubeBadSubspaceUnion n, γ ≤ dist v w) ∧
      (∀ x (q : Pair ι Z S),
        (∀ L ∈ cubeBadSubspaces n,
          (c - 2 * ε) * q.beat ≤ ‖projectAway L (q.vector (g x))‖) ∧
        q.vector (g x) ≠ 0 ∧
        ∀ lam : ℝ, 0 ≤ lam →
          (c - 2 * ε) * (lam * q.beat) ≤ ‖lam • q.vector (g x)‖ ∧
          ‖lam • q.vector (g x)‖ ≤ (C + 2 * ε) * (lam * q.beat)) := by
  dsimp only
  have hcp : 0 < c - 2 * ε := by linarith
  have hCp : 0 < C + 2 * ε := by linarith
  have hγ : 0 < (c - 2 * ε) / (C + 2 * ε) := div_pos hcp hCp
  have hb (x : X) (q : Pair ι Z S) (L : Submodule ℝ (Euclidean n))
      (hL : L ∈ cubeBadSubspaces n) :
      (c - 2 * ε) * q.beat ≤ ‖projectAway L (q.vector (g x))‖ ∧
        ‖q.vector (g x)‖ ≤ (C + 2 * ε) * q.beat :=
    projected_pair_perturbation (projectAway L) (norm_projectAway_le L)
      (hl q L hL) (hu q) (q.vector_error hS hε hf (hg x) (he x) (hv x))
  obtain ⟨L₀, hL₀, _⟩ := Set.mem_iUnion₂.mp (zero_mem_cubeBadSubspaceUnion hn)
  have hdir (x : X) (q : Pair ι Z S) :
      NormedSpace.normalize (q.vector (g x)) ∈ angularSet n ((c - 2 * ε) / (C + 2 * ε)) := by
    have hnz := (normalized_projection_lower (projectAway L₀) (norm_projectAway_le L₀)
      hcp hCp q.beat_pos (hb x q L₀ hL₀).1 (hb x q L₀ hL₀).2).1
    refine ⟨NormedSpace.norm_normalize hnz, ?_⟩
    intro L hL
    exact (normalized_projection_lower (projectAway L) (norm_projectAway_le L)
      hcp hCp q.beat_pos (hb x q L hL).1 (hb x q L hL).2).2
  refine ⟨hγ, isCompact_angularSet _ _, fun _ hv ↦ neg_mem_angularSet hv,
    closure_subset_angularSet ?_, fun _ hv _ hw ↦ angularSet_distance_gap hv hw, ?_⟩
  · rintro v ⟨x, q, rfl⟩
    exact hdir x q
  · intro x q
    have hb₀ := hb x q L₀ hL₀
    have hlo := hb₀.1.trans (norm_projectAway_le L₀ _)
    refine ⟨fun L hL ↦ (hb x q L hL).1,
      norm_pos_iff.mp ((mul_pos hcp q.beat_pos).trans_le hlo), ?_⟩
    intro lam hlam
    exact frequency_bounds hlam hlo hb₀.2

end JanetCartan.SignedPairs
