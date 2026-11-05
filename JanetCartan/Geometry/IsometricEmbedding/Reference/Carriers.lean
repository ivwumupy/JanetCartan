module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.Inversion
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.NormalAvoidance

/-!
# Nonexceptional transverse detecting carriers for the cube pencil

Reciprocal algebra, complete nonexceptional pair selection, and the paired
carrier construction for Step 1 of `app:ch_seed:prop:seed-frozen-menu` in
`paper.tex`. We prove rank, regularity, avoidance of both codimension-three
bad-normal families, and the transversality assertion from Step 3 in carrier
coordinates.

Only the node lines in dimension five are excluded; their separate calculation
is Step 2. Constructing three-dimensional characteristic patches and the finite
menu requires the remaining geometric arguments of Steps 3 and 4.
-/

@[expose] public noncomputable section
namespace JanetCartan.CubeCarrier

/-- Every nonexceptional kernel stress admits a transverse detecting carrier.
This assembles the pair criterion, reciprocal construction, simplicity,
regularity, bad-normal avoidance, and incidence transversality from
`app:ch_seed:prop:seed-frozen-menu`, Steps 1 and 3. The sole exclusion is the
five-dimensional node lines from Step 2; no pair or geometric premise remains. -/
theorem exists_transverse_detecting_carrier_of_nonexceptional {n : ℕ} (hn : 5 ≤ n)
    {k s : Euclidean n} (hk : k ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hnode : n = 5 → ¬ ∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, k = t • cubeVector a b) :
    ∃ ξ : Euclidean n,
      (∀ i, ξ i ≠ 0) ∧
      cubeDeterminant ξ = 0 ∧ cubeDeterminant (reciprocal ξ) = 0 ∧
      (cubePencil ξ).rank = n - 1 ∧ (cubePencil (reciprocal ξ)).rank = n - 1 ∧
      fderiv ℝ cubeDeterminant ξ ≠ 0 ∧ fderiv ℝ cubeDeterminant (reciprocal ξ) ≠ 0 ∧
      quadratic ξ ≠ 0 ∧ quadratic (reciprocal ξ) ≠ 0 ∧
      (∑ i, k i * quadratic (reciprocal ξ) i) = 0 ∧
      (∑ i, s i * quadratic ξ i) ≠ 0 ∧
      (∀ i j l : Fin n, ∃ x : Euclidean n,
        x i = 0 ∧ x j = 0 ∧ x l = 0 ∧ (∑ a, x a * quadratic (reciprocal ξ) a) ≠ 0) ∧
      (∀ i j : Fin n, ∃ x : Euclidean n,
        x i = 0 ∧ x j = 0 ∧ (∑ a, x a) = 0 ∧
          (∑ a, x a * quadratic (reciprocal ξ) a) ≠ 0) ∧
      (∃ e : Euclidean n, fderiv ℝ cubeDeterminant ξ e = 0 ∧
        fderiv ℝ (fun x : Euclidean n ↦ ∑ i, k i * quadratic (reciprocal x) i) ξ e ≠ 0) := by
  obtain ⟨r, hr, hchar, hchar', hinc, hdet, hqr, hqrec, _, _, p, A, B, hab, hshape⟩ :=
    exists_detecting_reciprocal_with_nonproportional_vectors hn hk hs hker hnode
  have hrec : ∀ i, reciprocal r i ≠ 0 := fun i ↦ inv_ne_zero (hr i)
  refine ⟨reciprocal r, hrec, hchar', ?_⟩
  simp only [reciprocal_reciprocal]
  exact ⟨hchar, pencil_rank_of_characteristic hn hrec hchar',
    pencil_rank_of_characteristic hn hr hchar,
    regular_of_quadratic_reciprocal_ne_zero hrec hchar'
      (by simpa only [reciprocal_reciprocal] using hqr),
    regular_of_quadratic_reciprocal_ne_zero hr hchar hqrec,
    hqrec, hqr, hinc, hdet, paired_normal_triple_witness hab hshape,
    paired_normal_pair_sum_witness hn hab hshape,
    exists_transverse_carrier_tangent hk hs hr hker hchar hdet⟩

end JanetCartan.CubeCarrier
