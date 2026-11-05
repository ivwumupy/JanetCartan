module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.SingularGap.PairGap
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.AngularConstruction
public import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# The numbered singular-value gap for actual angular pencils

Item 1 and Step 2 of `app:ch_seed:prop:seed-actual-menu` require a lower
bound for the `(n-1)`st singular value, not just rank at least `n-1`.
Here this is Mathlib's `LinearMap.singularValues` at zero-based index
`n-2`, for the literal real map `A.toEuclideanLin` in the original
Euclidean coordinates. The matrix and adjugate norms are Frobenius norms.

The proof uses compactness of bounded matrices and orthonormal pairs.
A positive adjugate gap forbids two kernel directions, so the sum of the
two image norms has a uniform positive lower bound. For the last two
right singular vectors those norms are exactly the last two singular
values, each at most the `(n-1)`st one. This proves the comparison without
assuming spectral continuity. The final corollary instantiates the actual
bounds from the componentwise `C⁶` projected-frame neighborhood.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

private theorem norm_image_eigenvectorBasis_eq_singularValues {n : ℕ}
    (T : Euclidean n →ₗ[ℝ] Euclidean n) (i : Fin n) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin i)‖ =
      T.singularValues i := by
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin
  have he := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis
    finrank_euclideanSpace_fin i
  have hi := congrArg (fun v ↦ inner ℝ (b i) v) he
  change inner ℝ (b i) (T.adjoint (T (b i))) =
    inner ℝ (b i) ((T.isSymmetric_adjoint_comp_self.eigenvalues
      finrank_euclideanSpace_fin i) • b i) at hi
  rw [T.adjoint_inner_right, real_inner_self_eq_norm_sq] at hi
  simp only [inner_smul_right, real_inner_self_eq_norm_sq,
    b.orthonormal.norm_eq_one, one_pow, mul_one] at hi
  rw [← T.sq_singularValues_fin finrank_euclideanSpace_fin] at hi
  exact (sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg i)).mp hi

/-- The numbered singular-value estimate of `app:ch_seed:prop:seed-actual-menu`,
item 1 and Step 2, for arbitrary real matrices. The constant depends only on
`n`, the positive Frobenius adjugate gap `a`, and the matrix bound `M`.
The Euclidean map is literally multiplication by `A`, as recorded in
`toEuclideanLin_apply_coordinate`; `n-2` is the zero-based index of the
`(n-1)`st singular value. -/
theorem exists_uniform_singularValue_gap_of_adjugate {n : ℕ} (hn : 5 ≤ n)
    {a M : ℝ} (ha : 0 < a) (_hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : MetricTensor n,
      a ≤ ‖A.adjugate‖ → ‖A‖ ≤ M →
        c ≤ A.toEuclideanLin.singularValues (n - 2) := by
  obtain ⟨d, hd, hpair⟩ := exists_uniform_orthonormal_pair_image_gap (n := n) (by omega) ha M
  refine ⟨d / 2, by positivity, ?_⟩
  intro A hgap hM
  let e : Fin 2 → Fin n := fun i ↦ ⟨n - 2 + i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [e] at this
    omega
  let b := A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvectorBasis
    finrank_euclideanSpace_fin
  have hb : Orthonormal ℝ (b ∘ e) := b.orthonormal.comp e he
  have hl := hpair A hgap hM (b ∘ e) hb
  have hu : (∑ i : Fin 2, ‖A.toEuclideanLin ((b ∘ e) i)‖) ≤
      2 * A.toEuclideanLin.singularValues (n - 2) := by
    calc
      _ ≤ ∑ _i : Fin 2, A.toEuclideanLin.singularValues (n - 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [Function.comp_apply, norm_image_eigenvectorBasis_eq_singularValues]
        exact A.toEuclideanLin.singularValues_antitone (by dsimp [e]; omega)
      _ = _ := by simp
  linarith

open SignedPairs ProjectedStressFrame in
/-- The actual angular singular-value bound in `app:ch_seed:prop:seed-actual-menu`,
item 1 and Step 2. The only perturbation assumption is the paper's
componentwise `C⁶` frame neighborhood. All constants precede the immersion
and its higher norms. The adjugate, rank, matrix and simple-zero bounds of
`exists_projectedStress_angular_neighborhood` are retained, and its actual
adjugate and matrix bounds are instantiated in the numbered spectral estimate.
Signed-direction inclusion and final carrier assembly remain with the parent
construction. -/
theorem exists_projectedStress_angular_singular_neighborhood {n : ℕ} (hn : 5 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ δ a c d M : ℝ,
      0 < δ ∧ 0 < a ∧ 0 < c ∧ 0 < d ∧ 0 < M ∧
      ∀ (N : ℕ) (F : Euclidean n → Euclidean N) (U K : Set (Euclidean n)),
        IsOpen U → IsCompact K → K ⊆ U →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) < δ) →
        ∀ x ∈ K, ∀ v ∈ angularSet n γ,
          a ≤ ‖(pencil (projectedStress F x) v).adjugate‖ ∧
          n - 1 ≤ (pencil (projectedStress F x) v).rank ∧
          ‖pencil (projectedStress F x) v‖ ≤ M ∧
          c ≤ (pencil (projectedStress F x) v).toEuclideanLin.singularValues (n - 2) ∧
          (determinant (projectedStress F x) v = 0 →
            d ≤ ‖fderiv ℝ (determinant (projectedStress F x)) v‖) := by
  obtain ⟨δ, a, d, M, hδ, ha, hd, hM, hreg⟩ :=
    exists_projectedStress_angular_neighborhood hn hγ
  obtain ⟨c, hc, hsing⟩ := exists_uniform_singularValue_gap_of_adjugate hn ha hM
  refine ⟨δ, a, c, d, M, hδ, ha, hc, hd, hM, ?_⟩
  intro N F U K hU hK hKU hF hi hr hclose x hx v hv
  obtain ⟨hgap, hrank, hbound, hzero⟩ :=
    hreg N F U K hU hK hKU hF hi hr hclose x hx v hv
  exact ⟨hgap, hrank, hbound, hsing _ hgap hbound, hzero⟩

end JanetCartan.ActualCarriers
