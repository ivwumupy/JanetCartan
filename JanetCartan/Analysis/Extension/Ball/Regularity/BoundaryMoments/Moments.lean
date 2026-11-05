module

public import JanetCartan.Analysis.Extension.Ball.Regularity.Jets
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Applying the Seeley moments to multilinear expressions

The identities in `app:ch_regular_base:eq:extension-infinite-moments`
evaluate every finite multilinear expression in affine functions of `bₖ = -2^k`
at `b = 1`. This is the algebraic step of the boundary-jet argument after
`app:ch_regular_base:eq:extension-collar-l2`.
-/

@[expose] public noncomputable section

namespace JanetCartan.BallExtension

/-- Absolute moments in `app:ch_regular_base:eq:extension-infinite-moments`
give convergence of each signed moment. -/
theorem summable_signed_moment (a : ℕ → ℝ) (ell : ℕ)
    (ha : Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell))) :
    Summable (fun k ↦ a k * (-(2 : ℝ) ^ k) ^ ell) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_pow, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    ← pow_mul] using ha

/-- A multilinear expression in affine functions of a scalar is a polynomial;
this explicit expansion is used with `app:ch_regular_base:eq:extension-infinite-moments`. -/
theorem multilinear_affine_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (M : ContinuousMultilinearMap ℝ V W) (u v : ∀ i, V i) (b : ℝ) :
    M (fun i ↦ u i + b • v i) =
      ∑ s : Finset ι, b ^ s.card • M (s.piecewise v u) := by
  classical
  have h : (fun i ↦ u i + b • v i) = (fun i ↦ b • v i) + u := by
    ext i; simp [add_comm]
  rw [h, M.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have he : s.piecewise (fun i ↦ b • v i) u =
      s.piecewise (fun i ↦ b • s.piecewise v u i) (s.piecewise v u) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [he, M.map_piecewise_smul]
  simp

/-- The moments in `app:ch_regular_base:eq:extension-infinite-moments`
sum any continuous multilinear expression in affine functions of `-2^k`
to its value at one, including convergence in the target norm. -/
theorem hasSum_multilinear_affine_moments (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    (hm : ∀ ell : ℕ, (∑' k, a k * (-(2 : ℝ) ^ k) ^ ell) = 1)
    {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (M : ContinuousMultilinearMap ℝ V W) (u v : ∀ i, V i) :
    HasSum (fun k ↦ a k • M (fun i ↦ u i + (-(2 : ℝ) ^ k) • v i))
      (M (fun i ↦ u i + v i)) := by
  classical
  have hs (s : Finset ι) :
      HasSum (fun k ↦ (a k * (-(2 : ℝ) ^ k) ^ s.card) • M (s.piecewise v u))
        (M (s.piecewise v u)) := by
    have h := ((summable_signed_moment a s.card (ha s.card)).hasSum)
    rw [hm] at h
    simpa using h.smul_const (M (s.piecewise v u))
  have h := hasSum_sum (s := Finset.univ) (fun s _ ↦ hs s)
  have he := multilinear_affine_expansion M u v 1
  simp only [one_smul, one_pow] at he
  rw [he]
  simpa only [multilinear_affine_expansion, Finset.smul_sum, smul_smul] using h

/-- The Faà di Bruno composition is a finite sum of multilinear expressions,
so the moments in `app:ch_regular_base:eq:extension-infinite-moments`
evaluate an affine family of inner jets at one. -/
theorem hasSum_taylorComp_affine_moments (a : ℕ → ℝ)
    (ha : ∀ ell : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ell)))
    (hm : ∀ ell : ℕ, (∑' k, a k * (-(2 : ℝ) ^ k) ^ ell) = 1)
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : FormalMultilinearSeries ℝ F G) (u v : FormalMultilinearSeries ℝ E F) (m : ℕ) :
    HasSum (fun k ↦ a k • q.taylorComp (fun j ↦ u j + (-(2 : ℝ) ^ k) • v j) m)
      (q.taylorComp (fun j ↦ u j + v j) m) := by
  classical
  simp only [FormalMultilinearSeries.taylorComp, Finset.smul_sum]
  apply hasSum_sum
  intro c _
  exact hasSum_multilinear_affine_moments a ha hm
    (c.compAlongOrderedFinpartitionL ℝ E F G (q c.length))
    (fun i ↦ u (c.partSize i)) (fun i ↦ v (c.partSize i))

end JanetCartan.BallExtension
