module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The radial ball-extension formula

This file constructs the pointwise operator in
`app:ch_regular_base:eq:extension-radial-formula` of paper.tex. The coefficients are
parameters: no moment identities are needed for linearity, restriction, or support.
Smoothness across the sphere and bounds on derivatives require additional proofs.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.BallExtension

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Geometric choices in the proof of `app:ch_regular_base:lem:ball-extension`.
The positive collar width is smaller than half the ball radius. -/
structure Parameters where
  center : E
  radius : ℝ
  radius_pos : 0 < radius
  width : ℝ
  width_pos : 0 < width
  width_lt : width < radius / 2

variable {E}

/-- The collar in `app:ch_regular_base:lem:ball-extension` can be chosen inside
any open neighborhood of the closed ball. -/
theorem exists_parameters [FiniteDimensional ℝ E] (c : E) {R : ℝ} (hR : 0 < R)
    {V : Set E} (hV : IsOpen V) (hRV : closedBall c R ⊆ V) :
    ∃ p : Parameters E, p.center = c ∧ p.radius = R ∧
      closedBall p.center (p.radius + p.width) ⊆ V := by
  obtain ⟨ε, hε, hεV⟩ := (isCompact_closedBall c R).exists_cthickening_subset_open hV hRV
  rw [cthickening_closedBall hε.le hR.le, add_comm ε R] at hεV
  refine ⟨⟨c, R, hR, min ε (R / 4), lt_min hε (by positivity), ?_⟩, rfl, rfl, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · apply Subset.trans (closedBall_subset_closedBall (show R + min ε (R / 4) ≤ R + ε from ?_)) hεV
    linarith [min_le_left ε (R / 4)]

namespace Parameters

variable (p : Parameters E)

/-- The fixed cutoff from `app:ch_regular_base:eq:extension-radial-formula`:
one on `[0, d/4]` and zero on `[d/2, ∞)`. -/
def cutoff : ContDiffBump (0 : ℝ) where
  rIn := p.width / 4
  rOut := p.width / 2
  rIn_pos := by linarith [p.width_pos]
  rIn_lt_rOut := by linarith [p.width_pos]

/-- The interior sampling point in `app:ch_regular_base:eq:extension-radial-formula`. -/
def radialPoint (k : ℕ) (x : E) : E :=
  p.center + ((p.radius - (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) /
    ‖x - p.center‖) • (x - p.center)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- One term in `app:ch_regular_base:eq:extension-radial-formula`. -/
def summand (a : ℕ → ℝ) (f : E → F) (x : E) (k : ℕ) : F :=
  (a k * p.cutoff ((2 : ℝ) ^ k * (‖x - p.center‖ - p.radius))) •
    f (p.radialPoint k x)

/-- The single, order-independent pointwise formula of
`app:ch_regular_base:eq:extension-radial-formula`, including the boundary values. -/
def extend (a : ℕ → ℝ) (f : E → F) (x : E) : F :=
  if ‖x - p.center‖ ≤ p.radius then f x else ∑' k, p.summand a f x k

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The cutoff has the values prescribed in the proof of
`app:ch_regular_base:lem:ball-extension`. -/
theorem cutoff_eq_one {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ p.width / 4) :
    p.cutoff s = 1 := by
  apply p.cutoff.one_of_mem_closedBall
  simpa [mem_closedBall, Real.dist_eq, abs_of_nonneg hs, cutoff] using hs'

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The fixed outer cutoff in `app:ch_regular_base:eq:extension-radial-formula`. -/
theorem cutoff_eq_zero {s : ℝ} (hs : p.width / 2 ≤ s) : p.cutoff s = 0 := by
  apply p.cutoff.zero_of_le_dist
  have hs0 : 0 ≤ s := by linarith [p.width_pos]
  simpa [Real.dist_eq, abs_of_nonneg hs0, cutoff] using hs

/-- Terms outside the cutoff vanish in `app:ch_regular_base:eq:extension-radial-formula`. -/
theorem summand_eq_zero (a : ℕ → ℝ) (f : E → F) (x : E) (k : ℕ)
    (hk : p.width / 2 ≤ (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) :
    p.summand a f x k = 0 := by
  simp [summand, p.cutoff_eq_zero hk]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The sum in `app:ch_regular_base:eq:extension-radial-formula` is uniformly
finite whenever the exterior distance is bounded below by a positive number. -/
theorem exists_truncation {t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, ∀ s : ℝ, t ≤ s → ∀ k : ℕ, N ≤ k → p.width / 2 ≤ (2 : ℝ) ^ k * s := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (p.width / 2 / t) (by norm_num : (1 : ℝ) < 2)
  refine ⟨N, fun s hs k hk ↦ ?_⟩
  calc
    p.width / 2 ≤ (2 : ℝ) ^ N * t := ((div_lt_iff₀ ht).mp hN).le
    _ ≤ (2 : ℝ) ^ k * s := mul_le_mul
      (pow_le_pow_right₀ (by norm_num) hk) hs ht.le (by positivity)

/-- A finite-sum version of `app:ch_regular_base:eq:extension-radial-formula`. -/
theorem extend_eq_sum (a : ℕ → ℝ) (f : E → F) {x : E}
    (hx : p.radius < ‖x - p.center‖) {N : ℕ}
    (hN : ∀ k : ℕ, N ≤ k → p.width / 2 ≤ (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) :
    p.extend a f x = ∑ k ∈ Finset.range N, p.summand a f x k := by
  rw [extend, ite_eq_right (not_le.mpr hx)]
  exact tsum_eq_sum (fun k hk ↦ p.summand_eq_zero a f x k
    (hN k (Nat.le_of_not_gt (by simpa using hk))))

/-- Exact restriction, including the sphere, in
`app:ch_regular_base:lem:ball-extension`. -/
theorem extend_eq_on_closedBall (a : ℕ → ℝ) (f : E → F) :
    EqOn (p.extend a f) f (closedBall p.center p.radius) := by
  intro x hx
  exact ite_eq_left (mem_closedBall_iff_norm.mp hx)

/-- Additivity of the fixed formula in `app:ch_regular_base:eq:extension-radial-formula`. -/
theorem extend_add (a : ℕ → ℝ) (f g : E → F) :
    p.extend a (f + g) = p.extend a f + p.extend a g := by
  funext x
  by_cases hx : ‖x - p.center‖ ≤ p.radius
  · simp [extend, hx]
  · have ht : 0 < ‖x - p.center‖ - p.radius := sub_pos.mpr (lt_of_not_ge hx)
    obtain ⟨N, hN⟩ := p.exists_truncation ht
    simp only [Pi.add_apply]
    rw [p.extend_eq_sum a (f + g) (lt_of_not_ge hx) (hN _ le_rfl),
      p.extend_eq_sum a f (lt_of_not_ge hx) (hN _ le_rfl),
      p.extend_eq_sum a g (lt_of_not_ge hx) (hN _ le_rfl)]
    simp [summand, smul_add, Finset.sum_add_distrib]

/-- Real homogeneity of the fixed formula in
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem extend_smul (a : ℕ → ℝ) (r : ℝ) (f : E → F) :
    p.extend a (r • f) = r • p.extend a f := by
  funext x
  by_cases hx : ‖x - p.center‖ ≤ p.radius
  · simp [extend, hx]
  · have ht : 0 < ‖x - p.center‖ - p.radius := sub_pos.mpr (lt_of_not_ge hx)
    obtain ⟨N, hN⟩ := p.exists_truncation ht
    simp only [Pi.smul_apply]
    rw [p.extend_eq_sum a (r • f) (lt_of_not_ge hx) (hN _ le_rfl),
      p.extend_eq_sum a f (lt_of_not_ge hx) (hN _ le_rfl), Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [summand, Pi.smul_apply]
    exact smul_comm _ _ _

/-- The actual pointwise linear operator of
`app:ch_regular_base:eq:extension-radial-formula`. Its definition has no order parameter. -/
def linearMap (a : ℕ → ℝ) : (E → F) →ₗ[ℝ] (E → F) where
  toFun := p.extend a
  map_add' := p.extend_add a
  map_smul' := p.extend_smul a

/-- Outside the fixed collar the formula vanishes, as in the proof of
`app:ch_regular_base:lem:ball-extension`. -/
theorem extend_eq_zero (a : ℕ → ℝ) (f : E → F) {x : E}
    (hx : p.radius + p.width / 2 ≤ ‖x - p.center‖) : p.extend a f x = 0 := by
  have ht : 0 ≤ ‖x - p.center‖ - p.radius := by linarith [p.width_pos]
  rw [extend, ite_eq_right (by linarith [p.width_pos])]
  have hz (k : ℕ) : p.summand a f x k = 0 := by
    apply p.summand_eq_zero
    calc
      p.width / 2 ≤ ‖x - p.center‖ - p.radius := by linarith
      _ ≤ (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) :=
        le_mul_of_one_le_left ht (one_le_pow₀ (by norm_num))
  simp only [hz, tsum_zero]

/-- One fixed support set for every input and every order, as in
`app:ch_regular_base:lem:ball-extension`. -/
theorem tsupport_extend_subset (a : ℕ → ℝ) (f : E → F) :
    tsupport (p.extend a f) ⊆ closedBall p.center (p.radius + p.width / 2) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra h
  exact hx (p.extend_eq_zero a f (le_of_lt (lt_of_not_ge (mem_closedBall_iff_norm.not.mp h))))

/-- Compact support of the pointwise extension in finite dimension, as in
`app:ch_regular_base:lem:ball-extension`. -/
theorem hasCompactSupport_extend [FiniteDimensional ℝ E] (a : ℕ → ℝ) (f : E → F) :
    HasCompactSupport (p.extend a f) :=
  (isCompact_closedBall p.center (p.radius + p.width / 2)).of_isClosed_subset
    isClosed_closure (p.tsupport_extend_subset a f)

/-- Every active exterior term samples strictly inside the original ball in
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem radialPoint_mem_ball {x : E} (hx : p.radius < ‖x - p.center‖) {k : ℕ}
    (hk : p.cutoff ((2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) ≠ 0) :
    p.radialPoint k x ∈ ball p.center p.radius := by
  have ht : 0 < ‖x - p.center‖ - p.radius := sub_pos.mpr hx
  have hs : 0 < (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := mul_pos (by positivity) ht
  have hs' : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width / 2 := by
    by_contra h
    exact hk (p.cutoff_eq_zero (le_of_not_gt h))
  have hinner : 0 < p.radius - (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
    linarith [p.width_lt, p.radius_pos]
  have hnorm : 0 < ‖x - p.center‖ := p.radius_pos.trans hx
  rw [mem_ball_iff_norm, radialPoint, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos hinner hnorm), div_mul_cancel₀ _ hnorm.ne']
  linarith

/-- The operator depends only on the restriction to the closed ball, as required
for the domain `C∞(closure Ω)` in `app:ch_regular_base:lem:ball-extension`. -/
theorem extend_congr (a : ℕ → ℝ) {f g : E → F}
    (hfg : EqOn f g (closedBall p.center p.radius)) : p.extend a f = p.extend a g := by
  funext x
  by_cases hx : ‖x - p.center‖ ≤ p.radius
  · simpa [extend, hx] using hfg (mem_closedBall_iff_norm.mpr hx)
  · simp only [extend, ite_eq_right hx]
    apply tsum_congr
    intro k
    by_cases hk : p.cutoff ((2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) = 0
    · simp [summand, hk]
    · simp only [summand, hfg (ball_subset_closedBall
        (p.radialPoint_mem_ball (lt_of_not_ge hx) hk))]

/-- The fixed support is contained in the chosen open neighborhood in
`app:ch_regular_base:lem:ball-extension`. -/
theorem tsupport_extend_subset_of_collar_subset (a : ℕ → ℝ) (f : E → F)
    {V : Set E} (hV : closedBall p.center (p.radius + p.width) ⊆ V) :
    tsupport (p.extend a f) ⊆ V :=
  (p.tsupport_extend_subset a f).trans
    ((closedBall_subset_closedBall (by linarith [p.width_pos])).trans hV)

/-- Componentwise compatibility of the actual formula in
`app:ch_regular_base:lem:ball-extension`. No continuity of the linear map is needed
because each exterior sum is finite. -/
theorem extend_map {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : ℕ → ℝ) (L : F →ₗ[ℝ] G) (f : E → F) :
    p.extend a (L ∘ f) = L ∘ p.extend a f := by
  funext x
  by_cases hx : ‖x - p.center‖ ≤ p.radius
  · simp [extend, hx]
  · have ht : 0 < ‖x - p.center‖ - p.radius := sub_pos.mpr (lt_of_not_ge hx)
    obtain ⟨N, hN⟩ := p.exists_truncation ht
    simp only [Function.comp_apply]
    rw [p.extend_eq_sum a (L ∘ f) (lt_of_not_ge hx) (hN _ le_rfl),
      p.extend_eq_sum a f (lt_of_not_ge hx) (hN _ le_rfl)]
    simp [summand]

/-- The order-zero term bound underlying
`app:ch_regular_base:eq:ball-extension-continuous`. -/
theorem norm_summand_le (a : ℕ → ℝ) (f : E → F) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ y ∈ closedBall p.center p.radius, ‖f y‖ ≤ M) {x : E}
    (hx : p.radius < ‖x - p.center‖) (k : ℕ) : ‖p.summand a f x k‖ ≤ |a k| * M := by
  by_cases hk : p.cutoff ((2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) = 0
  · simpa [summand, hk] using mul_nonneg (abs_nonneg (a k)) hM
  · have hf' := hf _ (ball_subset_closedBall (p.radialPoint_mem_ball hx hk))
    have hc : ‖a k * p.cutoff ((2 : ℝ) ^ k * (‖x - p.center‖ - p.radius))‖ ≤ |a k| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg p.cutoff.nonneg]
      exact mul_le_of_le_one_right (abs_nonneg _) p.cutoff.le_one
    rw [summand, norm_smul]
    exact mul_le_mul hc hf' (norm_nonneg _) (abs_nonneg _)

/-- A uniform order-zero bound for the same operator, from the absolute zeroth
moment in `app:ch_regular_base:eq:extension-infinite-moments`. This does not
assert higher derivative bounds or smoothness across the boundary. -/
theorem norm_extend_le (a : ℕ → ℝ) (ha : Summable (fun k ↦ |a k|))
    (f : E → F) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ y ∈ closedBall p.center p.radius, ‖f y‖ ≤ M) (x : E) :
    ‖p.extend a f x‖ ≤ max 1 (∑' k, |a k|) * M := by
  by_cases hx : ‖x - p.center‖ ≤ p.radius
  · rw [p.extend_eq_on_closedBall a f (mem_closedBall_iff_norm.mpr hx)]
    exact (hf _ (mem_closedBall_iff_norm.mpr hx)).trans
      (le_mul_of_one_le_left hM (le_max_left _ _))
  · have ht : 0 < ‖x - p.center‖ - p.radius := sub_pos.mpr (lt_of_not_ge hx)
    obtain ⟨N, hN⟩ := p.exists_truncation ht
    rw [p.extend_eq_sum a f (lt_of_not_ge hx) (hN _ le_rfl)]
    calc
      ‖∑ k ∈ Finset.range N, p.summand a f x k‖
          ≤ ∑ k ∈ Finset.range N, ‖p.summand a f x k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, |a k| * M :=
        Finset.sum_le_sum (fun k _ ↦ p.norm_summand_le a f hM hf (lt_of_not_ge hx) k)
      _ = (∑ k ∈ Finset.range N, |a k|) * M := (Finset.sum_mul _ _ _).symm
      _ ≤ (∑' k, |a k|) * M := mul_le_mul_of_nonneg_right
        (ha.sum_le_tsum _ (fun k _ ↦ abs_nonneg (a k))) hM
      _ ≤ max 1 (∑' k, |a k|) * M := mul_le_mul_of_nonneg_right (le_max_right _ _) hM

end Parameters
end JanetCartan.BallExtension
