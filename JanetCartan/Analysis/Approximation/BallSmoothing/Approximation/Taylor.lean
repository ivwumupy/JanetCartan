module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Basic
public import JanetCartan.Analysis.Approximation.BallSmoothing.Moments
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature.Taylor
public import Mathlib.Tactic

/-!
# Taylor cancellation for the literal inward samples

The finite coefficients cancel every Taylor order below `m`. The segment from
the original point to every inward sample stays in the closed unit ball, so
the remainder uses only the original closed-ball derivative seminorm. This is
the pointwise deduction in
`app:ch_regular_base:eq:ball-extension-continuous`, before averaging against
the actual fixed nonnegative kernel.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric Finset
open scoped ContDiff

namespace JanetCartan.BallSmoothing

open Sampling.BackgroundQuadrature

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem carrierTaylor_smul_euclidean (f : E → F) (m : ℕ) (x v : E) (t : ℝ) :
    carrierTaylor f m x (t • v) = ∑ k ∈ range m, t ^ k •
      ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ v)) := by
  unfold carrierTaylor
  apply sum_congr rfl
  intro k _
  rw [(iteratedFDeriv ℝ k f x).map_smul_univ]
  simp only [prod_const, card_univ, Fintype.card_fin]
  exact smul_comm _ _ _

private theorem sum_coefficient_scaled_pow {m k : ℕ} (hm : 1 ≤ m) (hk : k < m) (R : ℝ) :
    ∑ j ∈ Icc 1 m, coefficient m j * ((j : ℝ) / R) ^ k = if k = 0 then 1 else 0 := by
  calc
    _ = (∑ j ∈ Icc 1 m, coefficient m j * (j : ℝ) ^ k) / R ^ k := by
      rw [sum_div]
      apply sum_congr rfl
      intro j _
      rw [div_pow]
      ring
    _ = _ := by
      rw [sum_coefficient_mul_pow hm hk]
      by_cases hk0 : k = 0 <;> simp [hk0]

/-- The actual finite binomial coefficients retain precisely the constant
Taylor term, for the original Euclidean-fiber function and every displacement.
This is the cancellation in
`app:ch_regular_base:eq:extension-finite-moments`; no polynomial or output
exactness hypothesis is introduced. -/
theorem sum_coefficient_carrierTaylor_eq {m : ℕ} (hm : 1 ≤ m)
    (f : E → F) (x v : E) (R : ℝ) :
    ∑ j ∈ Icc 1 m, coefficient m j • carrierTaylor f m x (((j : ℝ) / R) • v) = f x := by
  classical
  calc
    _ = ∑ k ∈ range m, (∑ j ∈ Icc 1 m, coefficient m j * ((j : ℝ) / R) ^ k) •
        ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ v)) := by
      simp_rw [carrierTaylor_smul_euclidean, smul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      rw [sum_smul]
      apply sum_congr rfl
      intro j _
      rw [smul_smul]
    _ = ∑ k ∈ range m, (if k = 0 then (1 : ℝ) else 0) •
        ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ v)) := by
      apply sum_congr rfl
      intro k hk
      rw [sum_coefficient_scaled_pow hm (mem_range.mp hk)]
    _ = f x := by
      rw [sum_eq_single 0]
      · simp
      · intro k _ hk
        simp [hk]
      · intro hnot
        exact False.elim (hnot (mem_range.mpr (show 0 < m from hm)))

private theorem inward_segment_mem_closedBall {x y : E}
    (hx : x ∈ closedBall 0 1) (hy : y ∈ closedBall 0 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : x + t • (y-x) ∈ closedBall 0 1 := by
  have he : x + t • (y-x) = (1-t) • x + t • y := by module
  rw [he]
  exact (convex_closedBall (0 : E) 1) hx hy (sub_nonneg.mpr ht1) ht0 (by ring)

/-- A Taylor remainder of order `m` along the actual inward displacement
uses only `m` derivatives on the original closed unit ball. The kernel point
lies in the radius-`1/4` ball and hence the displacement has length at most
`5/4` (`app:ch_regular_base:eq:ball-extension-continuous`). -/
theorem norm_inwardTaylor_remainder_le [CompleteSpace F]
    {m : ℕ} (hm : 1 ≤ m) (f : E → F)
    (hf : ∀ z ∈ closedBall (0 : E) 1, ContDiffAt ℝ ∞ f z)
    {x y : E} (hx : x ∈ closedBall 0 1) (hy : y ∈ closedBall 0 (1/4 : ℝ))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖f (x + t • (y-x)) - carrierTaylor f m x (t • (y-x))‖ ≤
      (5/4 : ℝ)^m * t^m * cNorm (closedBall 0 1) m f := by
  have hy1 : y ∈ closedBall (0 : E) 1 := closedBall_subset_closedBall (by norm_num) hy
  have hs (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      x + s • (t • (y-x)) ∈ closedBall 0 1 := by
    rw [smul_smul]
    exact inward_segment_mem_closedBall hx hy1 (mul_nonneg hs.1 ht0)
      ((mul_le_of_le_one_left ht0 hs.2).trans ht1)
  have hb := norm_sub_carrierTaylor_le (show 0 < m from hm)
    (cNorm_nonneg (closedBall (0 : E) 1) m f)
    (fun s hs' ↦ (hf _ (hs s hs')).of_le (by simp))
    (fun s hs' ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall 0 1)
      (fun z hz ↦ (hf z hz).of_le (by simp)) (hs s hs') (le_refl m))
  have hdist : ‖y-x‖ ≤ (5/4 : ℝ) := by
    have hxn : ‖x‖ ≤ (1 : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hyn : ‖y‖ ≤ (1/4 : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hy
    exact (norm_sub_le y x).trans (by linarith)
  calc
    _ ≤ cNorm (closedBall (0 : E) 1) m f * ‖t • (y-x)‖^m := hb
    _ = cNorm (closedBall (0 : E) 1) m f * t^m * ‖y-x‖^m := by
      rw [norm_smul, Real.norm_of_nonneg ht0, mul_pow]
      ring
    _ ≤ cNorm (closedBall (0 : E) 1) m f * t^m * (5/4 : ℝ)^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist _)
        (mul_nonneg (cNorm_nonneg _ _ _) (pow_nonneg ht0 _))
    _ = _ := by ring

/-- Before averaging, the literal finite inward samples already have an
order-`m` error with a constant chosen independently of the scale and input.
The real binomial signs are exactly those of the manuscript, and no extension
of `f` is used (`app:ch_regular_base:eq:extension-radial-formula`,
`app:ch_regular_base:eq:ball-extension-continuous`). -/
theorem norm_radial_sample_combination_sub_le [CompleteSpace F]
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    (f : E → F) (hf : ∀ z ∈ closedBall (0 : E) 1, ContDiffAt ℝ ∞ f z)
    {x y : E} (hx : x ∈ closedBall 0 1) (hy : y ∈ closedBall 0 (1/4 : ℝ)) :
    ‖(∑ j ∈ Icc 1 m, coefficient m j • f (radialPoint R j x y)) - f x‖ ≤
      ((5/4 : ℝ)^m * ∑ j ∈ Icc 1 m, |coefficient m j| * (j : ℝ)^m) *
        (R⁻¹)^m * cNorm (closedBall 0 1) m f := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m from hm)
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have ht j (hj : j ∈ Finset.Icc 1 m) : 0 ≤ (j : ℝ)/R ∧ (j : ℝ)/R ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hRpos.le, (div_le_iff₀ hRpos).mpr ?_⟩
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    linarith
  have hpoint j : radialPoint R j x y = x + ((j : ℝ)/R) • (y-x) := by
    unfold radialPoint
    module
  have hcancel := sum_coefficient_carrierTaylor_eq hm f x (y-x) R
  have he : (∑ j ∈ Icc 1 m, coefficient m j •
      (f (radialPoint R j x y) - carrierTaylor f m x (((j : ℝ)/R) • (y-x)))) =
      (∑ j ∈ Icc 1 m, coefficient m j • f (radialPoint R j x y)) - f x := by
    calc
      _ = ∑ j ∈ Icc 1 m, (coefficient m j • f (radialPoint R j x y) -
          coefficient m j • carrierTaylor f m x (((j : ℝ)/R) • (y-x))) :=
        sum_congr rfl (fun _ _ ↦ smul_sub _ _ _)
      _ = _ := by rw [sum_sub_distrib, hcancel]
  rw [← he]
  calc
    _ ≤ ∑ j ∈ Icc 1 m, ‖coefficient m j •
        (f (radialPoint R j x y) - carrierTaylor f m x (((j : ℝ)/R) • (y-x)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Icc 1 m, |coefficient m j| *
        ((5/4 : ℝ)^m * ((j : ℝ)/R)^m * cNorm (closedBall 0 1) m f) := by
      apply sum_le_sum
      intro j hj
      rw [norm_smul, Real.norm_eq_abs, hpoint]
      exact mul_le_mul_of_nonneg_left
        (norm_inwardTaylor_remainder_le hm f hf hx hy (ht j hj).1 (ht j hj).2) (abs_nonneg _)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_pow, mul_sum, sum_mul]
      apply sum_congr rfl
      intro j _
      ring

end JanetCartan.BallSmoothing
