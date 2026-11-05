module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Cutoff.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Basic
import Mathlib.Tactic.Ring

/-!
# Uniform derivative costs of the actual thin ball cutoff

All constants are chosen from the fixed transition function and the squared
radius on the fixed ball of radius two. The chain rule then gives one power
of `R` per derivative, uniformly for every `R ≥ 1`. This supplies the cutoff
factor in `app:ch_regular_base:eq:ball-extension-sobolev` and hence
`main:eq:smoothing-low`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.BallSmoothing

private theorem exists_smoothTransition_jet_bounds :
    ∃ B : ℕ → ℝ, (∀ r, 0 ≤ B r) ∧
      ∀ r j, j ≤ r → ∀ x, ‖iteratedFDeriv ℝ j Real.smoothTransition x‖ ≤ B r := by
  let B (r : ℕ) := 1 + cNorm (Icc (0 : ℝ) 1) r Real.smoothTransition
  have hB r : 0 ≤ B r := add_nonneg zero_le_one (cNorm_nonneg _ _ _)
  have hB1 r : 1 ≤ B r := by dsimp only [B]; linarith [cNorm_nonneg (Icc (0 : ℝ) 1) r Real.smoothTransition]
  refine ⟨B,hB,?_⟩
  intro r j hj x
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero,Real.norm_of_nonneg (Real.smoothTransition.nonneg x)]
    exact (Real.smoothTransition.le_one x).trans (hB1 r)
  | succ j =>
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · exact (norm_iteratedFDeriv_le_cNorm isCompact_Icc
        (Real.smoothTransition.contDiff : ContDiff ℝ r Real.smoothTransition) hx hj).trans
        (by dsimp only [B]; linarith)
    · by_cases hx0 : x < 0
      · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
          filter_upwards [gt_mem_nhds hx0] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le
        rw [(he.iteratedFDeriv ℝ (j+1)).eq_of_nhds]
        rw [iteratedFDeriv_succ_const]
        simpa using hB r
      · have hx1 : 1 < x := by
          by_contra hn
          exact hx ⟨le_of_not_gt hx0,le_of_not_gt hn⟩
        have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
          filter_upwards [lt_mem_nhds hx1] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
        rw [(he.iteratedFDeriv ℝ (j+1)).eq_of_nhds]
        rw [iteratedFDeriv_succ_const]
        simpa using hB r

/-- Fixed constants bound every global derivative and the native global
`C^r` seminorm of the SAME actual cutoff by `C r * R^r`. The constants are
chosen before the varying scale. This is the required quantitative cutoff
input to `app:ch_regular_base:lem:ball-extension` and `main:lem:smoothing`. -/
theorem exists_unitCutoff_global_bounds (n : ℕ) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ r x, ‖iteratedFDeriv ℝ r (unitCutoff n R) x‖ ≤ C r*R^r) ∧
      ∀ R : ℝ, 1 ≤ R → ∀ r, cNorm univ r (unitCutoff n R) ≤ C r*R^r := by
  obtain ⟨B,hB,hBbound⟩ := exists_smoothTransition_jet_bounds
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ ‖x‖^2-1
  have hq : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).sub contDiff_const
  let M (r : ℕ) := 1 + cNorm (closedBall (0 : EuclideanSpace ℝ (Fin n)) 2) r q
  have hM r : 1 ≤ M r := by dsimp only [M]; linarith [cNorm_nonneg (closedBall (0 : EuclideanSpace ℝ (Fin n)) 2) r q]
  have hM0 r : 0 ≤ M r := zero_le_one.trans (hM r)
  let inner (R : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ 2 - (8*R) • q x
  have hinner R : ContDiff ℝ ∞ (inner R) := contDiff_const.sub (hq.const_smul (8*R))
  have hinnerBound R (hR : 1 ≤ R) r j (hj : 1 ≤ j) (hjr : j ≤ r)
      x (hx : x ∈ closedBall 0 2) :
      ‖iteratedFDeriv ℝ j (inner R) x‖ ≤ (8*M r*R)^j := by
    have hqj : ContDiffAt ℝ j q x := (hq.of_le (by simp)).contDiffAt
    change ‖iteratedFDeriv ℝ j ((fun _ ↦ (2 : ℝ)) - (fun y ↦ (8*R) • q y)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply contDiffAt_const (hqj.const_smul (8*R)),
      iteratedFDeriv_const_of_ne (by omega : j ≠ 0),Pi.zero_apply,zero_sub,norm_neg,
      iteratedFDeriv_const_smul_apply' hqj,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ 8*R)]
    have hqbound : ‖iteratedFDeriv ℝ j q x‖ ≤ M r :=
      (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
        (hq.of_le (by simp)) hx hjr).trans (by dsimp only [M]; linarith)
    calc
      _ ≤ (8*R)*M r := mul_le_mul_of_nonneg_left hqbound (by positivity)
      _ = 8*M r*R := by ring
      _ ≤ (8*M r*R)^j := le_self_pow₀
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ) ≤ 8) (hM r)) hR)
        (by omega)
  let A (r : ℕ) : ℝ := (r.factorial : ℝ)*B r*(8*M r)^r
  have hA r : 0 ≤ A r := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hB r)) (pow_nonneg (mul_nonneg (by norm_num) (hM0 r)) _)
  have hlocal R (hR : 1 ≤ R) r x (hx : x ∈ closedBall 0 2) :
      ‖iteratedFDeriv ℝ r (unitCutoff n R) x‖ ≤ A r*R^r := by
    have hh := norm_iteratedFDeriv_comp_le
      (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition) (hinner R)
      (by simp : (r : ℕ∞ω) ≤ ∞) x
      (fun j hj ↦ hBbound r j hj ((inner R) x))
      (fun j hj hjr ↦ hinnerBound R hR r j hj hjr x hx)
    change ‖iteratedFDeriv ℝ r (unitCutoff n R) x‖ ≤ _ at hh
    exact hh.trans_eq (by dsimp only [A]; rw [mul_pow]; ring)
  have hglobal R (hR : 1 ≤ R) r x :
      ‖iteratedFDeriv ℝ r (unitCutoff n R) x‖ ≤ A r*R^r := by
    by_cases hx : x ∈ closedBall 0 2
    · exact hlocal R hR r x hx
    · have hxt : x ∉ tsupport (iteratedFDeriv ℝ r (unitCutoff n R)) := fun h ↦
        hx (unitCutoff_tsupport_subset_closedBall_two n hR (tsupport_iteratedFDeriv_subset r h))
      rw [image_eq_zero_of_notMem_tsupport hxt,norm_zero]
      exact mul_nonneg (hA r) (pow_nonneg (zero_le_one.trans hR) _)
  let C (r : ℕ) : ℝ := ∑ j ∈ Finset.range (r+1), A j
  have hC r : 0 ≤ C r := Finset.sum_nonneg (fun j _ ↦ hA j)
  have hAC r : A r ≤ C r := Finset.single_le_sum (fun j _ ↦ hA j) (by simp)
  refine ⟨C,hC,?_,?_⟩
  · intro R hR r x
    exact (hglobal R hR r x).trans
      (mul_le_mul_of_nonneg_right (hAC r) (pow_nonneg (zero_le_one.trans hR) _))
  · intro R hR r
    calc
      cNorm univ r (unitCutoff n R) ≤ ∑ j ∈ Finset.range (r+1), A j*R^j :=
        cNorm_le_sum_of_bounds
          (fun j _ ↦ mul_nonneg (hA j) (pow_nonneg (zero_le_one.trans hR) _))
          (fun j _ x _ ↦ hglobal R hR j x)
      _ ≤ ∑ j ∈ Finset.range (r+1), A j*R^r := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hR (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (hA j)
      _ = C r*R^r := by simp only [C,Finset.sum_mul]

end JanetCartan.BallSmoothing
