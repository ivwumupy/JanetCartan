module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Approximation.Taylor
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Averaging the actual finite Taylor cancellation

All integrals use the original fixed nonnegative mass-one kernel. Integrability
is obtained from continuity on its compact support, so no behavior of the input
away from the closed unit ball is required. Averaging the pointwise finite
Taylor cancellation gives the actual unmasked radial combination's error in
`app:ch_regular_base:eq:ball-extension-continuous`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric Finset MeasureTheory Filter
open scoped ContDiff

namespace JanetCartan.BallSmoothing

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The explicit approximation constant depends only on the finite Taylor
order. In particular it is independent of the scale, input, and target Banach
space (`app:ch_regular_base:eq:ball-extension-continuous`). -/
def radialApproximationConstant (m : ℕ) : ℝ :=
  (5/4 : ℝ)^m * ∑ j ∈ Finset.Icc 1 m, |coefficient m j| * (j : ℝ)^m

/-- Nonnegativity of the constant used for the same inward-average operator
(`app:ch_regular_base:eq:ball-extension-continuous`). -/
theorem radialApproximationConstant_nonneg (m : ℕ) : 0 ≤ radialApproximationConstant m := by
  unfold radialApproximationConstant
  exact mul_nonneg (by positivity) (sum_nonneg fun j _ ↦
    mul_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg j) m))

private theorem integrable_kernel_radial_sample
    {R : ℝ} {j : ℕ} (ht0 : 0 ≤ (j : ℝ)/R) (ht1 : (j : ℝ)/R ≤ 1)
    (f : E → F) (hf : ∀ z ∈ closedBall (0 : E) 1, ContDiffAt ℝ ∞ f z)
    {x : E} (hx : x ∈ closedBall 0 1) :
    Integrable (fun y ↦ kernel n y • f (radialPoint R j x y)) := by
  have hfcont : ContinuousOn f (closedBall (0 : E) 1) :=
    fun z hz ↦ (hf z hz).continuousAt.continuousWithinAt
  have hmap : MapsTo (radialPoint R j x) (closedBall 0 (1/4 : ℝ)) (closedBall 0 1) := by
    intro y hy
    have hy1 : y ∈ closedBall (0 : E) 1 := closedBall_subset_closedBall (by norm_num) hy
    exact (convex_closedBall (0 : E) 1) hx hy1 (sub_nonneg.mpr ht1) ht0 (by ring)
  have hc : ContinuousOn (fun y ↦ kernel n y • f (radialPoint R j x y))
      (closedBall (0 : E) (1/4 : ℝ)) :=
    contDiff_kernel.continuous.continuousOn.smul
      (hfcont.comp (by unfold radialPoint; fun_prop) hmap)
  apply (hc.integrableOn_compact (isCompact_closedBall 0 (1/4 : ℝ))).integrable_of_forall_notMem_eq_zero
  intro y hy
  have hnot : y ∉ tsupport (kernel n) := fun ht ↦
    hy (ball_subset_closedBall (tsupport_kernel_subset ht))
  rw [image_eq_zero_of_notMem_tsupport hnot, zero_smul]

/-- The literal finite inward average approximates the original closed-ball
input with exactly `m` input derivatives and the original scale `R⁻¹`.
The finite signs, inward points, and normalized kernel are all the actual
constructions, and the bound is uniform before the input and scale
(`app:ch_regular_base:eq:extension-radial-formula`,
`app:ch_regular_base:eq:ball-extension-continuous`). -/
theorem norm_radialCombination_sub_le [CompleteSpace F]
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    (f : E → F) (hf : ∀ z ∈ closedBall (0 : E) 1, ContDiffAt ℝ ∞ f z)
    {x : E} (hx : x ∈ closedBall 0 1) :
    ‖radialCombination (coefficient m) (kernel n) R m f x - f x‖ ≤
      radialApproximationConstant m * (R⁻¹)^m * cNorm (closedBall 0 1) m f := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m from hm)
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have ht j (hj : j ∈ Finset.Icc 1 m) : 0 ≤ (j : ℝ)/R ∧ (j : ℝ)/R ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hRpos.le, (div_le_iff₀ hRpos).mpr ?_⟩
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    linarith
  have hint j (hj : j ∈ Finset.Icc 1 m) :
      Integrable (fun y ↦ kernel n y • f (radialPoint R j x y)) :=
    integrable_kernel_radial_sample (ht j hj).1 (ht j hj).2 f hf hx
  let sample := fun y ↦ ∑ j ∈ Finset.Icc 1 m, coefficient m j • f (radialPoint R j x y)
  have hpoint (y : E) :
      (∑ j ∈ Finset.Icc 1 m, coefficient m j • (kernel n y • f (radialPoint R j x y))) =
        kernel n y • sample y := by
    dsimp only [sample]
    rw [smul_sum]
    apply sum_congr rfl
    intro j _
    exact smul_comm _ _ _
  have hsumInt : Integrable (fun y ↦ kernel n y • sample y) := by
    have h := integrable_finsetSum (Finset.Icc 1 m) (fun j hj ↦ (hint j hj).smul (coefficient m j))
    simpa only [Pi.smul_apply, hpoint] using h
  have hsumEq : radialCombination (coefficient m) (kernel n) R m f x =
      ∫ y, kernel n y • sample y := by
    calc
      _ = ∑ j ∈ Finset.Icc 1 m, ∫ y, coefficient m j •
          (kernel n y • f (radialPoint R j x y)) := by
        simp only [radialCombination, radialAverage, integral_smul]
      _ = ∫ y, ∑ j ∈ Finset.Icc 1 m, coefficient m j •
          (kernel n y • f (radialPoint R j x y)) :=
        (integral_finsetSum _ (fun j hj ↦ (hint j hj).smul (coefficient m j))).symm
      _ = _ := integral_congr_ae (Eventually.of_forall hpoint)
  have hconst : (∫ y : E, kernel n y • f x) = f x := by
    rw [integral_smul_const, integral_kernel, one_smul]
  have herr : radialCombination (coefficient m) (kernel n) R m f x - f x =
      ∫ y, kernel n y • (sample y - f x) := by
    calc
      _ = (∫ y, kernel n y • sample y) - (∫ y : E, kernel n y • f x) := by
        rw [hsumEq, hconst]
      _ = ∫ y : E, (kernel n y • sample y - kernel n y • f x) :=
        (integral_sub hsumInt (integrable_kernel.smul_const (f x))).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun _ ↦ (smul_sub _ _ _).symm)
  let B := radialApproximationConstant m * (R⁻¹)^m * cNorm (closedBall (0 : E) 1) m f
  have hbound (y : E) : ‖kernel n y • (sample y - f x)‖ ≤ kernel n y * B := by
    rw [norm_smul, Real.norm_of_nonneg (kernel_nonneg y)]
    by_cases hy : y ∈ closedBall (0 : E) (1/4 : ℝ)
    · exact mul_le_mul_of_nonneg_left
        (norm_radial_sample_combination_sub_le hm hR f hf hx hy) (kernel_nonneg y)
    · have hnot : y ∉ tsupport (kernel n) := fun ht ↦
        hy (ball_subset_closedBall (tsupport_kernel_subset ht))
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul, zero_mul]
  rw [herr]
  have h := norm_integral_le_of_norm_le (integrable_kernel.mul_const B) (Eventually.of_forall hbound)
  simpa only [integral_mul_const, integral_kernel, one_mul] using h

end JanetCartan.BallSmoothing
