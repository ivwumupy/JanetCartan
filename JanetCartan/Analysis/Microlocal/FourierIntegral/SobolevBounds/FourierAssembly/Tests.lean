module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Coordinates
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Interpolation

/-!
# Fourier estimates for the actual compact graph tests

The datum-word estimate and weighted Young inequality used after
`app:ch_regular_base:eq:graph-derivative-transfer`. All measures remain Euclidean
Lebesgue measures and every coordinate derivative retains its `2π` factor.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv JanetCartan.Pseudodifferential
open scoped SchwartzMap
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- The actual compact smooth tests have every Fourier order, as used for
interpolation in `app:ch_regular_base:eq:fio-input`. -/
theorem graphTest_memVectorFourierSobolev (s : ℝ) (u : graphTestSpace n r) :
    MemVectorFourierSobolev s (graphTestToLp u) := by
  intro a
  let f := (u.property.2.toSchwartzMap u.property.1).postcompCLM
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) a)
  have he : finiteL2CoordinateIsometry volume (graphTestToLp u) a = f.toLp 2 volume := by
    apply Lp.ext
    filter_upwards [finiteL2Coordinates_apply_ae volume (graphTestToLp u) a,
      (graphTest_memLp u).coeFn_toLp, f.coeFn_toLp 2 volume] with x hx hy hz
    exact hx.trans ((congrArg (fun z : V ↦ z a) hy).trans hz.symm)
  rw [he]
  exact memFourierSobolev_schwartz s f

/-- Classical test differentiation represents the actual vector distributional
coordinate derivative in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphTestToLp_partialDeriv (u : graphTestSpace n r) (i : Fin n) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ))
        (graphTestToLp u : 𝓢'(E, V)) =
      (graphTestToLp (graphTestPartialDeriv i u) : 𝓢'(E, V)) := by
  let f := u.property.2.toSchwartzMap u.property.1
  have he : graphTestToLp u = f.toLp 2 volume := rfl
  have he' : graphTestToLp (graphTestPartialDeriv i u) =
      (lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f).toLp 2 volume := by
    apply Lp.ext
    filter_upwards [(graphTest_memLp (graphTestPartialDeriv i u)).coeFn_toLp,
      (lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f).coeFn_toLp 2 volume] with x hx hy
    exact hx.trans hy.symm
  rw [he, he', Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq f _

/-- Each scalar coordinate of a datum word costs `(2π)^k` Fourier derivatives.
Consumed by the weighted branch summation for `app:ch_regular_base:eq:fio-input`. -/
theorem graphTest_coordinate_word_bound (u : graphTestSpace n r)
    (is : List (Fin n)) (a : Fin r) (t : ℝ) (ht : 0 ≤ t) :
    fourierSobolevNorm t (finiteL2CoordinateIsometry volume
      (graphTestToLp (orderedTransferAction graphTestPartialDeriv is u)) a) ≤
      (2 * Real.pi) ^ is.length * fourierSobolevNorm (t + is.length)
        (finiteL2CoordinateIsometry volume (graphTestToLp u) a) := by
  induction is generalizing t with
  | nil => simp [orderedTransferAction]
  | cons i is ih =>
    have hd := graphL2_coordinate_derivative
      (graphTestToLp_partialDeriv (orderedTransferAction graphTestPartialDeriv is u) i) a
    have hm := graphTest_memVectorFourierSobolev (t + 1)
      (orderedTransferAction graphTestPartialDeriv is u) a
    calc
      _ ≤ (2 * Real.pi) * fourierSobolevNorm (t + 1)
          (finiteL2CoordinateIsometry volume
            (graphTestToLp (orderedTransferAction graphTestPartialDeriv is u)) a) :=
        hd.fourierSobolevNorm_le ht hm
      _ ≤ (2 * Real.pi) * ((2 * Real.pi) ^ is.length *
          fourierSobolevNorm (t + 1 + is.length)
            (finiteL2CoordinateIsometry volume (graphTestToLp u) a)) :=
        mul_le_mul_of_nonneg_left (ih (t + 1) (by linarith)) (by positivity)
      _ = _ := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, pow_succ]
        rw [show t + 1 + (is.length : ℝ) = t + (is.length + 1) by ring]
        ring

/-- Weighted datum words collapse to the single tame input envelope, exactly
as in Step 3 following `app:ch_regular_base:eq:graph-derivative-transfer`.
The constant depends on the fixed order and fiber dimension only. -/
theorem graphTest_weighted_word_bound (s : ℕ) (u : graphTestSpace n r)
    (is : List (Fin n)) (his : is.length ≤ s) (Hhigh : ℝ) (hH : 0 ≤ Hhigh) :
    Hhigh ^ (1 - (is.length : ℝ) / s) *
        ‖graphTestToLp (orderedTransferAction graphTestPartialDeriv is u)‖ ≤
      ((r : ℝ) * (2 * Real.pi) ^ s) *
        (vectorFourierSobolevNorm (s : ℝ) (graphTestToLp u) + Hhigh * ‖graphTestToLp u‖) := by
  let f := finiteL2CoordinateIsometry volume (graphTestToLp u)
  have hc (a : Fin r) : Hhigh ^ (1 - (is.length : ℝ) / s) *
      ‖finiteL2CoordinateIsometry volume
        (graphTestToLp (orderedTransferAction graphTestPartialDeriv is u)) a‖ ≤
      (2 * Real.pi) ^ s *
        (vectorFourierSobolevNorm (s : ℝ) (graphTestToLp u) + Hhigh * ‖graphTestToLp u‖) := by
    have hword := graphTest_coordinate_word_bound u is a 0 le_rfl
    simp only [fourierSobolevNorm_zero, zero_add] at hword
    have hp : (2 * Real.pi) ^ is.length ≤ (2 * Real.pi) ^ s :=
      pow_le_pow_right₀ (by linarith [Real.two_le_pi]) his
    calc
      _ ≤ Hhigh ^ (1 - (is.length : ℝ) / s) *
          ((2 * Real.pi) ^ s * fourierSobolevNorm (is.length : ℝ) (f a)) :=
        mul_le_mul_of_nonneg_left (hword.trans (mul_le_mul_of_nonneg_right hp
          (fourierSobolevNorm_nonneg _ _))) (Real.rpow_nonneg hH _)
      _ = (2 * Real.pi) ^ s * (Hhigh ^ (1 - (is.length : ℝ) / s) *
          fourierSobolevNorm (is.length : ℝ) (f a)) := by ring
      _ ≤ (2 * Real.pi) ^ s * (Hhigh * ‖f a‖ + fourierSobolevNorm (s : ℝ) (f a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [fourierSobolevNorm_zero] using
          fourierSobolevNorm_weighted_interpolate (s := (s : ℝ)) (k := (is.length : ℝ))
            (Nat.cast_nonneg _) (by exact_mod_cast his) hH
            (graphTest_memVectorFourierSobolev (s : ℝ) u a)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [add_comm]
        exact add_le_add (fourierSobolevNorm_coordinate_le _ _ a)
          (mul_le_mul_of_nonneg_left (by simpa [f] using PiLp.norm_apply_le f a) hH)
  calc
    _ ≤ Hhigh ^ (1 - (is.length : ℝ) / s) *
        ∑ a, ‖finiteL2CoordinateIsometry volume
          (graphTestToLp (orderedTransferAction graphTestPartialDeriv is u)) a‖ := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hH _)
      simpa using matrixFourierSobolevNorm_le_sum 0 (finiteL2CoordinateIsometry volume
        (graphTestToLp (orderedTransferAction graphTestPartialDeriv is u)))
    _ ≤ ∑ _a : Fin r, (2 * Real.pi) ^ s *
        (vectorFourierSobolevNorm (s : ℝ) (graphTestToLp u) + Hhigh * ‖graphTestToLp u‖) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a _ ↦ hc a)
    _ = _ := by simp [mul_assoc]

end JanetCartan.FourierIntegral
