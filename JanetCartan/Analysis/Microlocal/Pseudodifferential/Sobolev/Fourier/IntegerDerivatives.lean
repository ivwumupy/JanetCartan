module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives.Basic

/-!
# Integer Sobolev membership and actual distributional derivatives

At every natural order, Euclidean Fourier Sobolev membership is equivalent to
existence of a finite family of actual L² representatives of all ordered
coordinate derivatives through that order. This supplies the integer-order norm
comparison in `app:ch_regular_base:eq:graph-derivative-transfer` and
`app:ch_regular_base:eq:fio-input`.

Writing `A` for the sum of the actual derivative L² norms, we prove
`‖u‖_{Hⁿ} ≤ 2ⁿ A` and `A ≤ (1 + 2πd)ⁿ ‖u‖_{Hⁿ}`. The constants depend only
on dimension and order. Both are positive, the `2π` convention is retained,
and neither order zero nor dimension zero is excluded.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.Pseudodifferential

variable {d n : ℕ}

/-- Integer Sobolev membership constructs all actual L² coordinate derivatives,
for the finite derivative transfer in
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem MemFourierSobolev.exists_integerDerivatives
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2} (hu : MemFourierSobolev (n : ℝ) u) :
    ∃ v : EuclideanL2DerivativeFamily d n, HasEuclideanL2Derivatives n u v := by
  induction n generalizing u with
  | zero => exact ⟨fun _ => u, rfl⟩
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one] at hu
    obtain ⟨v, hv⟩ := hu.exists_coordinateDerivatives (by positivity)
    choose w hw using fun i => ih (hv i).2
    let f : EuclideanL2DerivativeFamily d (n + 1) := fun x =>
      match x with
      | none => u
      | some (i, j) => w i j
    refine ⟨f, rfl, fun i => ?_⟩
    change HasEuclideanL2CoordinateDerivative i u (w i (.empty d n)) ∧
      HasEuclideanL2Derivatives n (w i (.empty d n)) (w i)
    rw [(hw i).root]
    exact ⟨(hv i).1, hw i⟩

/-- Existence of the finite actual derivative family establishes integer Sobolev
membership. In particular membership is a conclusion, as required for
`app:ch_regular_base:eq:fio-input`. -/
theorem HasEuclideanL2Derivatives.memFourierSobolev
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : EuclideanL2DerivativeFamily d n} (h : HasEuclideanL2Derivatives n u v) :
    MemFourierSobolev (n : ℝ) u := by
  induction n generalizing u with
  | zero => simpa only [Nat.cast_zero] using memFourierSobolev_zero u
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    exact (ih h.truncate).of_coordinateDerivatives (by positivity)
      (fun i => ih (h.2 i).2) (fun i => (h.2 i).1)

/-- Both membership directions at each natural order, including zero, for
`app:ch_regular_base:eq:graph-derivative-transfer`. The family consists of actual
scalar Euclidean L² classes and includes `u` at the empty word. -/
theorem memFourierSobolev_nat_iff_exists_integerDerivatives
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    MemFourierSobolev (n : ℝ) u ↔
      ∃ v : EuclideanL2DerivativeFamily d n, HasEuclideanL2Derivatives n u v :=
  ⟨MemFourierSobolev.exists_integerDerivatives, fun ⟨_, hv⟩ => hv.memFourierSobolev⟩

/-- The actual finite derivative aggregate bounds the Sobolev norm, with an
explicit positive constant, for `app:ch_regular_base:eq:fio-input`. Membership
need not be assumed: it follows from the derivative family. -/
theorem HasEuclideanL2Derivatives.fourierSobolevNorm_le
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : EuclideanL2DerivativeFamily d n} (h : HasEuclideanL2Derivatives n u v) :
    fourierSobolevNorm (n : ℝ) u ≤ (2 : ℝ) ^ n * euclideanL2DerivativeNormSum v := by
  induction n generalizing u with
  | zero =>
    change v () = u at h
    simpa only [Nat.cast_zero, fourierSobolevNorm_zero, pow_zero, one_mul,
      euclideanL2DerivativeNormSum, h] using le_refl ‖u‖
  | succ n ih =>
    have hbase := ih h.truncate
    have hbranch := fun i => ih (h.2 i).2
    have hsum : (∑ i : Fin d, euclideanL2DerivativeNormSum (fun w => v (some (i, w)))) ≤
        euclideanL2DerivativeNormSum v :=
      le_add_of_nonneg_left (norm_nonneg _)
    rw [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ fourierSobolevNorm (n : ℝ) u +
          ∑ i : Fin d, fourierSobolevNorm (n : ℝ) (v (some (i, .empty d n))) :=
        fourierSobolevNorm_le_coordinateDerivatives (by positivity)
          h.truncate.memFourierSobolev (fun i => (h.2 i).2.memFourierSobolev)
          (fun i => (h.2 i).1)
      _ ≤ (2 : ℝ) ^ n * euclideanL2DerivativeNormSum v +
          ∑ i : Fin d, (2 : ℝ) ^ n *
            euclideanL2DerivativeNormSum (fun w => v (some (i, w))) :=
        add_le_add (hbase.trans (mul_le_mul_of_nonneg_left
          (euclideanL2DerivativeNormSum_truncate_le v) (by positivity)))
          (Finset.sum_le_sum (fun i _ => hbranch i))
      _ ≤ (2 : ℝ) ^ n * euclideanL2DerivativeNormSum v +
          (2 : ℝ) ^ n * euclideanL2DerivativeNormSum v := by
        rw [← Finset.mul_sum]
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2 : ℝ) ^ (n + 1) * euclideanL2DerivativeNormSum v := by rw [pow_succ]; ring

/-- The sum of actual derivative L² norms is bounded by the integer Sobolev norm
with the explicit `2π` dimension constant, for
`app:ch_regular_base:eq:graph-derivative-transfer` and `app:ch_regular_base:eq:fio-input`. -/
theorem HasEuclideanL2Derivatives.normSum_le_fourierSobolevNorm
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : EuclideanL2DerivativeFamily d n} (h : HasEuclideanL2Derivatives n u v) :
    euclideanL2DerivativeNormSum v ≤
      (1 + 2 * Real.pi * d) ^ n * fourierSobolevNorm (n : ℝ) u := by
  induction n generalizing u with
  | zero =>
    change v () = u at h
    simpa only [Nat.cast_zero, fourierSobolevNorm_zero, pow_zero, one_mul,
      euclideanL2DerivativeNormSum, h] using le_refl ‖u‖
  | succ n ih =>
    have hC : (1 : ℝ) ≤ (1 + 2 * Real.pi * d) ^ n :=
      one_le_pow₀ (le_add_of_nonneg_right (by positivity))
    have hroot : ‖u‖ ≤ (1 + 2 * Real.pi * d) ^ n * fourierSobolevNorm (n : ℝ) u :=
      (norm_le_fourierSobolevNorm (by positivity) h.truncate.memFourierSobolev).trans
        (le_mul_of_one_le_left (fourierSobolevNorm_nonneg _ _) hC)
    have hu : MemFourierSobolev ((n : ℝ) + 1) u := by
      simpa only [Nat.cast_add, Nat.cast_one] using h.memFourierSobolev
    calc
      _ = ‖u‖ + ∑ i : Fin d, euclideanL2DerivativeNormSum (fun w => v (some (i, w))) := by
        rw [euclideanL2DerivativeNormSum, h.1]
      _ ≤ (1 + 2 * Real.pi * d) ^ n * fourierSobolevNorm (n : ℝ) u +
          ∑ i : Fin d, (1 + 2 * Real.pi * d) ^ n *
            fourierSobolevNorm (n : ℝ) (v (some (i, .empty d n))) :=
        add_le_add hroot (Finset.sum_le_sum (fun i _ => ih (h.2 i).2))
      _ = (1 + 2 * Real.pi * d) ^ n * (fourierSobolevNorm (n : ℝ) u +
          ∑ i : Fin d, fourierSobolevNorm (n : ℝ) (v (some (i, .empty d n)))) := by
        rw [mul_add, Finset.mul_sum]
      _ ≤ (1 + 2 * Real.pi * d) ^ n *
          ((1 + 2 * Real.pi * d) * fourierSobolevNorm ((n : ℝ) + 1) u) :=
        mul_le_mul_of_nonneg_left
          (fourierSobolevNorm_coordinateDerivatives_le (by positivity) hu (fun i => (h.2 i).1))
          (by positivity)
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, pow_succ]; ring

/-- The explicit finite constants in the integer derivative comparison are
positive, including in dimension zero, for `app:ch_regular_base:eq:fio-input`. -/
theorem integerDerivative_norm_constants_pos (d n : ℕ) :
    0 < (2 : ℝ) ^ n ∧ 0 < (1 + 2 * Real.pi * d) ^ n := by
  constructor <;> positivity

/-- Quantitative integer derivative characterization constructed from Sobolev
membership alone, for `app:ch_regular_base:eq:fio-input`. Every entry is an actual
L² derivative, the empty entry is `u`, and both constants are explicit. -/
theorem MemFourierSobolev.exists_integerDerivatives_norm_bounds
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2} (hu : MemFourierSobolev (n : ℝ) u) :
    ∃ v : EuclideanL2DerivativeFamily d n,
      HasEuclideanL2Derivatives n u v ∧ v (.empty d n) = u ∧
      fourierSobolevNorm (n : ℝ) u ≤ (2 : ℝ) ^ n * euclideanL2DerivativeNormSum v ∧
      euclideanL2DerivativeNormSum v ≤
        (1 + 2 * Real.pi * d) ^ n * fourierSobolevNorm (n : ℝ) u := by
  obtain ⟨v, hv⟩ := hu.exists_integerDerivatives
  exact ⟨v, hv, hv.root, hv.fourierSobolevNorm_le, hv.normSum_le_fourierSobolevNorm⟩

end JanetCartan.Pseudodifferential
