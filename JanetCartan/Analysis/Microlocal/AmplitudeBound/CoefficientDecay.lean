module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FrequencyLimit
public import JanetCartan.Analysis.Fourier.Periodic.Lattice

/-!
# Summing the two-position coefficient decay

The lattice summation in `app:ch_osc:lem:osc-amplitude`. The decay exponent is
exactly `2(d+1)` in `2d` physical dimensions. Estimates below take the coefficient
decay as an input; deriving it by integration by parts remains separate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound

/-- Bessel weights are summable when their decay exceeds the lattice dimension,
as required in `app:ch_osc:lem:osc-amplitude`. -/
theorem summable_besselWeight {n : ℕ} {s : ℝ} (hs : (n : ℝ) < 2 * s) :
    Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ (-s)) := by
  have hs0 : 0 ≤ s := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  apply (finite_frequencyNorm_le n 1).summable_compl_iff.mp
  apply Summable.of_nonneg_of_le (fun k ↦ Real.rpow_nonneg (by positivity) _)
    (fun k ↦ ?_) ((summable_frequencyNorm_rpow (p := 2 * s) hs).subtype _)
  have hk : 1 < frequencyNorm k.val := by simpa only [Set.mem_compl_iff,
    Set.mem_ofPred_eq, not_le] using k.property
  calc
    (1 + frequencyNorm k.val ^ 2) ^ (-s) ≤ (frequencyNorm k.val ^ 2) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    _ = frequencyNorm k.val ^ (-(2 * s)) := by
      rw [← Real.rpow_natCast_mul (frequencyNorm_nonneg _) 2]
      congr 1
      push_cast
      ring

/-- The physical Fourier decay from `2(d+1)` derivatives in
`app:ch_osc:lem:osc-amplitude`. The two physical frequencies are concatenated. -/
def twoPositionWeight (d : ℕ) (k : Fin (2 * d) → ℤ) : ℝ :=
  (1 + frequencyNorm k ^ 2) ^ (-((d : ℝ) + 1))

/-- Nonnegativity of the summation weight in `app:ch_osc:lem:osc-amplitude`. -/
theorem twoPositionWeight_nonneg (d : ℕ) (k : Fin (2 * d) → ℤ) :
    0 ≤ twoPositionWeight d k := Real.rpow_nonneg (by positivity) _

/-- The manuscript's exact decay exponent is summable in the combined physical
dimension, as used in `app:ch_osc:lem:osc-amplitude`. -/
theorem summable_twoPositionWeight (d : ℕ) : Summable (twoPositionWeight d) := by
  apply summable_besselWeight
  push_cast
  linarith

/-- The dimension-dependent sum in the coefficient estimate of
`app:ch_osc:lem:osc-amplitude`, with the unit-torus `2π` convention. -/
def coefficientSumConstant (d : ℕ) : ℝ := ∑' k, twoPositionWeight d k

/-- The summation constant in `app:ch_osc:lem:osc-amplitude` is nonnegative. -/
theorem coefficientSumConstant_nonneg (d : ℕ) : 0 ≤ coefficientSumConstant d :=
  tsum_nonneg (twoPositionWeight_nonneg d)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The scalar operator-series estimate in `app:ch_osc:lem:osc-amplitude`,
conditional on its stated physical Fourier coefficient decay. The bound is
independent of frequency support. -/
theorem norm_amplitudeOperator_fourierMultiplier_le_of_decay (d : ℕ)
    (L R : (Fin (2 * d) → ℤ) → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (a : (Fin (2 * d) → ℤ) → Lp (α := E) ℂ ∞) (A : ℝ)
    (hL : ∀ k, ‖L k‖ ≤ 1) (hR : ∀ k, ‖R k‖ ≤ 1)
    (ha : ∀ k, ‖a k‖ ≤ A * twoPositionWeight d k) :
    ‖amplitudeOperator L R (fun k ↦ fourierMultiplier (a k))‖ ≤
      coefficientSumConstant d * A := by
  calc
    _ ≤ ∑' k, A * twoPositionWeight d k :=
      norm_amplitudeOperator_fourierMultiplier_le L R a _ hL hR ha
        ((summable_twoPositionWeight d).mul_left A)
    _ = coefficientSumConstant d * A := by rw [tsum_mul_left, mul_comm]; rfl

/-- The finite and compact regularizations of `app:ch_osc:lem:osc-amplitude`
satisfy the same decay-based bound, uniformly in both cutoffs. -/
theorem norm_regularizedAmplitudeOperator_le_of_decay (d : ℕ)
    (L R : (Fin (2 * d) → ℤ) → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (a : (Fin (2 * d) → ℤ) → Lp (α := E) ℂ ∞) (A : ℝ)
    (hL : ∀ k, ‖L k‖ ≤ 1) (hR : ∀ k, ‖R k‖ ≤ 1)
    (ha : ∀ k, ‖a k‖ ≤ A * twoPositionWeight d k)
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ) :
    ‖regularizedAmplitudeOperator (E := E) L R a s ρ‖ ≤ coefficientSumConstant d * A := by
  calc
    _ ≤ ∑' k, A * twoPositionWeight d k :=
      norm_regularizedAmplitudeOperator_le L R a _ hL hR ha
        ((summable_twoPositionWeight d).mul_left A) s ρ
    _ = coefficientSumConstant d * A := by rw [tsum_mul_left, mul_comm]; rfl

/-- The normal-series estimate of `app:ch_osc:eq:two-position-normal-bound`,
conditional on the manuscript's Fourier coefficient decay for `c`. -/
theorem norm_normalAmplitudeOperator_le_of_decay {X H : Type*}
    [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (d : ℕ)
    (L R : (Fin (2 * d) → ℤ) → H →L[ℂ] H) (T : Lp ℂ 2 μ →L[ℂ] H)
    (a : (Fin (2 * d) → ℤ) → Lp ℂ ∞ μ) (g : Lp ℂ ∞ μ) (A : ℝ)
    (hL : ∀ k, ‖L k‖ ≤ 1) (hR : ∀ k, ‖R k‖ ≤ 1)
    (ha : ∀ k, ‖a k‖ ≤ A * twoPositionWeight d k) :
    ‖normalAmplitudeOperator L R T
      (fun k ↦ (multiplicationOperator (a k)).comp (multiplicationOperator g))‖ ≤
      coefficientSumConstant d * A * ‖T‖ ^ 2 * ‖g‖ := by
  calc
    _ ≤ (∑' k, A * twoPositionWeight d k) * ‖T‖ ^ 2 * ‖g‖ :=
      norm_normalAmplitudeOperator_multiplication_le L R T a g _ hL hR ha
        ((summable_twoPositionWeight d).mul_left A)
    _ = _ := by rw [tsum_mul_left, mul_comm A]; rfl

end JanetCartan.AmplitudeBound
