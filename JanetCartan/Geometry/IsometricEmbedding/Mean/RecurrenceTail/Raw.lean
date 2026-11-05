module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse
public import JanetCartan.Analysis.Iteration.MeanRecurrence

/-!
# Applying the literal raw cutoff to the fixed inverse

`main:eq:linear-two-errors` and the one-high estimate used in
`main:lem:mean-recurrence`. Carrier inputs retain Lebesgue initial variables;
both auxiliary channels retain the periodic real L² model. The raw energy
comparison, convergence, adjoint profile and inverse regularity are explicit
producer obligations. No output projection or replacement inverse is used.
-/

@[expose] public noncomputable section
namespace JanetCartan.RecurrenceTail
open MeasureTheory ContinuumRow RawCutoffBounds
open scoped ENNReal

variable {n : ℕ} {ι Y : Type*} [Fintype ι]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- `main:eq:linear-two-errors`: the reference error is bounded by the
actual squared raw multiplier tail on all channels of the fixed row. -/
theorem reference_error_le_raw_energy (A : AugmentedInput n ι →L[ℝ] Y)
    {c K : ℝ} (hc : 0 < c) (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2)
    (hK : 1 ≤ K) (S : ℕ) (m : ι → Lp ℝ ∞ (carrierMeasure n)) (r : Y)
    (hm : ∀ a, ∀ᵐ x ∂carrierMeasure n, m a x ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ a, ∀ᵐ x ∂carrierMeasure n,
      (CoerciveInverse.rightInverse A r).fst.snd a x ≠ 0 → ‖x.2‖ ≤ K → m a x = 1)
    (w : ι → CarrierVariable n → ℝ)
    (hh : RawWeightedMem S w (CoerciveInverse.rightInverse A r))
    (hweight : ∀ a, ∀ᵐ x ∂carrierMeasure n,
      Real.sqrt (1 + ‖x.2‖ ^ 2) ^ S ≤ w a x) :
    ‖r - A (rawSquaredCutoff K m (A.adjoint ((CoerciveInverse.normalOperator A).inverse r)))‖ ≤
      ‖A‖ * K ^ (-(S : ℝ)) * rawWeightedNorm S w (CoerciveInverse.rightInverse A r) hh := by
  have hid := MeanRecurrence.reference_error_eq_raw_tail A.toLinearMap A.adjoint.toLinearMap
    (CoerciveInverse.normalOperator A).inverse.toLinearMap
    (rawSquaredCutoffCLM hK m).toLinearMap r (CoerciveInverse.apply_rightInverse A hc hgap r)
  change r - A (rawSquaredCutoff K m (CoerciveInverse.rightInverse A r)) =
    A (CoerciveInverse.rightInverse A r - rawSquaredCutoff K m (CoerciveInverse.rightInverse A r)) at hid
  change ‖r - A (rawSquaredCutoff K m (CoerciveInverse.rightInverse A r))‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖A‖ * ‖CoerciveInverse.rightInverse A r -
        rawSquaredCutoff K m (CoerciveInverse.rightInverse A r)‖ := A.le_opNorm _
    _ ≤ ‖A‖ * (K ^ (-(S : ℝ)) * rawWeightedNorm S w (CoerciveInverse.rightInverse A r) hh) :=
      mul_le_mul_of_nonneg_left (rawSquaredCutoff_tail hK S m _ hm hone w hh hweight) (norm_nonneg _)
    _ = _ := by ring

/-- `main:lem:mean-recurrence`: compose the actual multiplier estimate with
`ContinuumInverse.rightInverse_gradeNorm_le`. The same normal inverse appears
in the reference error, its Sobolev estimate, and the raw-adjoint argument.
`henergy` compares the explicitly convergent raw energy with the actual `X^S`
scale; it does not assume a tail or residual bound. -/
theorem reference_error_le_one_high (G : GradedScale Y)
    (R : GradedScale (AugmentedInput n ι)) (A : AugmentedInput n ι →L[ℝ] Y)
    {c K : ℝ} (hc : 0 < c) (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2)
    (hK : 1 ≤ K) (S : ℕ) (m : ι → Lp ℝ ∞ (carrierMeasure n)) (r : Y)
    (hm : ∀ a, ∀ᵐ x ∂carrierMeasure n, m a x ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ a, ∀ᵐ x ∂carrierMeasure n,
      (CoerciveInverse.rightInverse A r).fst.snd a x ≠ 0 → ‖x.2‖ ≤ K → m a x = 1)
    (w : ι → CarrierVariable n → ℝ)
    (hh : RawWeightedMem S w (CoerciveInverse.rightInverse A r))
    (hweight : ∀ a, ∀ᵐ x ∂carrierMeasure n,
      Real.sqrt (1 + ‖x.2‖ ^ 2) ^ S ≤ w a x)
    (henergy : rawWeightedNorm S w (CoerciveInverse.rightInverse A r) hh ≤
      R.gradeNorm S (CoerciveInverse.rightInverse A r))
    {d k T : ℝ} (hk : 0 ≤ k) (hT : 0 ≤ T)
    (hinvmem : (CoerciveInverse.normalOperator A).inverse r ∈ G.level S)
    (hinv : G.gradeNorm S ((CoerciveInverse.normalOperator A).inverse r) ≤
      d * (G.gradeNorm S r + T ^ S * ‖r‖))
    (hraw : ∀ v, v ∈ G.level S →
      R.gradeNorm S (A.adjoint v) ≤ k * (G.gradeNorm S v + T ^ S * ‖v‖)) :
    ‖r - A (rawSquaredCutoff K m (A.adjoint ((CoerciveInverse.normalOperator A).inverse r)))‖ ≤
      (‖A‖ * (k * (d + c⁻¹))) * K ^ (-(S : ℝ)) *
        (G.gradeNorm S r + T ^ S * ‖r‖) := by
  have hright := ContinuumInverse.rightInverse_gradeNorm_le G R A hc hgap hk
    (pow_nonneg hT S) hinvmem hinv hraw
  calc
    _ ≤ ‖A‖ * K ^ (-(S : ℝ)) * rawWeightedNorm S w (CoerciveInverse.rightInverse A r) hh :=
      reference_error_le_raw_energy A hc hgap hK S m r hm hone w hh hweight
    _ ≤ ‖A‖ * K ^ (-(S : ℝ)) *
        (k * (d + c⁻¹) * (G.gradeNorm S r + T ^ S * ‖r‖)) :=
      mul_le_mul_of_nonneg_left (henergy.trans hright)
        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by linarith) _))
    _ = _ := by ring

end JanetCartan.RecurrenceTail
