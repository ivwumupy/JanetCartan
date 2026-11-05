module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Normal
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Interpolation

/-!
# Reducing the image commutator estimate to its finite branches

The recursive commutator contains at most `s+1` branches. This file proves the
norm summation and density step independently of the quantitative branch
producer, for `app:ch_background:eq:bg-commutator`.

`WeightedEstimates.exists_primitive_branch_bound` bounds the constructed first
coefficient derivative on lower derivatives of the same datum from primitive
jets, using the allocated multiplier bounds and weighted interpolation.
`TameEstimates` applies that producer and the summation/density lemmas here
to the actual normal, discharging the branch-bound premise.
-/

public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential
namespace ImageFactorExpression

open PeriodicSobolevSpace ContinuumRow

variable {n : ℕ} {ι : Type*}
variable (q : ι → C(Torus n, ℝ)) (hq : ∀ a, IsSmoothPeriodic (q a))

private theorem norm_reverseDerivativeToL2_le (s : ℕ) (is : List (Fin n))
    (hlen : is.length ≤ s) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖Exterior.reverseDerivativeToL2 s is hlen u‖ ≤ ‖u‖ := by
  simpa only [Exterior.derivativeToL2, List.reverse_reverse] using
    HigherRegularity.norm_derivativeToL2_le s is.reverse (by simpa using hlen) u

/-- The finite recursion costs at most `t+1` copies of a common branch bound.
The branch keeps the original coefficient expression and the exact lower
derivative of the datum (`app:ch_background:eq:bg-commutator`). This is a
pure summation lemma; primitive coefficient estimates must supply `hbranch`. -/
theorem norm_reverseCommutator_of_branch_bounds (e : ImageFactorExpression n ι)
    (s : ℕ) (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f)
    {M : ℝ} (hM : 0 ≤ M)
    (hbranch : ∀ (t : ℕ) (js : List (Fin n)), t + js.length ≤ s → ∀ i : Fin n,
      ‖(e.coefficientDerivative i).onSobolev q hq t
        (ofSmooth t (periodicCoordinateDerivList js f) (hf.coordinateDerivList js))‖ ≤ M)
    (t : ℕ) (is : List (Fin n)) (hlen : is.length ≤ t + 1)
    (js : List (Fin n)) (hcount : t + js.length ≤ s) :
    ‖e.reverseCommutator q hq t is hlen
      (ofSmooth t (periodicCoordinateDerivList js f) (hf.coordinateDerivList js))‖ ≤
        (t + 1) * M := by
  induction t generalizing is js with
  | zero =>
    cases is with
    | nil => simpa only [reverseCommutator, zero_apply, norm_zero, Nat.cast_zero,
        zero_add, one_mul] using hM
    | cons i is =>
      simp only [reverseCommutator, ContinuousLinearMap.comp_apply, Nat.cast_zero,
        zero_add, one_mul]
      exact (norm_toL2_le 0 _).trans (hbranch 0 js hcount i)
  | succ t ih =>
    cases is with
    | nil =>
      simp only [reverseCommutator, zero_apply, norm_zero]
      positivity
    | cons i is =>
      simp only [reverseCommutator, add_apply, ContinuousLinearMap.comp_apply,
        coordinateDerivative_ofSmooth]
      have h₁ := ih is (by simpa using hlen) (i :: js) (by simp only [List.length_cons]; omega)
      have h₂ := (norm_reverseDerivativeToL2_le (t + 1) is (by simpa using hlen)
        ((e.coefficientDerivative i).onSobolev q hq (t + 1)
          (ofSmooth (t + 1) (periodicCoordinateDerivList js f)
            (hf.coordinateDerivList js)))).trans (hbranch (t + 1) js hcount i)
      calc
        _ ≤ _ + _ := norm_add_le _ _
        _ ≤ (t + 1) * M + M := add_le_add h₁ h₂
        _ = _ := by push_cast; ring

/-- The exact ordered commutator inherits the common finite-branch bound
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_commutator_of_branch_bounds (e : ImageFactorExpression n ι)
    (s : ℕ) (is : List (Fin n)) (hlen : is.length ≤ s + 1)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f)
    {M : ℝ} (hM : 0 ≤ M)
    (hbranch : ∀ (t : ℕ) (js : List (Fin n)), t + js.length ≤ s → ∀ i : Fin n,
      ‖(e.coefficientDerivative i).onSobolev q hq t
        (ofSmooth t (periodicCoordinateDerivList js f) (hf.coordinateDerivList js))‖ ≤ M) :
    ‖e.commutator q hq s is hlen (ofSmooth s f hf)‖ ≤ (s + 1) * M := by
  simpa only [commutator, periodicCoordinateDerivList] using
    e.norm_reverseCommutator_of_branch_bounds q hq s f hf hM hbranch s is.reverse
      (by simpa using hlen) [] (by simp)

/-- Smooth density transfers a uniform single-high branch bound to every
Sobolev datum for the already constructed commutator. The branch producer
still owes `hbranch` from primitive jets of the same coefficients; this
conditional summation step is not the image-normal tame theorem
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_commutator_le_of_smooth_branch_bound (e : ImageFactorExpression n ι)
    (s : ℕ) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hbranch : ∀ (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f)
      (t : ℕ) (js : List (Fin n)), t + js.length ≤ s → ∀ i : Fin n,
      ‖(e.coefficientDerivative i).onSobolev q hq t
        (ofSmooth t (periodicCoordinateDerivList js f) (hf.coordinateDerivList js))‖ ≤
          C * (‖ofSmooth s f hf‖ + (1 + H) * ‖toL2 s (ofSmooth s f hf)‖))
    (is : List (Fin n)) (hlen : is.length ≤ s + 1)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖e.commutator q hq s is hlen u‖ ≤
      ((s + 1) * C) * (‖u‖ + (1 + H) * ‖toL2 s u‖) := by
  refine (denseRange_ofSmooth (n := n) (F := Euclidean n) s).induction_on u ?_ ?_
  · exact isClosed_le (e.commutator q hq s is hlen).continuous.norm
      (continuous_const.mul (continuous_norm.add
        (continuous_const.mul (toL2 s).continuous.norm)))
  · rintro ⟨f, hf⟩
    simpa only [mul_assoc] using e.norm_commutator_of_branch_bounds q hq s is hlen
      f hf (show 0 ≤ C * (‖ofSmooth s f hf‖ +
        (1 + H) * ‖toL2 s (ofSmooth s f hf)‖) by positivity) (hbranch f hf)

end ImageFactorExpression
end JanetCartan.ContinuumCommutator.ImageChannel.Differential
