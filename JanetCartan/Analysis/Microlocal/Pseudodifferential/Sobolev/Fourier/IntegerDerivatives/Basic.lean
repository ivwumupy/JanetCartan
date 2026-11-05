module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.FirstDerivatives

/-!
# Finite families of distributional coordinate derivatives

For `app:ch_regular_base:eq:graph-derivative-transfer`, a recursive finite index
lists every ordered coordinate word of length at most `n`, exactly once.
The empty word has the original L² class. Each branch starts with one actual
distributional derivative and contains all its derivatives through order `n - 1`.
No Sobolev membership or norm estimate is included in the derivative predicate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap LineDeriv

namespace JanetCartan.Pseudodifferential

/-- Ordered coordinate words of length at most `n`, for
`app:ch_regular_base:eq:graph-derivative-transfer`. `none` is the empty word;
`some (i, w)` first differentiates in coordinate `i`, then follows `w`. -/
def EuclideanDerivativeIndex (d : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => Option (Fin d × EuclideanDerivativeIndex d n)

/-- Finiteness of the words summed in `app:ch_regular_base:eq:fio-input`. -/
instance (d : ℕ) : (n : ℕ) → Fintype (EuclideanDerivativeIndex d n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
    letI := instFintypeEuclideanDerivativeIndex d n
    inferInstanceAs (Fintype (Option (Fin d × EuclideanDerivativeIndex d n)))

/-- The order-zero word for `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def EuclideanDerivativeIndex.empty (d : ℕ) : (n : ℕ) → EuclideanDerivativeIndex d n
  | 0 => ()
  | _ + 1 => none

/-- Inclusion of words through order `n` into those through order `n + 1`,
used to lower the derivative budget in `app:ch_regular_base:eq:fio-input`. -/
def EuclideanDerivativeIndex.raise {d : ℕ} :
    {n : ℕ} → EuclideanDerivativeIndex d n → EuclideanDerivativeIndex d (n + 1)
  | 0, _ => none
  | _ + 1, none => none
  | _ + 1, some (i, w) => some (i, w.raise)

/-- Truncation preserves order zero in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
@[simp] theorem EuclideanDerivativeIndex.raise_empty (d n : ℕ) :
    (empty d n).raise = empty d (n + 1) := by cases n <;> rfl

/-- A finite family of actual scalar Euclidean L² classes, indexed by all
coordinate words through order `n`, for `app:ch_regular_base:eq:fio-input`. -/
abbrev EuclideanL2DerivativeFamily (d n : ℕ) :=
  EuclideanDerivativeIndex d n → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2

/-- Distributional compatibility of the finite derivative family used in
`app:ch_regular_base:eq:graph-derivative-transfer`. The root is literally `u`;
every branch is a family for an actual coordinate derivative of `u`. -/
def HasEuclideanL2Derivatives {d : ℕ} : (n : ℕ) →
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 → EuclideanL2DerivativeFamily d n → Prop
  | 0, u, v => v () = u
  | n + 1, u, v => v none = u ∧ ∀ i : Fin d,
      HasEuclideanL2CoordinateDerivative i u (v (some (i, .empty d n))) ∧
      HasEuclideanL2Derivatives n (v (some (i, .empty d n))) (fun w => v (some (i, w)))

/-- Sum of the actual L² norms of every derivative through order `n`, for
`app:ch_regular_base:eq:fio-input`. -/
def euclideanL2DerivativeNormSum {d : ℕ} : {n : ℕ} → EuclideanL2DerivativeFamily d n → ℝ
  | 0, v => ‖v ()‖
  | _ + 1, v => ‖v none‖ + ∑ i : Fin d, euclideanL2DerivativeNormSum (fun w => v (some (i, w)))

variable {d n : ℕ}

/-- The recursive aggregate is the ordinary finite sum of the actual L² norms,
for `app:ch_regular_base:eq:fio-input`. -/
theorem euclideanL2DerivativeNormSum_eq_sum (v : EuclideanL2DerivativeFamily d n) :
    euclideanL2DerivativeNormSum v = ∑ w, ‖v w‖ := by
  induction n with
  | zero =>
    change ‖v ()‖ = ∑ w : Unit, ‖v w‖
    simp
  | succ n ih =>
    simp only [euclideanL2DerivativeNormSum, ih]
    change _ = ∑ w : Option (Fin d × EuclideanDerivativeIndex d n), ‖v w‖
    rw [Fintype.sum_option, Fintype.sum_prod_type]

/-- Nonnegativity of the derivative aggregate in `app:ch_regular_base:eq:fio-input`. -/
theorem euclideanL2DerivativeNormSum_nonneg (v : EuclideanL2DerivativeFamily d n) :
    0 ≤ euclideanL2DerivativeNormSum v := by
  rw [euclideanL2DerivativeNormSum_eq_sum]
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- The order-zero representative is the input itself, for
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem HasEuclideanL2Derivatives.root
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : EuclideanL2DerivativeFamily d n} (h : HasEuclideanL2Derivatives n u v) :
    v (.empty d n) = u := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

/-- Truncating an actual derivative family preserves compatibility, as required
by the induction for `app:ch_regular_base:eq:fio-input`. -/
theorem HasEuclideanL2Derivatives.truncate
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : EuclideanL2DerivativeFamily d (n + 1)} (h : HasEuclideanL2Derivatives (n + 1) u v) :
    HasEuclideanL2Derivatives n u (fun w => v w.raise) := by
  induction n generalizing u with
  | zero => exact h.1
  | succ n ih =>
    refine ⟨h.1, fun i => ?_⟩
    simpa only [EuclideanDerivativeIndex.raise, EuclideanDerivativeIndex.raise_empty] using
      And.intro (h.2 i).1 (ih (h.2 i).2)

/-- Truncation can only decrease the finite derivative aggregate in
`app:ch_regular_base:eq:fio-input`. -/
theorem euclideanL2DerivativeNormSum_truncate_le (v : EuclideanL2DerivativeFamily d (n + 1)) :
    euclideanL2DerivativeNormSum (fun w : EuclideanDerivativeIndex d n => v w.raise) ≤
      euclideanL2DerivativeNormSum v := by
  induction n with
  | zero =>
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ =>
      euclideanL2DerivativeNormSum_nonneg _))
  | succ n ih =>
    apply add_le_add le_rfl
    exact Finset.sum_le_sum (fun i _ => ih (fun w => v (some (i, w))))

/-- Actual iteration of tempered-distribution coordinate derivatives along a
finite word, for `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def euclideanIteratedCoordinateDerivative : {n : ℕ} → EuclideanDerivativeIndex d n →
    𝓢'(EuclideanSpace ℝ (Fin d), ℂ) → 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)
  | 0, _, T => T
  | _ + 1, none, T => T
  | _ + 1, some (i, w), T =>
      euclideanIteratedCoordinateDerivative w (∂_{EuclideanSpace.basisFun (Fin d) ℝ i} T)

/-- Every entry is the corresponding iterated distributional derivative,
not an abstract jet, for `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem HasEuclideanL2Derivatives.toTemperedDistribution
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : EuclideanL2DerivativeFamily d n} (h : HasEuclideanL2Derivatives n u v)
    (w : EuclideanDerivativeIndex d n) :
    euclideanIteratedCoordinateDerivative w (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (v w : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  induction n generalizing u with
  | zero => cases w; exact congrArg (fun f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 =>
      (f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) h.symm
  | succ n ih =>
    cases w with
    | none => exact congrArg (fun f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 =>
        (f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) h.1.symm
    | some p =>
      obtain ⟨i, w⟩ := p
      change euclideanIteratedCoordinateDerivative w (euclideanCoordinateDerivative i u) = _
      rw [(h.2 i).1]
      exact ih (h.2 i).2 w

end JanetCartan.Pseudodifferential
