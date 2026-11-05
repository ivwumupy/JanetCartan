module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowSeries.Column

/-!
# The bounded sharp row-amplitude operator

The actual original-input column is composed with the actual Sobolev
diagonal synthesis. This constructs the operator in
`app:ch_osc:eq:amplitude-row` on all of `L²`, and its literal finite mode
regularizations converge in operator norm. Kernel identification is a
separate dense-core deduction from those finite identities; it never
evaluates parameterwise almost-everywhere identities on a diagonal.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.AmplitudeBound.PaperEstimates

open DiagonalTrace

variable {κ X H : Type*} [Countable κ] [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem cancel_sqrt_weight (w : ℝ) (hw : 0 < w) (v : H) :
    (((Real.sqrt w)⁻¹ : ℝ) : ℂ) • ((Real.sqrt w : ℂ) • v) = v := by
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hw),
    Complex.ofReal_one, one_smul]

/-- The actual bounded row multiplier, defined by the same coefficient
inputs, original operator, and physical mode contractions as its finite
kernel regularizations (`app:ch_osc:eq:amplitude-row`). -/
def rowAmplitudeOperator
    (w : κ → ℝ) (hw : ∀ k, 0 < w k) (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H) (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : κ → Lp ℂ ∞ μ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) : Lp ℂ 2 μ →L[ℂ] H :=
  (weightedSynthesis w hw hsum M hM).comp
    (weightedRowColumn w (fun k ↦ (hw k).le) a B hB hrow T)

/-- Evaluation of the bounded row multiplier is the original convergent
mode series (`app:ch_osc:eq:amplitude-row`). -/
theorem rowAmplitudeOperator_apply
    (w : κ → ℝ) (hw : ∀ k, 0 < w k) (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H) (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : κ → Lp ℂ ∞ μ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) (f : Lp ℂ 2 μ) :
    rowAmplitudeOperator w hw hsum M hM a B hB hrow T f =
      ∑' k, M k (T (multiplicationOperator (a k) f)) := by
  simp only [rowAmplitudeOperator, ContinuousLinearMap.comp_apply, weightedSynthesis_apply,
    weightedRowColumn_apply, cancel_sqrt_weight _ (hw _)]

/-- The sharp row norm has only the dimension-dependent diagonal
constant, original operator norm, and original row-energy size
(`app:ch_osc:eq:amplitude-row`). -/
theorem norm_rowAmplitudeOperator_le
    (w : κ → ℝ) (hw : ∀ k, 0 < w k) (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H) (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : κ → Lp ℂ ∞ μ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) :
    ‖rowAmplitudeOperator w hw hsum M hM a B hB hrow T‖ ≤
      Real.sqrt (∑' k, (w k)⁻¹) * ‖T‖ * B := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [mul_assoc] using mul_le_mul
    (norm_weightedSynthesis_le w hw hsum M hM)
    (norm_weightedRowColumn_le w (fun k ↦ (hw k).le) a B hB hrow T)
    (norm_nonneg _) (Real.sqrt_nonneg _)

omit [CompleteSpace H] in
/-- Finite synthesis is exactly the literal finite original row
operator, rather than a new regularization
(`app:ch_osc:eq:amplitude-row`). -/
theorem finiteRowAmplitudeOperator_eq_partial
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (M : κ → H →L[ℂ] H) (a : κ → Lp ℂ ∞ μ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) (s : Finset κ) :
    finiteRowAmplitudeOperator M T a s =
      (weightedSynthesisPartial w M s).comp
        (weightedRowColumn w (fun k ↦ (hw k).le) a B hB hrow T) := by
  ext f
  simp only [finiteRowAmplitudeOperator, sum_apply,
    rowModeOperator, ContinuousLinearMap.comp_apply, weightedSynthesisPartial_apply,
    weightedRowColumn_apply, cancel_sqrt_weight _ (hw _)]

omit [CompleteSpace H] in
/-- Every actual finite row regularization satisfies its finite
inverse-weight bound (`app:ch_osc:eq:amplitude-row`). -/
theorem norm_finiteRowAmplitudeOperator_le
    (w : κ → ℝ) (hw : ∀ k, 0 < w k)
    (M : κ → H →L[ℂ] H) (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : κ → Lp ℂ ∞ μ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) (s : Finset κ) :
    ‖finiteRowAmplitudeOperator M T a s‖ ≤
      Real.sqrt (∑ k ∈ s, (w k)⁻¹) * ‖T‖ * B := by
  rw [finiteRowAmplitudeOperator_eq_partial w hw M a B hB hrow T s]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa only [mul_assoc] using mul_le_mul
    (norm_weightedSynthesisPartial_le w hw M hM s)
    (norm_weightedRowColumn_le w (fun k ↦ (hw k).le) a B hB hrow T)
    (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Actual finite row operators converge in operator norm. In
particular, their strong convergence is available for the literal
kernel limit in `app:ch_osc:eq:amplitude-row`. -/
theorem tendsto_finiteRowAmplitudeOperator
    (w : κ → ℝ) (hw : ∀ k, 0 < w k) (hsum : Summable (fun k ↦ (w k)⁻¹))
    (M : κ → H →L[ℂ] H) (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : κ → Lp ℂ ∞ μ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) :
    Tendsto (finiteRowAmplitudeOperator M T a) atTop
      (𝓝 (rowAmplitudeOperator w hw hsum M hM a B hB hrow T)) := by
  change Tendsto (fun s ↦ finiteRowAmplitudeOperator M T a s) atTop _
  simpa only [Function.comp_def, finiteRowAmplitudeOperator_eq_partial w hw M a B hB hrow T,
    rowAmplitudeOperator] using
    ((show Continuous (fun P : lp (fun _ : κ ↦ H) 2 →L[ℂ] H ↦
      P.comp (weightedRowColumn w (fun k ↦ (hw k).le) a B hB hrow T)) by
        fun_prop).continuousAt.tendsto.comp (tendsto_weightedSynthesisPartial w hw hsum M hM))

end JanetCartan.AmplitudeBound.PaperEstimates
