module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowSeries.Energy
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.DiagonalTrace.Operator

/-!
# The actual weighted input column

The first part of the construction in `app:ch_osc:eq:amplitude-row`
sends the original input to its coefficient-multiplied outputs under
the SAME bounded operator `T`. Its norm follows from the integrated
original row energy. Composing this column with the checked diagonal
synthesis produces the bounded kernel multiplier on all of `L²`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound.PaperEstimates

variable {κ X H : Type*} [Countable κ] [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [NormedSpace ℂ H]

private theorem sqrt_smul_norm_sq (w : ℝ) (hw : 0 ≤ w) (v : H) :
    ‖(Real.sqrt w : ℂ) • v‖ ^ 2 = w * ‖v‖ ^ 2 := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt hw]

private theorem weighted_column_memℓp
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (a : κ → Lp ℂ ∞ μ) (B : ℝ)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) (f : Lp ℂ 2 μ) :
    Memℓp (fun k ↦ (Real.sqrt (w k) : ℂ) • T (multiplicationOperator (a k) f)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sqrt_smul_norm_sq _ (hw _)] using
    (transformed_row_energy w hw a B hrow T f).1

/-- The actual coefficient column in the Sobolev diagonal proof of
`app:ch_osc:eq:amplitude-row`. The input and the original bounded operator
are retained literally in every coordinate. -/
def weightedRowColumn
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (a : κ → Lp ℂ ∞ μ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) : Lp ℂ 2 μ →L[ℂ] lp (fun _ : κ ↦ H) 2 :=
  LinearMap.mkContinuous
    { toFun f := ⟨fun k ↦ (Real.sqrt (w k) : ℂ) • T (multiplicationOperator (a k) f),
        by exact weighted_column_memℓp w hw a B hrow T f⟩
      map_add' f g := by
        apply lp.ext
        funext k
        simp only [map_add, smul_add, lp.coeFn_add, Pi.add_apply]
      map_smul' z f := by
        apply lp.ext
        funext k
        simp only [map_smul, lp.coeFn_smul, Pi.smul_apply]
        exact smul_comm _ _ _ }
    (‖T‖ * B)
    (by
      intro f
      let v : lp (fun _ : κ ↦ H) 2 :=
        ⟨fun k ↦ (Real.sqrt (w k) : ℂ) • T (multiplicationOperator (a k) f),
          weighted_column_memℓp w hw a B hrow T f⟩
      change ‖v‖ ≤ ‖T‖ * B * ‖f‖
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (norm_nonneg _) hB) (norm_nonneg _))).mp
      have he : ‖v‖ ^ 2 = ∑' k, w k * ‖T (multiplicationOperator (a k) f)‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, v, sqrt_smul_norm_sq _ (hw _)] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v
      rw [he]
      exact (transformed_row_energy w hw a B hrow T f).2.trans_eq (by ring))

/-- Literal coordinates of the actual normalized column
(`app:ch_osc:eq:amplitude-row`). -/
@[simp] theorem weightedRowColumn_apply
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (a : κ → Lp ℂ ∞ μ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) (f : Lp ℂ 2 μ) (k : κ) :
    weightedRowColumn w hw a B hB hrow T f k =
      (Real.sqrt (w k) : ℂ) • T (multiplicationOperator (a k) f) := rfl

/-- The column norm has exactly the original row-energy and bounded
operator costs, independent of the source measure
(`app:ch_osc:eq:amplitude-row`). -/
theorem norm_weightedRowColumn_le
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (a : κ → Lp ℂ ∞ μ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ s : Finset κ, ∀ᵐ u ∂μ, ∑ k ∈ s, w k * ‖a k u‖ ^ 2 ≤ B ^ 2)
    (T : Lp ℂ 2 μ →L[ℂ] H) :
    ‖weightedRowColumn w hw a B hB hrow T‖ ≤ ‖T‖ * B :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) hB) _

end JanetCartan.AmplitudeBound.PaperEstimates
