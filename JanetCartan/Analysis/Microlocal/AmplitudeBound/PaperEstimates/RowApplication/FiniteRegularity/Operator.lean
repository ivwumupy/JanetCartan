module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.FiniteRegularity.Sources

/-!
# The actual row operator from finite physical derivatives

The same original coefficient symbols and physical modulations construct
the operator in `app:ch_osc:eq:amplitude-row`. The estimate uses only the
finite physical `C^ell` bound and the original operator norm.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.AmplitudeBound.PaperEstimates

open DiagonalTrace TwoPositionCoefficients

variable {d : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mode" => Fin d → ℤ
local notation "Output" => Lp ℂ 2 (volume : Measure E)

variable (R : ℝ) (b : X → EuclideanSpace ℝ (Fin d) → ℂ) (hb : StronglyMeasurable (Function.uncurry b))
  (hc : ∀ u, ContDiff ℝ (d / 2 + 1 : ℕ) (b u))
  (hs : ∀ u, SupportedInCenteredBox R (b u))
  (A : ℝ) (hA : 0 ≤ A)
  (hjet : ∀ u (is : List (Fin d)), is.length ≤ d / 2 + 1 → ∀ x,
    ‖euclideanCoordinateDerivList is (b u) x‖ ≤ A)

/-- The bounded original row operator, from finite physical regularity
alone (`app:ch_osc:eq:amplitude-row`). -/
def finiteRegularityRowAmplitudeOperator (T : Lp ℂ 2 μ →L[ℂ] Output) :
    Lp ℂ 2 μ →L[ℂ] Output :=
  rowAmplitudeOperator (sobolevWeight d) (sobolevWeight_pos d)
    (summable_inverse_sobolevWeight d) (rowPhysicalModulation R)
    (norm_rowPhysicalModulation_le R)
    (finiteRegularityRowSymbol R b hb hc hs A hA hjet)
    (Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R) * A)
    (mul_nonneg (Real.sqrt_nonneg _) hA)
    (finiteRegularityRowSymbol_energy R b hb hc hs A hA hjet) T

/-- The exact finite-regularity row estimate with fixed geometric constant
and the norm of the same original operator
(`app:ch_osc:eq:amplitude-row`). -/
theorem norm_finiteRegularityRowAmplitudeOperator_le (T : Lp ℂ 2 μ →L[ℂ] Output) :
    ‖finiteRegularityRowAmplitudeOperator R b hb hc hs A hA hjet T‖ ≤
      finiteRowAmplitudeConstant d R * ‖T‖ * A := by
  have h := norm_rowAmplitudeOperator_le (sobolevWeight d) (sobolevWeight_pos d)
    (summable_inverse_sobolevWeight d) (rowPhysicalModulation R)
    (norm_rowPhysicalModulation_le R)
    (finiteRegularityRowSymbol R b hb hc hs A hA hjet)
    (Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R) * A)
    (mul_nonneg (Real.sqrt_nonneg _) hA)
    (finiteRegularityRowSymbol_energy R b hb hc hs A hA hjet) T
  calc
    _ ≤ Real.sqrt (∑' k, (sobolevWeight d k)⁻¹) * ‖T‖ *
        (Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R) * A) := h
    _ = _ := by unfold finiteRowAmplitudeConstant sobolevDiagonalConstant; ring

/-- The literal finite coefficient operators converge in norm to this
same finite-regularity row construction (`app:ch_osc:eq:amplitude-row`). -/
theorem tendsto_finiteRegularityRowAmplitudeOperator (T : Lp ℂ 2 μ →L[ℂ] Output) :
    Tendsto (finiteRowAmplitudeOperator (rowPhysicalModulation R) T
      (finiteRegularityRowSymbol R b hb hc hs A hA hjet)) atTop
      (𝓝 (finiteRegularityRowAmplitudeOperator R b hb hc hs A hA hjet T)) :=
  tendsto_finiteRowAmplitudeOperator (sobolevWeight d) (sobolevWeight_pos d)
    (summable_inverse_sobolevWeight d) (rowPhysicalModulation R)
    (norm_rowPhysicalModulation_le R)
    (finiteRegularityRowSymbol R b hb hc hs A hA hjet)
    (Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R) * A)
    (mul_nonneg (Real.sqrt_nonneg _) hA)
    (finiteRegularityRowSymbol_energy R b hb hc hs A hA hjet) T

/-- Strong convergence on the original input along any cofinal finite
mode sequence, for the literal kernel limit
(`app:ch_osc:eq:amplitude-row`). -/
theorem tendsto_finiteRegularityRowAmplitudeOperator_apply
    (T : Lp ℂ 2 μ →L[ℂ] Output) (f : Lp ℂ 2 μ)
    (s : ℕ → Finset Mode) (hs' : Tendsto s atTop atTop) :
    Tendsto (fun N ↦ finiteRowAmplitudeOperator (rowPhysicalModulation R) T
      (finiteRegularityRowSymbol R b hb hc hs A hA hjet) (s N) f) atTop
      (𝓝 (finiteRegularityRowAmplitudeOperator R b hb hc hs A hA hjet T f)) :=
  (show Continuous (fun P : Lp ℂ 2 μ →L[ℂ] Output ↦ P f) by fun_prop).continuousAt.tendsto.comp
    ((tendsto_finiteRegularityRowAmplitudeOperator R b hb hc hs A hA hjet T).comp hs')

end JanetCartan.AmplitudeBound.PaperEstimates
