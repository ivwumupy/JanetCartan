module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowSymbols
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowCoefficients.Reconstruction

/-!
# The sharp operator for the original compact Sobolev rows

This is the actual construction in `app:ch_osc:eq:amplitude-row`. Its
source symbols are the Fourier coefficients of the original amplitude,
and its output modulations use the original physical cell. The source
measure is arbitrary and no derivatives in that variable are required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.AmplitudeBound.PaperEstimates

open Pseudodifferential RowCoefficients DiagonalTrace

variable {d : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mode" => Fin d → ℤ
local notation "Output" => Lp ℂ 2 (volume : Measure E)

/-- The fixed constant for the original physical support box in the
sharp row estimate (`app:ch_osc:eq:amplitude-row`). -/
def rowAmplitudeConstant (d : ℕ) (R : ℝ) : ℝ :=
  sobolevDiagonalConstant d * Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R)

/-- The row constant is nonnegative. -/
theorem rowAmplitudeConstant_nonneg (d : ℕ) (R : ℝ) : 0 ≤ rowAmplitudeConstant d R :=
  mul_nonneg (sobolevDiagonalConstant_nonneg d) (Real.sqrt_nonneg _)

/-- Actual physical cutoff character for a row mode
(`app:ch_osc:eq:amplitude-row`). -/
def rowPhysicalModulation (R : ℝ) (k : Mode) : Output →L[ℂ] Output :=
  cutoffModulation (scaledTorusChart (amplitudeBoxScale R))
    (measurable_scaledTorusChart (amplitudeBoxScale R))
    (boxCellCutoff (amplitudeBoxScale R))
    (aestronglyMeasurable_boxCellCutoff (amplitudeBoxScale R))
    (Eventually.of_forall (norm_boxCellCutoff_le (amplitudeBoxScale R))) k

/-- The original output modulations are contractions. -/
theorem norm_rowPhysicalModulation_le (R : ℝ) (k : Mode) :
    ‖rowPhysicalModulation R k‖ ≤ 1 := norm_cutoffModulation_le ..

section OriginalRows

variable (R : ℝ) (b : X → EuclideanSpace ℝ (Fin d) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b))
  (hs : ∀ u, SupportedInCenteredBox R (b u))
  (hm : ∀ u, MemLp (b u) 2 volume)
  (hHs : ∀ u, MemFourierSobolev (d / 2 + 1 : ℕ) ((hm u).toLp (b u)))
  (A : ℝ) (hA : 0 ≤ A)
  (hbound : ∀ u, fourierSobolevNorm (d / 2 + 1 : ℕ) ((hm u).toLp (b u)) ≤ A)

/-- The bounded operator built from the original compact Sobolev row.
Every analytic coefficient bound is supplied by that row's actual
`H^ell` norm (`app:ch_osc:eq:amplitude-row`). -/
def compactRowAmplitudeOperator (T : Lp ℂ 2 μ →L[ℂ] Output) :
    Lp ℂ 2 μ →L[ℂ] Output :=
  rowAmplitudeOperator (sobolevWeight d) (sobolevWeight_pos d)
    (summable_inverse_sobolevWeight d) (rowPhysicalModulation R)
    (norm_rowPhysicalModulation_le R)
    (rowCoefficientSymbol R b hb hs hm hHs A hA hbound)
    (Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R) * A)
    (mul_nonneg (Real.sqrt_nonneg _) hA)
    (rowCoefficientSymbol_energy R b hb hs hm hHs A hA hbound) T

/-- The original-row construction has the sharp bound, with exactly
`ell = floor(d/2)+1` and no source-variable derivatives
(`app:ch_osc:eq:amplitude-row`). -/
theorem norm_compactRowAmplitudeOperator_le (T : Lp ℂ 2 μ →L[ℂ] Output) :
    ‖compactRowAmplitudeOperator R b hb hs hm hHs A hA hbound T‖ ≤
      rowAmplitudeConstant d R * ‖T‖ * A := by
  have h := norm_rowAmplitudeOperator_le (sobolevWeight d) (sobolevWeight_pos d)
    (summable_inverse_sobolevWeight d) (rowPhysicalModulation R)
    (norm_rowPhysicalModulation_le R)
    (rowCoefficientSymbol R b hb hs hm hHs A hA hbound)
    (Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R) * A)
    (mul_nonneg (Real.sqrt_nonneg _) hA)
    (rowCoefficientSymbol_energy R b hb hs hm hHs A hA hbound) T
  calc
    ‖compactRowAmplitudeOperator R b hb hs hm hHs A hA hbound T‖ ≤
        Real.sqrt (∑' k, (sobolevWeight d k)⁻¹) * ‖T‖ *
          (Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R) * A) := h
    _ = rowAmplitudeConstant d R * ‖T‖ * A := by
      unfold rowAmplitudeConstant sobolevDiagonalConstant
      ring

/-- The literal finite operators made from the original coefficients
converge to the original-row construction in operator norm
(`app:ch_osc:eq:amplitude-row`). -/
theorem tendsto_compactRowAmplitudeOperator (T : Lp ℂ 2 μ →L[ℂ] Output) :
    Tendsto (finiteRowAmplitudeOperator (rowPhysicalModulation R) T
      (rowCoefficientSymbol R b hb hs hm hHs A hA hbound)) atTop
        (𝓝 (compactRowAmplitudeOperator R b hb hs hm hHs A hA hbound T)) :=
  tendsto_finiteRowAmplitudeOperator (sobolevWeight d) (sobolevWeight_pos d)
    (summable_inverse_sobolevWeight d) (rowPhysicalModulation R)
    (norm_rowPhysicalModulation_le R)
    (rowCoefficientSymbol R b hb hs hm hHs A hA hbound)
    (Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R) * A)
    (mul_nonneg (Real.sqrt_nonneg _) hA)
    (rowCoefficientSymbol_energy R b hb hs hm hHs A hA hbound) T

include hs hm hHs hA hbound in
omit [MeasurableSpace X] in
/-- The actual original coefficients have a uniform absolute-sum bound.
This supplies the domination in the literal kernel limit, rather than
assuming absolute summability of mode operator norms
(`app:ch_osc:eq:amplitude-row`). -/
theorem rowFourierCoefficient_absolute_sum_bound (u : X) :
    Summable (fun k ↦ ‖rowFourierCoefficient R b k u‖) ∧
      (∑' k, ‖rowFourierCoefficient R b k u‖) ≤ rowAmplitudeConstant d R * A := by
  have he := (actual_row_coefficient_energy R (d / 2 + 1) (b u) (hs u) (hm u) (hHs u)).1
  change Summable (fun k ↦ sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2) at he
  obtain ⟨habs, hcs⟩ := summable_and_tsum_le_sqrt_mul_sqrt
    (t := fun k ↦ ‖rowFourierCoefficient R b k u‖)
    (a := fun k ↦ (sobolevWeight d k)⁻¹)
    (b := fun k ↦ sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2)
    (fun _ ↦ norm_nonneg _) (fun k ↦ inv_nonneg.mpr (sobolevWeight_pos d k).le)
    (fun k ↦ mul_nonneg (sobolevWeight_pos d k).le (sq_nonneg _))
    (fun k ↦ by rw [← mul_assoc, inv_mul_cancel₀ (sobolevWeight_pos d k).ne', one_mul])
    (summable_inverse_sobolevWeight d) he
  refine ⟨habs, hcs.trans ?_⟩
  have henergy : (∑' k, sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2) ≤
      (Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R) * A) ^ 2 :=
    Real.tsum_le_of_sum_le (fun k ↦ mul_nonneg (sobolevWeight_pos d k).le (sq_nonneg _))
      (fun s ↦ finite_rowFourierCoefficient_energy R b hs hm hHs A hA hbound s u)
  have hsqrt := (Real.sqrt_le_iff).mpr
    ⟨mul_nonneg (Real.sqrt_nonneg _) hA, henergy⟩
  simpa only [rowAmplitudeConstant, sobolevDiagonalConstant, mul_assoc] using
    mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (∑' k, (sobolevWeight d k)⁻¹))

end OriginalRows
end JanetCartan.AmplitudeBound.PaperEstimates
