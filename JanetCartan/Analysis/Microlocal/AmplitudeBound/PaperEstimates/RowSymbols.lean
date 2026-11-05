module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowCoefficients.Energy
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.DiagonalTrace
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowSeries.Operator

/-!
# Actual bounded coefficient symbols from original Sobolev rows

This instantiates the weighted coefficient-input hypothesis of the sharp
row operator on the original compact amplitude. The only quantitative
source input is its actual `H^ell` row bound, with `ell = d/2+1`.
Measurability in the arbitrary source parameter is enough; no parameter
derivative and no higher physical regularity are introduced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound.PaperEstimates

open Pseudodifferential RowCoefficients DiagonalTrace

variable {d : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mode" => Fin d → ℤ

/-- The actual physical row coefficient, on the fixed larger torus from
the original support box (`app:ch_osc:eq:amplitude-row`). -/
def rowFourierCoefficient (R : ℝ) (b : X → E → ℂ) (k : Mode) (u : X) : ℂ :=
  UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) (b u)) k

/-- Actual row Fourier coefficients are measurable in the arbitrary
source parameter, with no derivatives there
(`app:ch_osc:eq:amplitude-row`). -/
theorem stronglyMeasurable_rowFourierCoefficient (R : ℝ) (b : X → E → ℂ)
    (hb : StronglyMeasurable (Function.uncurry b)) (k : Mode) :
    StronglyMeasurable (rowFourierCoefficient R b k) := by
  exact (((UnitAddTorus.mFourier (-k)).continuous.stronglyMeasurable.comp_measurable
    measurable_snd).mul (stronglyMeasurable_boxAmplitudePeriodization hb (amplitudeBoxScale R))).integral_prod_right
      (ν := Measure.pi (fun _ : Fin d ↦ AddCircle.haarAddCircle))

omit [MeasurableSpace X] in
/-- The exact original row Sobolev bound supplies every finite weighted
coefficient-energy inequality used in the operator construction
(`app:ch_osc:eq:amplitude-row`). -/
theorem finite_rowFourierCoefficient_energy
    (R : ℝ) (b : X → E → ℂ) (hs : ∀ u, SupportedInCenteredBox R (b u))
    (hm : ∀ u, MemLp (b u) 2 volume)
    (hHs : ∀ u, MemFourierSobolev (d / 2 + 1 : ℕ) ((hm u).toLp (b u)))
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ u, fourierSobolevNorm (d / 2 + 1 : ℕ) ((hm u).toLp (b u)) ≤ A)
    (s : Finset Mode) (u : X) :
    (∑ k ∈ s, sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2) ≤
      (Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R) * A) ^ 2 := by
  obtain ⟨hseries, henergy⟩ := actual_row_coefficient_energy R (d / 2 + 1) (b u) (hs u) (hm u) (hHs u)
  change Summable (fun k ↦ sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2) at hseries
  change (∑' k, sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2) ≤ _ at henergy
  apply (hseries.sum_le_tsum s (fun k _ ↦ mul_nonneg (sobolevWeight_pos d k).le (sq_nonneg _))).trans
  apply henergy.trans
  rw [mul_pow, Real.sq_sqrt (rowCoefficientEnergyConstant_pos d (d / 2 + 1) R).le]
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (fourierSobolevNorm_nonneg _ _) hA).mpr (hbound u))
    (rowCoefficientEnergyConstant_pos d (d / 2 + 1) R).le

omit [MeasurableSpace X] in
/-- Each actual coefficient is bounded by the SAME original Sobolev
row size, so it defines a genuine `L∞` multiplier on an arbitrary source
measure (`app:ch_osc:eq:amplitude-row`). -/
theorem norm_rowFourierCoefficient_le
    (R : ℝ) (b : X → E → ℂ) (hs : ∀ u, SupportedInCenteredBox R (b u))
    (hm : ∀ u, MemLp (b u) 2 volume)
    (hHs : ∀ u, MemFourierSobolev (d / 2 + 1 : ℕ) ((hm u).toLp (b u)))
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ u, fourierSobolevNorm (d / 2 + 1 : ℕ) ((hm u).toLp (b u)) ≤ A)
    (k : Mode) (u : X) :
    ‖rowFourierCoefficient R b k u‖ ≤ Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R) * A := by
  have hw : 1 ≤ sobolevWeight d k := by
    apply one_le_pow₀
    nlinarith [sq_nonneg (frequencyNorm k)]
  have he := finite_rowFourierCoefficient_energy R b hs hm hHs A hA hbound {k} u
  simp only [Finset.sum_singleton] at he
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  exact (le_mul_of_one_le_left (sq_nonneg _) hw).trans he

section Symbols

variable (R : ℝ) (b : X → EuclideanSpace ℝ (Fin d) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b))
  (hs : ∀ u, SupportedInCenteredBox R (b u))
  (hm : ∀ u, MemLp (b u) 2 volume)
  (hHs : ∀ u, MemFourierSobolev (d / 2 + 1 : ℕ) ((hm u).toLp (b u)))
  (A : ℝ) (hA : 0 ≤ A)
  (hbound : ∀ u, fourierSobolevNorm (d / 2 + 1 : ℕ) ((hm u).toLp (b u)) ≤ A)

/-- The coefficient multiplier is the actual physical Fourier coefficient
of the original row. Its boundedness is proved from the original Sobolev
norm, not assumed independently (`app:ch_osc:eq:amplitude-row`). -/
def rowCoefficientSymbol (k : Mode) : Lp ℂ ∞ μ :=
  boundedSymbol (rowFourierCoefficient R b k)
    (stronglyMeasurable_rowFourierCoefficient R b hb k).aestronglyMeasurable
    (Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R) * A)
    (Filter.Eventually.of_forall (norm_rowFourierCoefficient_le R b hs hm hHs A hA hbound k))

/-- Exact representative of the original coefficient multiplier
(`app:ch_osc:eq:amplitude-row`). -/
theorem rowCoefficientSymbol_coeFn (k : Mode) :
    rowCoefficientSymbol (μ := μ) R b hb hs hm hHs A hA hbound k =ᵐ[μ]
      rowFourierCoefficient R b k :=
  boundedSymbol_coeFn ..

/-- The actual `L∞` coefficient symbols satisfy the weighted source-column
bound, from the original row Sobolev norm and with no source-variable
regularity (`app:ch_osc:eq:amplitude-row`). -/
theorem rowCoefficientSymbol_energy (s : Finset Mode) :
    ∀ᵐ u ∂μ, (∑ k ∈ s, sobolevWeight d k *
      ‖rowCoefficientSymbol (μ := μ) R b hb hs hm hHs A hA hbound k u‖ ^ 2) ≤
        (Real.sqrt (rowCoefficientEnergyConstant d (d / 2 + 1) R) * A) ^ 2 := by
  have hall : ∀ᵐ u ∂μ, ∀ k, rowCoefficientSymbol (μ := μ) R b hb hs hm hHs A hA hbound k u =
      rowFourierCoefficient R b k u := ae_all_iff.mpr (rowCoefficientSymbol_coeFn R b hb hs hm hHs A hA hbound)
  filter_upwards [hall] with u hu
  simp_rw [hu]
  exact finite_rowFourierCoefficient_energy R b hs hm hHs A hA hbound s u

end Symbols
end JanetCartan.AmplitudeBound.PaperEstimates
