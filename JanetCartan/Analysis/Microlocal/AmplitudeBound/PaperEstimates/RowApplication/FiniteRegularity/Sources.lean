module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Basic
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.TwoPositionCoefficients.FiniteEnergy

/-!
# The original finite-regularity row coefficients

For `app:ch_osc:eq:amplitude-row`, physical derivatives through
`ell = floor(d/2)+1` of the original compact row give its actual coefficient
energy.  No source-parameter derivative, higher physical regularity, or
separate Sobolev-membership premise enters this application.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.AmplitudeBound.PaperEstimates

open RowCoefficients DiagonalTrace TwoPositionCoefficients

variable {d : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mode" => Fin d → ℤ

/-- The finite physical row constant depends only on dimension and the
original support box (`app:ch_osc:eq:amplitude-row`). -/
def finiteRowAmplitudeConstant (d : ℕ) (R : ℝ) : ℝ :=
  sobolevDiagonalConstant d * Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R)

/-- Nonnegativity of the fixed finite-row constant
(`app:ch_osc:eq:amplitude-row`). -/
theorem finiteRowAmplitudeConstant_nonneg (d : ℕ) (R : ℝ) :
    0 ≤ finiteRowAmplitudeConstant d R :=
  mul_nonneg (sobolevDiagonalConstant_nonneg d) (Real.sqrt_nonneg _)

section Coefficients

variable (R : ℝ) (b : X → EuclideanSpace ℝ (Fin d) → ℂ)
  (hc : ∀ u, ContDiff ℝ (d / 2 + 1 : ℕ) (b u))
  (hs : ∀ u, SupportedInCenteredBox R (b u))
  (A : ℝ) (hA : 0 ≤ A)
  (hjet : ∀ u (is : List (Fin d)), is.length ≤ d / 2 + 1 → ∀ x,
    ‖euclideanCoordinateDerivList is (b u) x‖ ≤ A)

include hc hs hA hjet in
omit [MeasurableSpace X] in
/-- Actual weighted Fourier energy of the original finite `C^ell` row
(`app:ch_osc:eq:amplitude-row`). -/
theorem rowFourierCoefficient_energy_of_finiteRegularity (u : X) :
    Summable (fun k ↦ sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2) ∧
      (∑' k, sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2) ≤
        finiteRowCoefficientEnergyConstant d (d / 2 + 1) R * A ^ 2 :=
  finite_row_coefficient_energy (d / 2 + 1) R (b u) (hc u) (hs u) A hA (hjet u)

include hc hs hA hjet in
omit [MeasurableSpace X] in
/-- Every finite coefficient subset obeys the energy bound supplied by
the original physical derivatives (`app:ch_osc:eq:amplitude-row`). -/
theorem finite_rowFourierCoefficient_energy_of_finiteRegularity (s : Finset Mode) (u : X) :
    (∑ k ∈ s, sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2) ≤
      (Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R) * A) ^ 2 := by
  obtain ⟨he, hbound⟩ := rowFourierCoefficient_energy_of_finiteRegularity R b hc hs A hA hjet u
  apply (he.sum_le_tsum s (fun k _ ↦ mul_nonneg (sobolevWeight_pos d k).le (sq_nonneg _))).trans
  simpa only [mul_pow, Real.sq_sqrt (finiteRowCoefficientEnergyConstant_pos d (d / 2 + 1) R).le]
    using hbound

include hc hs hA hjet in
omit [MeasurableSpace X] in
/-- The original coefficient is a bounded source multiplier, with its
bound proved from the finite physical jets (`app:ch_osc:eq:amplitude-row`). -/
theorem norm_rowFourierCoefficient_le_of_finiteRegularity (k : Mode) (u : X) :
    ‖rowFourierCoefficient R b k u‖ ≤
      Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R) * A := by
  have hw : 1 ≤ sobolevWeight d k := by
    apply one_le_pow₀
    nlinarith [sq_nonneg (frequencyNorm k)]
  have he := finite_rowFourierCoefficient_energy_of_finiteRegularity R b hc hs A hA hjet {k} u
  simp only [Finset.sum_singleton] at he
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  exact (le_mul_of_one_le_left (sq_nonneg _) hw).trans he

include hc hs hA hjet in
omit [MeasurableSpace X] in
/-- Absolute summability and its uniform bound come from the original
finite-regularity coefficient energy (`app:ch_osc:eq:amplitude-row`). -/
theorem rowFourierCoefficient_absolute_sum_bound_of_finiteRegularity (u : X) :
    Summable (fun k ↦ ‖rowFourierCoefficient R b k u‖) ∧
      (∑' k, ‖rowFourierCoefficient R b k u‖) ≤ finiteRowAmplitudeConstant d R * A := by
  obtain ⟨he, henergy⟩ := rowFourierCoefficient_energy_of_finiteRegularity R b hc hs A hA hjet u
  obtain ⟨habs, hcs⟩ := summable_and_tsum_le_sqrt_mul_sqrt
    (t := fun k ↦ ‖rowFourierCoefficient R b k u‖)
    (a := fun k ↦ (sobolevWeight d k)⁻¹)
    (b := fun k ↦ sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2)
    (fun _ ↦ norm_nonneg _) (fun k ↦ inv_nonneg.mpr (sobolevWeight_pos d k).le)
    (fun k ↦ mul_nonneg (sobolevWeight_pos d k).le (sq_nonneg _))
    (fun k ↦ by rw [← mul_assoc, inv_mul_cancel₀ (sobolevWeight_pos d k).ne', one_mul])
    (summable_inverse_sobolevWeight d) he
  refine ⟨habs, hcs.trans ?_⟩
  have henergy' : (∑' k, sobolevWeight d k * ‖rowFourierCoefficient R b k u‖ ^ 2) ≤
      (Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R) * A) ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt (finiteRowCoefficientEnergyConstant_pos d (d / 2 + 1) R).le]
      using henergy
  have hroot := (Real.sqrt_le_iff).mpr ⟨mul_nonneg (Real.sqrt_nonneg _) hA, henergy'⟩
  simpa only [finiteRowAmplitudeConstant, sobolevDiagonalConstant, mul_assoc] using
    mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (∑' k, (sobolevWeight d k)⁻¹))

include hc hs hA hjet in
omit [MeasurableSpace X] in
/-- The original finite `C^ell` row is reconstructed everywhere by its
literal cutoff Fourier series, including at the physical cell boundary
(`app:ch_osc:eq:amplitude-row`). -/
theorem rowFourierCoefficient_hasSum_of_finiteRegularity (u : X) (x : E) :
    HasSum (fun k ↦ boxCellCutoff (amplitudeBoxScale R) x *
      UnitAddTorus.mFourier k (scaledTorusChart (amplitudeBoxScale R) x) *
        rowFourierCoefficient R b k u) (b u x) := by
  let L := amplitudeBoxScale R
  have hF : Continuous (boxAmplitudePeriodization L (b u)) :=
    continuous_amplitudePeriodization_of_supported (div_amplitudeBoxScale_lt R)
      (supportedInCenteredBox_comp_smul (amplitudeBoxScale_pos R) (hs u))
      ((hc u).continuous.comp (continuous_const_smul L))
  let F : C(Torus d, ℂ) := ⟨boxAmplitudePeriodization L (b u), hF⟩
  have habs : Summable (UnitAddTorus.mFourierCoeff F) :=
    (rowFourierCoefficient_absolute_sum_bound_of_finiteRegularity R b hc hs A hA hjet u).1.of_norm
  have hsum := (UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := F) habs
    (scaledTorusChart L x)).mul_left (boxCellCutoff L x)
  have he : boxCellCutoff L x * boxAmplitudePeriodization L (b u) (scaledTorusChart L x) = b u x :=
    boxCellCutoff_boxAmplitudePeriodization_row_eq (amplitudeBoxScale_pos R)
      (div_amplitudeBoxScale_lt R) (hs u) x
  rw [show boxCellCutoff L x * F (scaledTorusChart L x) = b u x from he] at hsum
  convert hsum using 1
  funext k
  simp only [F, ContinuousMap.coe_mk, smul_eq_mul, rowFourierCoefficient, L]
  ring

end Coefficients

section Symbols

variable (R : ℝ) (b : X → EuclideanSpace ℝ (Fin d) → ℂ) (hb : StronglyMeasurable (Function.uncurry b))
  (hc : ∀ u, ContDiff ℝ (d / 2 + 1 : ℕ) (b u))
  (hs : ∀ u, SupportedInCenteredBox R (b u))
  (A : ℝ) (hA : 0 ≤ A)
  (hjet : ∀ u (is : List (Fin d)), is.length ≤ d / 2 + 1 → ∀ x,
    ‖euclideanCoordinateDerivList is (b u) x‖ ≤ A)

/-- Actual bounded coefficient symbols of the finite-regularity row,
with the original source measure (`app:ch_osc:eq:amplitude-row`). -/
def finiteRegularityRowSymbol (k : Mode) : Lp ℂ ∞ μ :=
  boundedSymbol (rowFourierCoefficient R b k)
    (stronglyMeasurable_rowFourierCoefficient R b hb k).aestronglyMeasurable
    (Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R) * A)
    (Eventually.of_forall (norm_rowFourierCoefficient_le_of_finiteRegularity R b hc hs A hA hjet k))

/-- The source symbol has the literal original Fourier coefficient as
its representative (`app:ch_osc:eq:amplitude-row`). -/
theorem finiteRegularityRowSymbol_coeFn (k : Mode) :
    finiteRegularityRowSymbol (μ := μ) R b hb hc hs A hA hjet k =ᵐ[μ] rowFourierCoefficient R b k :=
  boundedSymbol_coeFn ..

/-- The weighted-column input for the same actual coefficient symbols,
proved from finite physical derivatives (`app:ch_osc:eq:amplitude-row`). -/
theorem finiteRegularityRowSymbol_energy (s : Finset Mode) :
    ∀ᵐ u ∂μ, (∑ k ∈ s, sobolevWeight d k *
      ‖finiteRegularityRowSymbol (μ := μ) R b hb hc hs A hA hjet k u‖ ^ 2) ≤
        (Real.sqrt (finiteRowCoefficientEnergyConstant d (d / 2 + 1) R) * A) ^ 2 := by
  have hall := ae_all_iff.mpr (finiteRegularityRowSymbol_coeFn (μ := μ) R b hb hc hs A hA hjet)
  filter_upwards [hall] with u hu
  simp_rw [hu]
  exact finite_rowFourierCoefficient_energy_of_finiteRegularity R b hc hs A hA hjet s u

end Symbols
end JanetCartan.AmplitudeBound.PaperEstimates
