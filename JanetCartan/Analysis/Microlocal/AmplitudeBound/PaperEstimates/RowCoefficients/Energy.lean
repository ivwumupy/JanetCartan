module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowCoefficients.Dilation
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowCoefficients.WeakEnergy
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.SourceEstimates

/-!
# The actual compact-row coefficient estimate

This instantiates the weak-derivative energy estimate on the same dilated,
centered periodization used for the physical row kernel in
`app:ch_osc:eq:amplitude-row`.  Constants are fixed before the input row; only its
original integer Fourier Sobolev norm appears.  Arbitrary natural order also
serves the combined-position input of part (ii) of the same lemma.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.AmplitudeBound.RowCoefficients

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Equality of the actual chart class and the original dilated row.  This is
the same coefficient source in `app:ch_osc:eq:amplitude-row`. -/
theorem toTorus_dilate_toLp_ae {L : ℝ} (hL : L ≠ 0) (f : E → ℂ)
    (hf : MemLp f 2 volume) :
    toTorus (𝕜 := ℂ) (dilateL2 L hL (hf.toLp f)) =ᵐ[volume]
      boxAmplitudePeriodization L f := by
  have he : dilateL2 L hL (hf.toLp f) =ᵐ[volume] fun x ↦ f (L • x) :=
    (dilateL2_coe L hL (hf.toLp f)).trans
      ((Measure.quasiMeasurePreserving_smul volume hL).ae_eq_comp hf.coeFn_toLp)
  filter_upwards [toTorus_coe (𝕜 := ℂ) (dilateL2 L hL (hf.toLp f)),
    measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp he.restrict]
    with z hz hez
  exact hz.trans hez

/-- The fixed-box constant in the genuine finite-Sobolev coefficient estimate
for `app:ch_osc:eq:amplitude-row` and its combined-position use. -/
def rowCoefficientEnergyConstant (d s : ℕ) (R : ℝ) : ℝ :=
  2 * (d + 1 : ℝ) ^ s *
    ((1 + 2 * Real.pi) ^ s *
      (amplitudeBoxScale R * (1 + 2 * Real.pi * d)) ^ s) ^ 2

/-- The row coefficient constant is strictly positive and depends only on the
original fixed box, dimension, and order (`app:ch_osc:lem:osc-amplitude`). -/
theorem rowCoefficientEnergyConstant_pos (d s : ℕ) (R : ℝ) :
    0 < rowCoefficientEnergyConstant d s R := by
  have := amplitudeBoxScale_pos R
  unfold rowCoefficientEnergyConstant
  positivity

/-- Actual complex coefficients of the same normalized periodization have
summable weighted energy controlled by the original finite Sobolev norm.
No source derivatives above `s`, and no external-parameter derivatives, occur
in this input to `app:ch_osc:eq:amplitude-row`. -/
theorem actual_row_coefficient_energy (R : ℝ) (s : ℕ) (f : E → ℂ)
    (hs : SupportedInCenteredBox R f) (hf : MemLp f 2 volume)
    (hHs : MemFourierSobolev (s : ℝ) (hf.toLp f)) :
    Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ s *
      ‖UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) f) k‖ ^ 2) ∧
    (∑' k, (1 + frequencyNorm k ^ 2) ^ s *
      ‖UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) f) k‖ ^ 2) ≤
      rowCoefficientEnergyConstant d s R * fourierSobolevNorm (s : ℝ) (hf.toLp f) ^ 2 := by
  let L := amplitudeBoxScale R
  have hL : 1 ≤ L := by dsimp [L, amplitudeBoxScale]; linarith [abs_nonneg R]
  have hL0 : 0 < L := amplitudeBoxScale_pos R
  let u := dilateL2 L hL0.ne' (hf.toLp f)
  have he : u =ᵐ[volume] fun x ↦ f (L • x) :=
    (dilateL2_coe L hL0.ne' (hf.toLp f)).trans
      ((Measure.quasiMeasurePreserving_smul volume hL0.ne').ae_eq_comp hf.coeFn_toLp)
  have hus : ∀ᵐ x ∂volume, x ∉ chartBox (R / L) → u x = 0 := by
    filter_upwards [he] with x hx hxs
    rw [hx]
    by_contra hn
    exact hxs (supportedInCenteredBox_comp_smul hL0 hs x hn)
  obtain ⟨huH, hnuH⟩ := fourierSobolev_dilate_nat hL s (hf.toLp f) hHs
  obtain ⟨henergy, hbound⟩ := supported_periodic_coefficient_energy
    (div_amplitudeBoxScale_lt R) s u hus huH
  have heT := toTorus_dilate_toLp_ae hL0.ne' f hf
  have hc (k : Fin d → ℤ) : UnitAddTorus.mFourierCoeff (toTorus (𝕜 := ℂ) u) k =
      UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization L f) k := by
    rw [mFourierCoeff_eq_volume_integral, mFourierCoeff_eq_volume_integral]
    exact integral_congr_ae (heT.mono (fun z h ↦
      congrArg (fun a : ℂ ↦ UnitAddTorus.mFourier (-k) z * a) h))
  simp_rw [hc] at henergy hbound
  refine ⟨henergy, hbound.trans ?_⟩
  calc
    _ ≤ 2 * ((d + 1 : ℝ) ^ s *
        ((1 + 2 * Real.pi) ^ s *
          ((L * (1 + 2 * Real.pi * d)) ^ s *
            fourierSobolevNorm (s : ℝ) (hf.toLp f))) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀
        (mul_nonneg (by positivity) (fourierSobolevNorm_nonneg _ _))
      exact mul_le_mul_of_nonneg_left hnuH (by positivity)
    _ = _ := by dsimp [rowCoefficientEnergyConstant, L]; ring

/-- Uniform quantifier order for the coefficient source in
`app:ch_osc:eq:amplitude-row`: the constant is selected before the row. -/
theorem exists_actual_row_coefficient_energy_constant (R : ℝ) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E → ℂ), SupportedInCenteredBox R f →
      ∀ hf : MemLp f 2 volume, MemFourierSobolev (s : ℝ) (hf.toLp f) →
        Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ s *
          ‖UnitAddTorus.mFourierCoeff
            (boxAmplitudePeriodization (amplitudeBoxScale R) f) k‖ ^ 2) ∧
        (∑' k, (1 + frequencyNorm k ^ 2) ^ s *
          ‖UnitAddTorus.mFourierCoeff
            (boxAmplitudePeriodization (amplitudeBoxScale R) f) k‖ ^ 2) ≤
          C * fourierSobolevNorm (s : ℝ) (hf.toLp f) ^ 2 :=
  ⟨rowCoefficientEnergyConstant d s R, rowCoefficientEnergyConstant_pos d s R,
    actual_row_coefficient_energy R s⟩

end JanetCartan.AmplitudeBound.RowCoefficients
