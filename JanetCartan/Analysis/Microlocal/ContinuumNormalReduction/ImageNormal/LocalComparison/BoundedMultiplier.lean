module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.BesselSymbol
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Multipliers

/-!
# The Euclidean image inverse on the full L² space

The bounded unit-frequency multiplier with symbol `imageBesselSymbol`, used
in the local comparison of `app:ch_background:prop:bg-frame`, Step 1.
Its action on Schwartz functions is identified with the existing multiplier.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The image symbol is bounded on all frequencies, with the manuscript's
physical normalization (`app:ch_background:defn:bg-row`). -/
theorem memLp_top_complex_imageBesselSymbol :
    MemLp (fun ξ : E ↦ (imageBesselSymbol ξ : ℂ)) ⊤ := by
  apply memLp_top_of_bound
    hasTemperateGrowth_complex_imageBesselSymbol.1.continuous.aestronglyMeasurable 1
  filter_upwards [] with ξ
  rw [Complex.norm_real, Real.norm_eq_abs, imageBesselSymbol, abs_of_pos (euclideanSobolevWeight_pos _ _)]
  exact (euclideanSobolevWeight_mono (by norm_num : (-1 : ℝ) ≤ 0) _).trans_eq
    (euclideanSobolevWeight_zero _)

/-- The actual Euclidean Bessel inverse on Lebesgue L²
(`app:ch_background:defn:bg-row`), constructed by Plancherel. -/
def imageBesselL2Operator : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMultiplier (memLp_top_complex_imageBesselSymbol.toLp _)

/-- The full L² multiplier extends its literal Schwartz action
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBesselL2Operator_toLp (u : 𝓢(E, ℂ)) :
    imageBesselL2Operator (u.toLp 2) =
      (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u).toLp 2 := by
  have hm : multiplicationOperator (memLp_top_complex_imageBesselSymbol.toLp _)
      ((𝓕 u : 𝓢(E, ℂ)).toLp 2) =
      (SchwartzMap.smulLeftCLM ℂ (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) (𝓕 u)).toLp 2 := by
    apply Lp.ext
    filter_upwards [multiplicationOperator_coeFn
      (memLp_top_complex_imageBesselSymbol.toLp _) ((𝓕 u : 𝓢(E, ℂ)).toLp 2),
      memLp_top_complex_imageBesselSymbol.coeFn_toLp,
      (𝓕 u : 𝓢(E, ℂ)).coeFn_toLp 2,
      (SchwartzMap.smulLeftCLM ℂ (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) (𝓕 u)).coeFn_toLp 2]
      with ξ hξ ha hu' hv
    rw [hξ, ha, hu', hv, SchwartzMap.smulLeftCLM_apply_apply
      hasTemperateGrowth_complex_imageBesselSymbol, smul_eq_mul]
  change 𝓕⁻ (multiplicationOperator (memLp_top_complex_imageBesselSymbol.toLp _)
    (𝓕 (u.toLp 2))) = _
  rw [SchwartzMap.toLp_fourier_eq, hm, SchwartzMap.toLp_fourierInv_eq]
  rfl

end JanetCartan.ContinuumNormalReduction.ImageNormal
