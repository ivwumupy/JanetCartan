module

public import JanetCartan.Analysis.Microlocal.NormalComparison.ChannelBounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.ChangeOfVariables
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Manuscript normalization and unit-period frequency

The normalization and frequency substitution in Step 1 of
`app:ch_osc:prop:osc-normal`. The amplitude theorem uses the phase `2π⟪x-y,ξ⟫`,
so its frequency variable is `ξ = K v / (2π)`. Physical derivative bounds are
unchanged by this substitution.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison

variable {n r : ℕ}

/-- The scalar normalization of `T_ε^K` in `app:ch_osc:prop:osc-normal`. -/
def normalOperatorScale (n : ℕ) (K : ℝ) : ℝ :=
  (K / (2 * Real.pi)) ^ ((n : ℝ) / 2)

/-- Squaring the operator normalization gives the exact normal-kernel
prefactor in `app:ch_osc:eq:osc-exact-normal-kernel`. -/
theorem normalOperatorScale_sq (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    normalOperatorScale n K ^ 2 = (K / (2 * Real.pi)) ^ n := by
  have h : 0 ≤ K / (2 * Real.pi) := div_nonneg hK (by positivity)
  rw [normalOperatorScale, ← Real.rpow_mul_natCast h]
  simp

/-- The rescaled full amplitude for the unit-period Fourier convention,
used in Step 1 of `app:ch_osc:prop:osc-normal`. Both positions are retained. -/
def unitFrequencyAmplitude (K : ℝ)
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ)
    (ξ : Euclidean n) (z : Euclidean (2 * n)) : Matrix (Fin r) (Fin r) ℂ :=
  b ((K / (2 * Real.pi))⁻¹ • ξ) z

/-- Frequency rescaling preserves joint smoothness in Step 1 of
`app:ch_osc:prop:osc-normal`. -/
theorem contDiff_unitFrequencyAmplitude (K : ℝ)
    {b : Euclidean n → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) :
    ContDiff ℝ ∞ (Function.uncurry (unitFrequencyAmplitude K b)) := by
  unfold unitFrequencyAmplitude
  exact hb.comp ((contDiff_fst.const_smul ((K / (2 * Real.pi))⁻¹)).prodMk contDiff_snd)

/-- No frequency factor enters the physical derivative budget of
`app:ch_osc:lem:osc-amplitude`, as used in `app:ch_osc:prop:osc-normal`. -/
theorem MatrixNormalAmplitudeBounds.unitFrequencyAmplitude
    {b : Euclidean n → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ}
    {R A : ℝ} (hb : MatrixNormalAmplitudeBounds b R A) (K : ℝ) :
    MatrixNormalAmplitudeBounds (unitFrequencyAmplitude K b) R A := by
  refine ⟨?_, fun ξ ↦ hb.smooth _, fun ξ ↦ hb.support _, fun ξ ↦ hb.derivative _⟩
  exact hb.measurable.comp_measurable
    ((measurable_fst.const_smul ((K / (2 * Real.pi))⁻¹)).prodMk measurable_snd)

/-- Exact conversion of the entire matrix integral to unit-period frequency,
including the Jacobian factor. This is the rescaling in Step 1 of
`app:ch_osc:prop:osc-normal`, not a diagonal or asymptotic formula. -/
theorem normal_integral_eq_unitFrequency
    {K : ℝ} (hK : 0 < K) (x y : Euclidean n)
    (b : Euclidean n → Matrix (Fin r) (Fin r) ℂ) :
    (K / (2 * Real.pi)) ^ n •
        (∫ v, oscillatoryFactor K (inner ℝ (x - y) v) • b v) =
      ∫ ξ, Complex.exp ((2 * Real.pi * inner ℝ (x - y) ξ : ℝ) * Complex.I) •
        b ((K / (2 * Real.pi))⁻¹ • ξ) := by
  have ha : 0 ≤ K / (2 * Real.pi) := le_of_lt (div_pos hK (by positivity))
  have h := Measure.integral_comp_inv_smul_of_nonneg volume
    (fun v ↦ oscillatoryFactor K (inner ℝ (x - y) v) • b v) ha
  simp only [Euclidean, finrank_euclideanSpace_fin] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with ξ
  congr 1
  unfold oscillatoryFactor
  congr 1
  rw [inner_smul_right]
  have he : K * ((K / (2 * Real.pi))⁻¹ * inner ℝ (x - y) ξ) =
      2 * Real.pi * inner ℝ (x - y) ξ := by
    field_simp
  rw [he, mul_comm Complex.I]

end JanetCartan.NormalComparison
