module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.Algebra
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.SourceBounds

/-!
# Frequency integrability from primitive physical budgets

The source-transform integrability needed for
`app:ch_regular_base:eq:graph-derivative-transfer` follows from finite coordinate
budgets of the original amplitude. No estimate for an operator output is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: a physical derivative
budget through `d + 1` ensures frequency integrability on compact smooth data.
The source Fréchet bounds and the Leibniz integral budget are both derived. -/
theorem integrable_sourceAmplitudeTransform_of_physicalBudget
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) {N : ℕ} (hN : d + 1 ≤ N)
    {A : ℝ} (hA : HasAmplitudeDerivativeBound b N A)
    (u : E → ℂ) (hu : ContDiff ℝ (d + 1) u) (hus : HasCompactSupport u) (x : E) :
    Integrable (sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y)) u x) := by
  refine integrable_sourceAmplitudeTransform_of_sourceSymbolBounds
    (fun x y ξ ↦ b ξ (pairedPosition x y)) u x 0 ?_ ?_ hus ?_
    (fun k ↦ ((2 * d : ℕ) : ℝ) ^ k * A * ‖physicalSourceInclusion d‖ ^ k) ?_
  · exact hb.continuous.comp (continuous_fst.prodMk
      (continuous_pairedPosition.comp (continuous_const.prodMk continuous_snd)))
  · simpa using hu
  · intro ξ
    exact (hb.comp (contDiff_const.prodMk
      (contDiff_pairedPosition.comp (contDiff_const.prodMk contDiff_id)))).of_le (by simp)
  · intro k hk y ξ
    simp only [pow_zero, mul_one]
    apply norm_iteratedFDeriv_source_le_physicalBudget
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hA ξ x y
    exact (by simpa using hk : k ≤ d + 1).trans hN

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: one extra primitive
physical derivative suffices for the transferred source transform. -/
theorem integrable_sourceAmplitudeTransform_transferAmplitude
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (i : Fin d)
    {N : ℕ} (hN : d + 1 ≤ N) {A : ℝ}
    (hA : HasAmplitudeDerivativeBound b (N + 1) A)
    (u : E → ℂ) (hu : ContDiff ℝ (d + 1) u) (hus : HasCompactSupport u) (x : E) :
    Integrable (sourceAmplitudeTransform
      (fun x y ξ ↦ transferAmplitude b i ξ (pairedPosition x y)) u x) :=
  integrable_sourceAmplitudeTransform_of_physicalBudget _
    (contDiff_uncurry_transferAmplitude hb i) hN
    (hasAmplitudeDerivativeBound_transferAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i N A hA) u hu hus x

/-- `app:ch_regular_base:eq:fio-input`: the published weighted physical budget
discharges source-transform integrability for the gain-one amplitude. -/
theorem integrable_sourceAmplitudeTransform_outputDerivativeAmplitude_of_weightedBudget
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (i : Fin d)
    {N : ℕ} (hN : d + 1 ≤ N) (A : ℝ)
    (hA : ∀ ξ is, is.length ≤ N + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A)
    (u : E → ℂ) (hu : ContDiff ℝ (d + 1) u) (hus : HasCompactSupport u) (x : E) :
    Integrable (sourceAmplitudeTransform
      (fun x y ξ ↦ outputDerivativeAmplitude b i ξ (pairedPosition x y)) u x) :=
  integrable_sourceAmplitudeTransform_of_physicalBudget _
    (contDiff_uncurry_outputDerivativeAmplitude hb i) hN
    (hasAmplitudeDerivativeBound_outputDerivativeAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i N A hA) u hu hus x

end JanetCartan.Pseudodifferential
