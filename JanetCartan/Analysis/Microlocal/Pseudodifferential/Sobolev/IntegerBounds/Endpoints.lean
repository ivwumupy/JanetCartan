module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.GainOne
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension

/-!
# All-data endpoints for the actual two-position operator

The zero-order and L²-to-H¹ endpoints of `app:ch_regular_base:eq:fio-input`
for the scalar Euclidean operator and its literal Hilbert adjoint. Compact
smooth density discharges the passage to arbitrary L² data; the only analytic
hypotheses are smoothness, physical support, and the primitive amplitude budget.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- The all-data zero endpoint of `app:ch_regular_base:eq:fio-input`, including
Sobolev membership, with only the fixed low amplitude budget. -/
theorem twoPositionL2Operator_zero_all_data
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (M : ℝ)
    (hM : HasAmplitudeDerivativeBound b (2 * (d + 1)) M) (f : L²) :
    MemFourierSobolev 0 (twoPositionL2Operator hd R b hb hs M hM f) ∧
      fourierSobolevNorm 0 (twoPositionL2Operator hd R b hb hs M hM f) ≤
        (fixedBoxAmplitudeConstant d R * M) * ‖f‖ := by
  exact ⟨memFourierSobolev_zero _, by
    simpa only [fourierSobolevNorm_zero] using
      norm_twoPositionL2Operator_apply_le hd R b hb hs M hM f⟩

/-- The literal adjoint's all-data zero endpoint in
`app:ch_regular_base:eq:fio-input`, with the original amplitude budget. -/
theorem twoPositionL2Operator_adjoint_zero_all_data
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (M : ℝ)
    (hM : HasAmplitudeDerivativeBound b (2 * (d + 1)) M) (f : L²) :
    MemFourierSobolev 0 ((twoPositionL2Operator hd R b hb hs M hM).adjoint f) ∧
      fourierSobolevNorm 0 ((twoPositionL2Operator hd R b hb hs M hM).adjoint f) ≤
        (fixedBoxAmplitudeConstant d R * M) * ‖f‖ := by
  exact ⟨memFourierSobolev_zero _, by
    simpa only [fourierSobolevNorm_zero] using
      norm_twoPositionL2Operator_adjoint_apply_le hd R b hb hs M hM f⟩

/-- The all-data L²-to-H¹ endpoint of `app:ch_regular_base:eq:fio-input`.
The constant and fixed weighted derivative shift are exactly those of the
compact-test estimate `twoPositionL2Operator_gain_one`. -/
theorem twoPositionL2Operator_gain_one_all_data
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (M : ℝ)
    (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ M) (f : L²) :
    let T := twoPositionL2Operator hd R b hb hs M
      (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
        (Nat.le_succ _))
    MemFourierSobolev 1 (T f) ∧
      fourierSobolevNorm 1 (T f) ≤
        ((1 + (d : ℝ) * (1 + 2 * Real.pi)) * fixedBoxAmplitudeConstant d R) * M * ‖f‖ := by
  dsimp only
  let T := twoPositionL2Operator hd R b hb hs M
    (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
      (Nat.le_succ _))
  have h := fourierSobolev_operator_bound_of_compactSmooth_zero T 1
    (((1 + (d : ℝ) * (1 + 2 * Real.pi)) * fixedBoxAmplitudeConstant d R) * M) 0
    (fun g hg hc ↦ by
      simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using
        twoPositionL2Operator_gain_one hd R b hb hs M hM g hg hc) f
  simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using h

/-- The literal adjoint maps every L² datum into H¹ with the original
weighted amplitude budget. This is the positive endpoint used by H-minus-one
duality in `app:ch_regular_base:thm:actual-calculus`, Step 3; reversing the
kernel and its source cutoff is already proved by the compact-test theorem. -/
theorem twoPositionL2Operator_adjoint_gain_one_all_data
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (M : ℝ)
    (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ M) (f : L²) :
    let T := twoPositionL2Operator hd R b hb hs M
      (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
        (Nat.le_succ _))
    MemFourierSobolev 1 (T.adjoint f) ∧
      fourierSobolevNorm 1 (T.adjoint f) ≤
        ((1 + (d : ℝ) * (1 + 2 * Real.pi)) * fixedBoxAmplitudeConstant d R) * M * ‖f‖ := by
  dsimp only
  let T := twoPositionL2Operator hd R b hb hs M
    (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
      (Nat.le_succ _))
  have h := fourierSobolev_operator_bound_of_compactSmooth_zero T.adjoint 1
    (((1 + (d : ℝ) * (1 + 2 * Real.pi)) * fixedBoxAmplitudeConstant d R) * M) 0
    (fun g hg hc ↦ by
      simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using
        twoPositionL2Operator_adjoint_gain_upto_one hd R b hb hs M hM 1 le_rfl g hg hc) f
  simpa only [fourierSobolevNorm_zero, zero_mul, add_zero] using h

end JanetCartan.Pseudodifferential
