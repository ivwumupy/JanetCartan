module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Basic
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Adjoint

/-!
# The low gain-one estimate for actual two-position operators

The order-minus-one case of `app:ch_regular_base:eq:fio-input` through output
index one. The weighted primitive budget produces every output derivative;
the Fourier characterization then proves membership and the quantitative bound.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_regular_base:eq:fio-input`: an actual order-minus-one amplitude
maps compact smooth L² data into H¹. Only `2 * (d + 1) + 1` weighted physical
derivatives enter; no operator or derivative estimate is assumed. -/
theorem twoPositionL2Operator_gain_one
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    let f : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
    let v := twoPositionL2Operator hd R b hb hs A
      (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hA)
        (Nat.le_succ _)) f
    MemFourierSobolev 1 v ∧
      fourierSobolevNorm 1 v ≤
        ((1 + (d : ℝ) * (1 + 2 * Real.pi)) * fixedBoxAmplitudeConstant d R) * A * ‖f‖ := by
  dsimp only
  let f : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
  let hbase := amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hA)
    (Nat.le_succ (2 * (d + 1)))
  let v := twoPositionL2Operator hd R b hb hs A hbase f
  let w := fun i ↦ twoPositionL2Operator hd R (outputDerivativeAmplitude b i)
    (contDiff_uncurry_outputDerivativeAmplitude hb i)
    (supportedInCenteredBox_outputDerivativeAmplitude b R hs i) ((1 + 2 * Real.pi) * A)
    (hasAmplitudeDerivativeBound_outputDerivativeAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ A hA) f
  have hw (i : Fin d) : HasEuclideanL2CoordinateDerivative i v (w i) := by
    simp only [HasEuclideanL2CoordinateDerivative, euclideanCoordinateDerivative,
      EuclideanSpace.basisFun_apply]
    exact twoPositionL2Operator_lineDeriv_outputDerivativeAmplitude hd R b hb hs A hA i u hu hus
  have hmem := (memFourierSobolev_zero v).of_coordinateDerivatives (s := 0) le_rfl
    (fun i ↦ memFourierSobolev_zero (w i)) hw
  refine ⟨by simpa only [zero_add] using hmem, ?_⟩
  have hn := fourierSobolevNorm_le_coordinateDerivatives (s := 0) le_rfl
    (memFourierSobolev_zero v) (fun i ↦ memFourierSobolev_zero (w i)) hw
  simp only [zero_add, fourierSobolevNorm_zero] at hn
  calc
    _ ≤ ‖v‖ + ∑ i, ‖w i‖ := hn
    _ ≤ (fixedBoxAmplitudeConstant d R * A) * ‖f‖ +
        ∑ _i : Fin d, (fixedBoxAmplitudeConstant d R * ((1 + 2 * Real.pi) * A)) * ‖f‖ := by
      apply add_le_add (norm_twoPositionL2Operator_apply_le hd R b hb hs A hbase f)
      exact Finset.sum_le_sum fun i _ ↦ norm_twoPositionL2Operator_apply_le ..
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `app:ch_regular_base:eq:fio-input` for all real indices between zero and
one, with L² input and the same fixed low weighted amplitude budget. -/
theorem twoPositionL2Operator_gain_upto_one
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A)
    (s : ℝ) (hs1 : s ≤ 1)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    let f : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
    let v := twoPositionL2Operator hd R b hb hs A
      (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hA)
        (Nat.le_succ _)) f
    MemFourierSobolev s v ∧
      fourierSobolevNorm s v ≤
        ((1 + (d : ℝ) * (1 + 2 * Real.pi)) * fixedBoxAmplitudeConstant d R) * A * ‖f‖ := by
  obtain ⟨hm, hn⟩ := twoPositionL2Operator_gain_one hd R b hb hs A hA u hu hus
  exact ⟨hm.mono hs1, (fourierSobolevNorm_mono hm hs1).trans hn⟩

/-- `app:ch_regular_base:eq:fio-input`: the literal Hilbert adjoint has the
same gain-one bound. Reversal preserves the original weighted budget. -/
theorem twoPositionL2Operator_adjoint_gain_upto_one
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A)
    (s : ℝ) (hs1 : s ≤ 1)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    let f : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
    let v := (twoPositionL2Operator hd R b hb hs A
      (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hA)
        (Nat.le_succ _))).adjoint f
    MemFourierSobolev s v ∧
      fourierSobolevNorm s v ≤
        ((1 + (d : ℝ) * (1 + 2 * Real.pi)) * fixedBoxAmplitudeConstant d R) * A * ‖f‖ := by
  have hA' : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
      (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (adjointAmplitude b ξ) z‖ ≤ A := by
    intro ξ is his z
    rw [euclideanCoordinateDerivList_adjointAmplitude (b := b)
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)), norm_star]
    exact hA ξ _ (by simpa using his) _
  dsimp only
  rw [twoPositionL2Operator_adjoint]
  exact twoPositionL2Operator_gain_upto_one hd R (adjointAmplitude b)
    (contDiff_adjointAmplitude hb) (supportedInCenteredBox_adjointAmplitude hs) A hA'
    s hs1 u hu hus

end JanetCartan.Pseudodifferential
