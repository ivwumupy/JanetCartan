module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.IntegerBounds.Endpoints
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.TameGain

/-!
# Integer tame bounds for all Euclidean Sobolev data

The scalar pseudodifferential case of `app:ch_regular_base:eq:fio-input`
and Step 3 of `app:ch_regular_base:thm:actual-calculus`, at every natural
input order, including zero. Each constant is chosen before the amplitude,
its high budget, and the datum. The low and high derivative shifts are the
ones proved in `Estimates.TameZero` and `Estimates.TameGain`.

The compact-test premises of `Extension` are discharged by those scalar
estimates. The remaining analytic hypotheses are the amplitude's joint
smoothness, fixed physical support, and primitive low/high derivative bounds;
downstream matrix and geometric constructions must supply these hypotheses.
The operators retain both physical variables and literal Hilbert adjoints,
on Euclidean Lebesgue L² with the existing 2π Fourier normalization.
This module does not assert the real-order or general graph-phase theorem.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

private theorem lowBudget_mul_le_tame (K M H x : ℝ) (hK : 0 ≤ K) (hx : 0 ≤ x) :
    K * M * x ≤ (K * max 0 M) * (x + max 1 H * x) := by
  calc
    _ ≤ (K * max 0 M) * x := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hK) hx
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg (by positivity) hx)) (by positivity)

/-- `app:ch_regular_base:eq:fio-input`, order zero, on every Hⁿ datum for
every natural `n`, including zero. Only the primitive budgets at
`2 * (d + 1)` and `2 * (d + 1) + n` are assumed; the constant is chosen
before the amplitude and the high budget. -/
theorem exists_twoPositionL2Operator_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : HasAmplitudeDerivativeBound b (2 * (d + 1)) M),
        HasAmplitudeDerivativeBound b (2 * (d + 1) + n) H →
        ∀ (f : L²), MemFourierSobolev (n : ℝ) f →
        let v := twoPositionL2Operator hd R b hb hs M hM f
        MemFourierSobolev (n : ℝ) v ∧
          fourierSobolevNorm (n : ℝ) v ≤ C *
            (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨fixedBoxAmplitudeConstant d R * max 0 M,
      mul_nonneg (fixedBoxAmplitudeConstant_nonneg d R) (le_max_left _ _), ?_⟩
    intro b hb hs H hM _hH f _hf
    obtain ⟨hm, he⟩ := twoPositionL2Operator_zero_all_data hd R b hb hs M hM f
    refine ⟨by simpa only [Nat.cast_zero] using hm, ?_⟩
    simpa only [Nat.cast_zero, fourierSobolevNorm_zero] using he.trans
      (lowBudget_mul_le_tame _ M H ‖f‖ (fixedBoxAmplitudeConstant_nonneg d R) (norm_nonneg f))
  · obtain ⟨C, hC, htest⟩ :=
      exists_twoPositionL2Operator_integer_tame_constant hd R n (Nat.pos_of_ne_zero hn) M
    refine ⟨C, hC, ?_⟩
    intro b hb hs H hM hH f hf
    exact fourierSobolev_operator_bound_of_compactSmooth_nat
      (twoPositionL2Operator hd R b hb hs M hM) n (n : ℝ) C (max 1 H)
      (htest b hb hs H hM hH) f hf

/-- The same all-data Hⁿ estimate for the literal Hilbert adjoint in
`app:ch_regular_base:eq:fio-input`. The original amplitude's budgets suffice;
no separate estimate or support assumption for a proposed adjoint is needed. -/
theorem exists_twoPositionL2Operator_adjoint_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : HasAmplitudeDerivativeBound b (2 * (d + 1)) M),
        HasAmplitudeDerivativeBound b (2 * (d + 1) + n) H →
        ∀ (f : L²), MemFourierSobolev (n : ℝ) f →
        let v := (twoPositionL2Operator hd R b hb hs M hM).adjoint f
        MemFourierSobolev (n : ℝ) v ∧
          fourierSobolevNorm (n : ℝ) v ≤ C *
            (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨fixedBoxAmplitudeConstant d R * max 0 M,
      mul_nonneg (fixedBoxAmplitudeConstant_nonneg d R) (le_max_left _ _), ?_⟩
    intro b hb hs H hM _hH f _hf
    obtain ⟨hm, he⟩ := twoPositionL2Operator_adjoint_zero_all_data hd R b hb hs M hM f
    refine ⟨by simpa only [Nat.cast_zero] using hm, ?_⟩
    simpa only [Nat.cast_zero, fourierSobolevNorm_zero] using he.trans
      (lowBudget_mul_le_tame _ M H ‖f‖ (fixedBoxAmplitudeConstant_nonneg d R) (norm_nonneg f))
  · obtain ⟨C, hC, htest⟩ := exists_twoPositionL2Operator_adjoint_integer_tame_constant
      hd R n (Nat.pos_of_ne_zero hn) M
    refine ⟨C, hC, ?_⟩
    intro b hb hs H hM hH f hf
    exact fourierSobolev_operator_bound_of_compactSmooth_nat
      (twoPositionL2Operator hd R b hb hs M hM).adjoint n (n : ℝ) C (max 1 H)
      (htest b hb hs H hM hH) f hf

/-- `app:ch_regular_base:eq:fio-input`, order minus one, maps every Hⁿ datum
into Hⁿ⁺¹. This includes `n = 0`. The weighted low shift is `2 * (d + 1) + 1`,
the high shift is `2 * (d + 1) + (n + 1)`, and the high budget multiplies
only the input L² norm. -/
theorem exists_twoPositionL2Operator_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : L²), MemFourierSobolev (n : ℝ) f →
        let v := twoPositionL2Operator hd R b hb hs M
          (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
            (Nat.le_succ _)) f
        MemFourierSobolev ((n : ℝ) + 1) v ∧
          fourierSobolevNorm ((n : ℝ) + 1) v ≤ C *
            (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  by_cases hn : n = 0
  · subst n
    let K := (1 + (d : ℝ) * (1 + 2 * Real.pi)) * fixedBoxAmplitudeConstant d R
    have hK : 0 ≤ K := mul_nonneg (by positivity) (fixedBoxAmplitudeConstant_nonneg d R)
    refine ⟨K * max 0 M, mul_nonneg hK (le_max_left _ _), ?_⟩
    intro b hb hs H hM _hH f _hf
    obtain ⟨hm, he⟩ := twoPositionL2Operator_gain_one_all_data hd R b hb hs M hM f
    refine ⟨by simpa only [Nat.cast_zero, zero_add] using hm, ?_⟩
    simpa only [Nat.cast_zero, zero_add, fourierSobolevNorm_zero] using
      he.trans (lowBudget_mul_le_tame K M H ‖f‖ hK (norm_nonneg f))
  · obtain ⟨C, hC, htest⟩ :=
      exists_twoPositionL2Operator_integer_gain_tame_constant hd R n (Nat.pos_of_ne_zero hn) M
    refine ⟨C, hC, ?_⟩
    intro b hb hs H hM hH f hf
    exact fourierSobolev_operator_bound_of_compactSmooth_nat
      (twoPositionL2Operator hd R b hb hs M
        (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
          (Nat.le_succ _))) n ((n : ℝ) + 1) C (max 1 H)
      (htest b hb hs H hM hH) f hf

/-- The literal adjoint's all-data gain-one estimate in
`app:ch_regular_base:eq:fio-input`, including the L²-to-H¹ endpoint used in
negative-order duality. Constants precede the amplitude and its high budget;
the fixed shifts and both physical cutoffs are preserved. -/
theorem exists_twoPositionL2Operator_adjoint_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : L²), MemFourierSobolev (n : ℝ) f →
        let v := (twoPositionL2Operator hd R b hb hs M
          (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
            (Nat.le_succ _))).adjoint f
        MemFourierSobolev ((n : ℝ) + 1) v ∧
          fourierSobolevNorm ((n : ℝ) + 1) v ≤ C *
            (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  by_cases hn : n = 0
  · subst n
    let K := (1 + (d : ℝ) * (1 + 2 * Real.pi)) * fixedBoxAmplitudeConstant d R
    have hK : 0 ≤ K := mul_nonneg (by positivity) (fixedBoxAmplitudeConstant_nonneg d R)
    refine ⟨K * max 0 M, mul_nonneg hK (le_max_left _ _), ?_⟩
    intro b hb hs H hM _hH f _hf
    obtain ⟨hm, he⟩ := twoPositionL2Operator_adjoint_gain_one_all_data hd R b hb hs M hM f
    refine ⟨by simpa only [Nat.cast_zero, zero_add] using hm, ?_⟩
    simpa only [Nat.cast_zero, zero_add, fourierSobolevNorm_zero] using
      he.trans (lowBudget_mul_le_tame K M H ‖f‖ hK (norm_nonneg f))
  · obtain ⟨C, hC, htest⟩ := exists_twoPositionL2Operator_adjoint_integer_gain_tame_constant
      hd R n (Nat.pos_of_ne_zero hn) M
    refine ⟨C, hC, ?_⟩
    intro b hb hs H hM hH f hf
    exact fourierSobolev_operator_bound_of_compactSmooth_nat
      (twoPositionL2Operator hd R b hb hs M
        (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
          (Nat.le_succ _))).adjoint n ((n : ℝ) + 1) C (max 1 H)
      (htest b hb hs H hM hH) f hf

end JanetCartan.Pseudodifferential
