module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.TameZero
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.GainOne

/-!
# One-high gain-one estimates at integer orders

The order-minus-one case of `app:ch_regular_base:eq:fio-input` follows from
the actual first-output-derivative amplitude and the order-zero tame estimate.
All physical masks and the `2π` derivative multiplier are retained.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_regular_base:eq:fio-input`: at every integer output index `n+1`
above one, the actual order-minus-one operator gains a derivative with one
high weighted symbol budget. The low budget is fixed at `2*(d+1)+1`,
and the high budget is `2*(d+1)+(n+1)`. -/
theorem exists_twoPositionL2Operator_integer_gain_tame_constant
    (hd : 0 < d) (R : ℝ) (n : ℕ) (hn : 0 < n) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u),
        let f := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
        let v := twoPositionL2Operator hd R b hb hs M
          (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
            (Nat.le_succ _)) f
        MemFourierSobolev ((n : ℝ) + 1) v ∧
          fourierSobolevNorm ((n : ℝ) + 1) v ≤ C *
            (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  let P : ℝ := 1 + 2 * Real.pi
  have hP : 1 ≤ P := by dsimp [P]; linarith [Real.pi_pos]
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  obtain ⟨C₀, hC₀, hzero⟩ := exists_twoPositionL2Operator_integer_tame_constant hd R n hn M
  obtain ⟨C₁, hC₁, hone⟩ := exists_twoPositionL2Operator_integer_tame_constant hd R n hn (P * M)
  refine ⟨C₀ + (d : ℝ) * C₁ * P, by positivity, ?_⟩
  intro b hb hs H hM hH u hu hus
  let f : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
  let hbase := amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
    (Nat.le_succ (2 * (d + 1)))
  let v := twoPositionL2Operator hd R b hb hs M hbase f
  have hhigh : HasAmplitudeDerivativeBound b (2 * (d + 1) + n) H :=
    amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hH) (by omega)
  have hv := hzero b hb hs H hbase hhigh u hu hus
  let w := fun i ↦ twoPositionL2Operator hd R (outputDerivativeAmplitude b i)
    (contDiff_uncurry_outputDerivativeAmplitude hb i)
    (supportedInCenteredBox_outputDerivativeAmplitude b R hs i) (P * M)
    (hasAmplitudeDerivativeBound_outputDerivativeAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ M hM) f
  have hwhigh (i : Fin d) :
      HasAmplitudeDerivativeBound (outputDerivativeAmplitude b i) (2 * (d + 1) + n) (P * H) := by
    apply hasAmplitudeDerivativeBound_outputDerivativeAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id))
    simpa only [Nat.add_assoc] using hH
  have hwbound := fun i ↦ hone (outputDerivativeAmplitude b i)
    (contDiff_uncurry_outputDerivativeAmplitude hb i)
    (supportedInCenteredBox_outputDerivativeAmplitude b R hs i) (P * H)
    (hasAmplitudeDerivativeBound_outputDerivativeAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ M hM)
    (hwhigh i) u hu hus
  have hw (i : Fin d) : HasEuclideanL2CoordinateDerivative i v (w i) := by
    simp only [HasEuclideanL2CoordinateDerivative, euclideanCoordinateDerivative,
      EuclideanSpace.basisFun_apply]
    exact twoPositionL2Operator_lineDeriv_outputDerivativeAmplitude hd R b hb hs M hM i u hu hus
  have hmax : max 1 (P * H) ≤ P * max 1 H := max_le
    (hP.trans (le_mul_of_one_le_right hP0 (le_max_left _ _)))
    (mul_le_mul_of_nonneg_left (le_max_right _ _) hP0)
  let Q := fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖
  have hwnorm (i : Fin d) : fourierSobolevNorm (n : ℝ) (w i) ≤ C₁ * P * Q := by
    calc
      _ ≤ C₁ * (fourierSobolevNorm (n : ℝ) f + max 1 (P * H) * ‖f‖) := (hwbound i).2
      _ ≤ C₁ * (P * fourierSobolevNorm (n : ℝ) f + P * max 1 H * ‖f‖) := by
        apply mul_le_mul_of_nonneg_left _ hC₁
        exact add_le_add
          (le_mul_of_one_le_left (fourierSobolevNorm_nonneg _ _) hP)
          (mul_le_mul_of_nonneg_right hmax (norm_nonneg _))
      _ = _ := by dsimp [Q]; ring
  refine ⟨hv.1.of_coordinateDerivatives (by positivity) (fun i ↦ (hwbound i).1) hw, ?_⟩
  calc
    _ ≤ fourierSobolevNorm (n : ℝ) v + ∑ i, fourierSobolevNorm (n : ℝ) (w i) :=
      fourierSobolevNorm_le_coordinateDerivatives (by positivity) hv.1
        (fun i ↦ (hwbound i).1) hw
    _ ≤ C₀ * Q + ∑ _i : Fin d, C₁ * P * Q :=
      add_le_add hv.2 (Finset.sum_le_sum fun i _ ↦ hwnorm i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The literal Hilbert adjoint satisfies the same one-high gain-one estimate
at integer orders, from the original amplitude budgets alone, as required by
`app:ch_regular_base:eq:fio-input`. -/
theorem exists_twoPositionL2Operator_adjoint_integer_gain_tame_constant
    (hd : 0 < d) (R : ℝ) (n : ℕ) (hn : 0 < n) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u),
        let f := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
        let v := (twoPositionL2Operator hd R b hb hs M
          (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted hM)
            (Nat.le_succ _))).adjoint f
        MemFourierSobolev ((n : ℝ) + 1) v ∧
          fourierSobolevNorm ((n : ℝ) + 1) v ≤ C *
            (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, he⟩ := exists_twoPositionL2Operator_integer_gain_tame_constant hd R n hn M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH u hu hus
  have hrev (N : ℕ) (A : ℝ)
      (hA : ∀ ξ is, is.length ≤ N → ∀ z,
        (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A) :
      ∀ ξ is, is.length ≤ N → ∀ z,
        (1 + ‖ξ‖) * ‖euclideanCoordinateDerivList is (adjointAmplitude b ξ) z‖ ≤ A := by
    intro ξ is his z
    rw [euclideanCoordinateDerivList_adjointAmplitude (b := b)
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)), norm_star]
    exact hA ξ _ (by simpa using his) _
  dsimp only
  rw [twoPositionL2Operator_adjoint]
  exact he (adjointAmplitude b) (contDiff_adjointAmplitude hb)
    (supportedInCenteredBox_adjointAmplitude hs) H (hrev _ _ hM) (hrev _ _ hH) u hu hus

end JanetCartan.Pseudodifferential
