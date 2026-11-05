module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Primitive grades of the target phases

These are the phase inputs to the output-amplitude grades used by
`norm_normalMatrixDerivList_forwardDemodulatedKernel` and
`norm_normalMatrixDerivList_reverseDemodulatedKernel` in
`app:ch_response:thm:response-literal-transfer`. The physical covector is retained.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral

variable {n : ℕ}

/-- Primitive target grades of `S` and `φ` give the forward phase profile at
`R = ρ + ‖η‖`, for `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_forwardTargetPhase_le
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (η x : Euclidean n) {ρ L : ℝ} (hρ : 0 ≤ ρ) (hL : 0 ≤ L)
    (PS Pφ : ℕ → ℝ) (hPS : ∀ j, 0 ≤ PS j) (hPφ : ∀ j, 0 ≤ Pφ j)
    (hS : ContDiff ℝ ∞ (fun z ↦ S z η)) (hφ : ContDiff ℝ ∞ φ)
    (hSj : ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ j (fun z ↦ S z η) x‖ ≤
      PS j * ‖η‖ * L ^ (j - 1))
    (hφj : ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ j φ x‖ ≤ Pφ j * L ^ (j - 1))
    (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (fun z ↦ forwardTargetPhase S φ ρ z η) x‖ ≤
      (PS j + Pφ j) * (ρ + ‖η‖) * L ^ (j - 1) := by
  change ‖iteratedFDeriv ℝ j ((fun z ↦ S z η) - (fun z ↦ ρ • φ z)) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (i := j) (x := x) (hS.contDiffAt.of_le (by simp))
      ((hφ.const_smul ρ).contDiffAt.of_le (by simp)),
    iteratedFDeriv_const_smul_apply' (hφ.contDiffAt.of_le (by simp))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun z ↦ S z η) x‖ +
        ρ * ‖iteratedFDeriv ℝ j φ x‖ := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ] using norm_sub_le
        (iteratedFDeriv ℝ j (fun z ↦ S z η) x) (ρ • iteratedFDeriv ℝ j φ x)
    _ ≤ PS j * ‖η‖ * L ^ (j - 1) + ρ * (Pφ j * L ^ (j - 1)) :=
      add_le_add (hSj j hj) (mul_le_mul_of_nonneg_left (hφj j hj) hρ)
    _ ≤ _ := by
      have h₁ := mul_nonneg (mul_nonneg (hPS j) hρ) (pow_nonneg hL (j - 1))
      have h₂ := mul_nonneg (mul_nonneg (hPφ j) (norm_nonneg η))
        (pow_nonneg hL (j - 1))
      nlinarith

/-- The reverse target phase has zero derivatives above order one; its exact
first derivative is the physical frequency gap. This is the affine phase input
for `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_reverseTargetPhase
    (ζ : Euclidean n) (ρ : ℝ) (y η : Euclidean n) (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (fun z ↦ reverseTargetPhase ζ ρ z η) y‖ =
      if j = 1 then ‖η - ρ • ζ‖ else 0 := by
  have he : (fun z ↦ reverseTargetPhase ζ ρ z η) = ⇑(innerSL ℝ (η - ρ • ζ)) := by
    funext z
    exact real_inner_comm _ _
  rw [he]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
    simp only [innerSL_apply_norm, Nat.succ_eq_add_one, Nat.reduceAdd, ite_true]
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ ⇑(innerSL ℝ (η - ρ • ζ)) =
        fun _ ↦ innerSL ℝ (η - ρ • ζ) := by
      funext z
      exact ContinuousLinearMap.fderiv _
    rw [hd, iteratedFDeriv_succ_const]
    simp

/-- A fixed carrier bound gives a phase profile independent of the physical
frequency and `ρ`, at `R = ρ + ‖η‖`, for
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_reverseTargetPhase_le
    (ζ : Euclidean n) (y η : Euclidean n) {ρ L Z : ℝ}
    (hρ : 0 ≤ ρ) (hL : 0 ≤ L) (hζ : ‖ζ‖ ≤ Z) (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (fun z ↦ reverseTargetPhase ζ ρ z η) y‖ ≤
      (1 + Z) * (ρ + ‖η‖) * L ^ (j - 1) := by
  rw [norm_iteratedFDeriv_reverseTargetPhase ζ ρ y η j hj]
  have hZ : 0 ≤ Z := (norm_nonneg ζ).trans hζ
  split_ifs with h
  · subst j
    simp only [Nat.sub_self, pow_zero, mul_one]
    calc
      ‖η - ρ • ζ‖ ≤ ‖η‖ + ‖ρ • ζ‖ := norm_sub_le _ _
      _ = ‖η‖ + ρ * ‖ζ‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
      _ ≤ ‖η‖ + ρ * Z := add_le_add_right (mul_le_mul_of_nonneg_left hζ hρ) _
      _ ≤ _ := by nlinarith [mul_nonneg hZ (norm_nonneg η)]
  · exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hL _)

end JanetCartan.ResponseTransfer.LowEnvelope
