module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Basic
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Oscillation grades from primitive target phase jets

For `app:ch_response:thm:response-literal-transfer`, primitive bounds of order
`P j * R * L^(j-1)` give oscillation bounds of order `R^m` when `1 ≤ L ≤ R`.
The constants use only finitely many entries of `P` and the output order, with
no dependence on the physical frequency or dimension. These are the scalar
Leibniz inputs to the all-order `outputJetAmplitude` estimate in `Grades`.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.ResponseTransfer.LowEnvelope

open JanetCartan.Localization

variable {n : ℕ}

/-- The finite phase profile used in the output-jet estimate of
`app:ch_response:thm:response-literal-transfer`. -/
def outputOscillationGrade (P : ℕ → ℝ) (m : ℕ) : ℝ :=
  m.factorial * (1 + ∑ j ∈ Finset.range (m + 1), P j) ^ m

/-- Nonnegativity of the output oscillation profile in
`app:ch_response:thm:response-literal-transfer`. -/
theorem outputOscillationGrade_nonneg (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (m : ℕ) :
    0 ≤ outputOscillationGrade P m := by
  unfold outputOscillationGrade
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
    (add_nonneg zero_le_one (Finset.sum_nonneg fun j _ ↦ hP j)) _)

private theorem iteratedDeriv_outputUnitOscillation (m : ℕ) :
    iteratedDeriv m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) =
      fun t : ℝ ↦ Complex.I ^ m * Complex.exp ((t : ℂ) * Complex.I) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h : HasDerivAt (fun s : ℝ ↦ Complex.exp ((s : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).cexp
    rw [(HasDerivAt.const_mul (Complex.I ^ m) h).deriv, pow_succ]
    ring

/-- All real derivatives of the unit-frequency oscillation have norm one.
This supplies the outer-function bound in the composition estimate for
`app:ch_response:thm:response-literal-transfer`; no exponential jet bound is
assumed. -/
theorem norm_iteratedFDeriv_outputUnitOscillation (m : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ m (fun s : ℝ ↦ Complex.exp ((s : ℂ) * Complex.I)) t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_outputUnitOscillation]
  simp [norm_pow, Complex.norm_exp_ofReal_mul_I]

/-- Primitive phase jets imply the full Fréchet output oscillation grade in
`app:ch_response:thm:response-literal-transfer`. The physical covector `η`
is fixed, and the grade is independent of it and of `L`, `R`, and dimension. -/
theorem norm_iteratedFDeriv_outputOscillation_le
    (τ : Euclidean n → Euclidean n → ℝ) (η : Euclidean n)
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {L R : ℝ} (hL : 1 ≤ L) (hLR : L ≤ R)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hτj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ P j * R * L ^ (j - 1))
    (m : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ m (phaseOscillation (fun z ↦ τ z η)) x‖ ≤
      outputOscillationGrade P m * R ^ m := by
  let M : ℝ := 1 + ∑ j ∈ Finset.range (m + 1), P j
  have hM : 1 ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ hP j)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hR0 : 0 ≤ R := hL0.trans hLR
  have hphase (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ (M * R) ^ j := by
    have hPM : P j ≤ M := by
      have hs := Finset.single_le_sum (s := Finset.range (m + 1))
        (f := P) (fun i _ ↦ hP i) (show j ∈ Finset.range (m + 1) by simp; omega)
      dsimp [M]
      linarith
    have hPpow : P j ≤ M ^ j :=
      hPM.trans (by simpa using pow_le_pow_right₀ hM hj)
    calc
      _ ≤ P j * R * L ^ (j - 1) := hτj j hj x
      _ ≤ P j * R * R ^ (j - 1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hL0 hLR _) (mul_nonneg (hP j) hR0)
      _ = P j * R ^ j := by
        rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hj]
      _ ≤ M ^ j * R ^ j := mul_le_mul_of_nonneg_right hPpow (pow_nonneg hR0 _)
      _ = (M * R) ^ j := (mul_pow _ _ _).symm
  have hout : ContDiff ℝ ∞ (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) :=
    contDiff_outputOscillation contDiff_id
  have hcomp := norm_iteratedFDeriv_comp_le hout hτ (by simp : (m : ℕ∞ω) ≤ ∞) x
    (C := 1) (D := M * R)
    (fun j _ ↦ (norm_iteratedFDeriv_outputUnitOscillation j (τ x η)).le) hphase
  change ‖iteratedFDeriv ℝ m
    ((fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) ∘ (fun z ↦ τ z η)) x‖ ≤ _
  simpa only [mul_one, mul_pow, mul_assoc, outputOscillationGrade, M] using hcomp

/-- Ordered coordinate derivatives satisfy the same dimension-independent
oscillation profile. This is the scalar input to the output-amplitude Leibniz
estimate in `Grades` for `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_euclideanCoordinateDerivList_outputOscillation_le
    (τ : Euclidean n → Euclidean n → ℝ) (η : Euclidean n)
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {L R : ℝ} (hL : 1 ≤ L) (hLR : L ≤ R)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hτj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ P j * R * L ^ (j - 1))
    (α : List (Fin n)) (x : Euclidean n) :
    ‖AmplitudeBound.euclideanCoordinateDerivList α (phaseOscillation (fun z ↦ τ z η)) x‖ ≤
      outputOscillationGrade P α.length * R ^ α.length :=
  (Pseudodifferential.norm_euclideanCoordinateDerivList_le_iteratedFDeriv
    (contDiff_outputOscillation hτ) α x).trans
      (norm_iteratedFDeriv_outputOscillation_le τ η P hP hL hLR hτ hτj α.length x)

end JanetCartan.ResponseTransfer.LowEnvelope
