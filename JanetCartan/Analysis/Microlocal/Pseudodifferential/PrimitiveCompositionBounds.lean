module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.PlaneWaveBounds

/-!
# Composition budgets from primitive source symbol bounds

For `app:ch_regular_base:thm:actual-calculus`, all derivatives of the source
mask and incoming plane wave are estimated from the separate primitive jets.
Only `n` derivatives of each primitive are used in the source mass of order `n`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace JanetCartan.Pseudodifferential
variable {V : Type} {F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:thm:actual-calculus`: the plane-wave-weighted product
is smooth through precisely the requested source order. -/
theorem contDiff_symbolPlaneWave_smul (a : V → F) (b : V → V → ℂ)
    (η : V) (n : ℕ) (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n (fun y ↦ b y η)) :
    ContDiff ℝ n (fun y ↦ symbolPlaneWave b η y • a y) := by
  have hp : ContDiff ℝ n (fun y : V ↦ (Real.fourierChar ⟪η, y⟫ : ℂ)) :=
    (contDiff_fourierChar.comp (innerSL ℝ η).contDiff).of_le
    (show (n : ℕ∞ω) ≤ ∞ by simp)
  simp only [symbolPlaneWave, Circle.smul_def]
  exact (hp.smul hb).smul ha

/-- `app:ch_regular_base:thm:actual-calculus`: a finite source jet estimate
for the plane-wave-weighted primitive product. The incoming frequency loss is
at most the source derivative count `n`. -/
theorem norm_iteratedFDeriv_symbolPlaneWave_smul_le
    (a : V → F) (b : V → V → ℂ) (η ξ y : V) (m l n j : ℕ) (hj : j ≤ n)
    (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n (fun z ↦ b z η))
    (B C : ℝ) (hB : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun z ↦ b z η) y‖ ≤
      B * (1 + ‖η‖) ^ l)
    (hC : ∀ i ≤ n, ‖iteratedFDeriv ℝ i a y‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    ‖iteratedFDeriv ℝ j (fun z ↦ symbolPlaneWave b η z • a z) y‖ ≤
      (2 ^ n * (1 + 2 * Real.pi) ^ n * (2 ^ n * B * C)) *
        (1 + ‖η‖) ^ (n + l) * (1 + ‖ξ‖) ^ m := by
  have hp : ContDiff ℝ n (fun z : V ↦ (Real.fourierChar ⟪η, z⟫ : ℂ)) :=
    (contDiff_fourierChar.comp (innerSL ℝ η).contDiff).of_le (by simp)
  have hphase (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun z : V ↦ (Real.fourierChar ⟪η, z⟫ : ℂ)) y‖ ≤
        (1 + 2 * Real.pi) ^ n * (1 + ‖η‖) ^ n := by
    apply (norm_iteratedFDeriv_planeWave_le η y i).trans
    rw [← mul_pow]
    calc
      _ ≤ ((1 + 2 * Real.pi) * (1 + ‖η‖)) ^ i := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [Real.pi_pos, norm_nonneg η]
      _ ≤ _ := pow_le_pow_right₀ (by nlinarith [Real.pi_pos, norm_nonneg η]) hi
  have hprod (i : ℕ) (hi : i ≤ n) := norm_iteratedFDeriv_smul_le_uniform
    (fun z ↦ b z η) a n i hi hb ha y
    (B * (1 + ‖η‖) ^ l) (C * (1 + ‖ξ‖) ^ m) hB hC
  have hh := norm_iteratedFDeriv_smul_le_uniform
    (fun z : V ↦ (Real.fourierChar ⟪η, z⟫ : ℂ)) (fun z ↦ b z η • a z)
    n j hj hp (hb.smul ha) y ((1 + 2 * Real.pi) ^ n * (1 + ‖η‖) ^ n)
    (2 ^ n * (B * (1 + ‖η‖) ^ l) * (C * (1 + ‖ξ‖) ^ m)) hphase hprod
  simpa only [symbolPlaneWave, Circle.smul_def, smul_eq_mul, smul_smul] using
    hh.trans_eq (by ring)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- `app:ch_regular_base:thm:actual-calculus`: the explicit composition mass
constant retains every derivative of the actual compact source mask. -/
def compositionSourceBound (χ : V → ℂ) (n : ℕ) (B C : ℝ) : ℝ :=
  sourceLeibnizBudget χ (fun _ ↦ 1) n *
    (2 ^ n * (1 + 2 * Real.pi) ^ n * (2 ^ n * B * C))

/-- `app:ch_regular_base:thm:actual-calculus`: nonnegative primitive bounds give
a nonnegative explicit composition constant. -/
theorem compositionSourceBound_nonneg (χ : V → ℂ) (n : ℕ) (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) : 0 ≤ compositionSourceBound χ n B C := by
  have hs : 0 ≤ sourceLeibnizBudget χ (fun _ ↦ 1) n := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (integral_nonneg (fun _ ↦ norm_nonneg _)))
      zero_le_one
  unfold compositionSourceBound
  positivity

/-- `app:ch_regular_base:thm:actual-calculus`: separate pointwise source symbol
bounds imply the composition mass budget, including the incoming plane wave.
There is no assumed estimate for a product or for an oscillatory integral. -/
theorem sourceDerivativeMass_composition_le
    (a : V → V → V → F) (b : V → V → ℂ) (χ : V → ℂ)
    (x ξ η : V) (m l n : ℕ)
    (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ)
    (ha : ContDiff ℝ n (fun y ↦ a x y ξ))
    (hb : ContDiff ℝ n (fun y ↦ b y η)) (B C : ℝ)
    (hB : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i (fun z ↦ b z η) y‖ ≤
      B * (1 + ‖η‖) ^ l)
    (hC : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i (fun z ↦ a x z ξ) y‖ ≤
      C * (1 + ‖ξ‖) ^ m) :
    sourceDerivativeMass (fun y ↦ symbolPlaneWave b η y • (χ y • a x y ξ)) n ≤
      compositionSourceBound χ n B C * (1 + ‖η‖) ^ (n + l) * (1 + ‖ξ‖) ^ m := by
  let D := (2 ^ n * (1 + 2 * Real.pi) ^ n * (2 ^ n * B * C)) *
    (1 + ‖η‖) ^ (n + l) * (1 + ‖ξ‖) ^ m
  have hh := sourceDerivativeMass_smul_le χ (fun y ↦ symbolPlaneWave b η y • a x y ξ)
    n hχ hχc (contDiff_symbolPlaneWave_smul _ b η n ha hb) (fun _ ↦ 1 * D)
    (fun j hj y ↦ by
      simpa only [one_mul] using norm_iteratedFDeriv_symbolPlaneWave_smul_le
        (fun y ↦ a x y ξ) b η ξ y m l n j hj ha hb B C
        (fun i hi ↦ hB i hi y) (fun i hi ↦ hC i hi y))
  rw [sourceLeibnizBudget_mul] at hh
  simp_rw [smul_comm (χ _) (symbolPlaneWave b η _)] at hh
  exact hh.trans_eq (by dsimp [D, compositionSourceBound]; ring)
end JanetCartan.Pseudodifferential
