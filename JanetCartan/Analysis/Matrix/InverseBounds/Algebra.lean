module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Quantitative derivatives of inversion in a normed algebra

The coefficient estimate used for fixed-gap matrix inverses in
`app:lem:elementary-interpolation-jets`. Multiplication need not commute.
-/

@[expose] public noncomputable section

open scoped ContDiff Nat
open Set ContinuousLinearMap

namespace JanetCartan

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [HasSummableGeomSeries A]

/-- `app:lem:elementary-interpolation-jets`: inversion is smooth on the units. -/
theorem contDiffOn_ringInverse_units {N : ℕ∞ω} :
    ContDiffOn ℝ N (Ring.inverse : A → A) {a | IsUnit a} := by
  rintro a ⟨u, rfl⟩
  exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt

/-- `app:lem:elementary-interpolation-jets`: the order `r` coefficient of inversion
is bounded by `r! ‖a⁻¹‖^(r+1)`. This uses ordered multiplication throughout. -/
theorem norm_iteratedFDeriv_ringInverse_le (r : ℕ) {a : A} (ha : IsUnit a) :
    ‖iteratedFDeriv ℝ r (Ring.inverse : A → A) a‖ ≤
      (r.factorial : ℝ) * ‖Ring.inverse a‖ ^ (r + 1) := by
  let U : Set A := {a | IsUnit a}
  have hU : IsOpen U := Units.isOpen
  have huniq : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hdiff : ContDiffOn ℝ ∞ (Ring.inverse : A → A) U :=
    contDiffOn_ringInverse_units
  have hderiv : EqOn (fderivWithin ℝ (Ring.inverse : A → A) U)
      (fun a ↦ -mulLeftRight ℝ A (Ring.inverse a) (Ring.inverse a)) U := by
    rintro a ⟨u, rfl⟩
    rw [fderivWithin_of_isOpen hU u.isUnit, fderiv_inverse]
    simp only [Ring.inverse_unit]
  rw [← iteratedFDerivWithin_of_isOpen r hU ha]
  induction r using Nat.case_strong_induction_on with
  | hz => simp
  | hi n ih =>
    calc
      ‖iteratedFDerivWithin ℝ (n + 1) (Ring.inverse : A → A) U a‖ =
          ‖iteratedFDerivWithin ℝ n (fderivWithin ℝ (Ring.inverse : A → A) U) U a‖ := by
        rw [norm_iteratedFDerivWithin_fderivWithin huniq ha]
      _ = ‖iteratedFDerivWithin ℝ n
          (fun b ↦ mulLeftRight ℝ A (Ring.inverse b) (Ring.inverse b)) U a‖ := by
        rw [iteratedFDerivWithin_congr hderiv ha]
        change ‖iteratedFDerivWithin ℝ n
          (-(fun b ↦ mulLeftRight ℝ A (Ring.inverse b) (Ring.inverse b))) U a‖ = _
        rw [iteratedFDerivWithin_neg_apply huniq ha, norm_neg]
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (Ring.inverse : A → A) U a‖ *
          ‖iteratedFDerivWithin ℝ (n - i) (Ring.inverse : A → A) U a‖ :=
        (mulLeftRight ℝ A).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
          hdiff hdiff huniq ha (by simp) (opNorm_mulLeftRight_le ℝ A)
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (i.factorial * ‖Ring.inverse a‖ ^ (i + 1)) *
          ((n - i).factorial * ‖Ring.inverse a‖ ^ (n - i + 1)) := by
        gcongr with i hi
        · exact ih i (Finset.mem_range_succ_iff.mp hi)
        · exact ih (n - i) (Nat.sub_le _ _)
      _ = ∑ _i ∈ Finset.range (n + 1), (n.factorial : ℝ) *
          ‖Ring.inverse a‖ ^ (n + 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
        have hc : (n.choose i : ℝ) * i.factorial * (n - i).factorial = n.factorial := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
        calc
          _ = ((n.choose i : ℝ) * i.factorial * (n - i).factorial) *
              (‖Ring.inverse a‖ ^ (i + 1) * ‖Ring.inverse a‖ ^ (n - i + 1)) := by ring
          _ = _ := by rw [hc, ← pow_add]; congr 2; omega
      _ = _ := by simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, mul_assoc]

/-- `app:lem:elementary-interpolation-jets`: one bound for all coefficient derivatives
through order `r`, depending only on the inverse bound. -/
theorem norm_iteratedFDeriv_ringInverse_le_uniform {r i : ℕ} (hi : i ≤ r)
    {a : A} (ha : IsUnit a) {B : ℝ} (hB : ‖Ring.inverse a‖ ≤ B) :
    ‖iteratedFDeriv ℝ i (Ring.inverse : A → A) a‖ ≤
      (r.factorial : ℝ) * max 1 B ^ (r + 1) := by
  apply (norm_iteratedFDeriv_ringInverse_le i ha).trans
  apply mul_le_mul
  · exact_mod_cast Nat.factorial_le hi
  · exact (pow_le_pow_left₀ (norm_nonneg _) (hB.trans (le_max_right _ _)) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (Nat.add_le_add_right hi 1))
  · positivity
  · positivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:lem:elementary-interpolation-jets`: an explicit finite-order inversion
bound. The only input derivatives are the orders `1,…,r`. This polynomial
estimate precedes the interpolation step needed for the one-high tame bound. -/
theorem norm_iteratedFDerivWithin_ringInverse_comp_le {f : E → A} {s : Set E}
    {r : ℕ} (hf : ContDiffOn ℝ r f s) (hs : UniqueDiffOn ℝ s)
    (hu : ∀ x ∈ s, IsUnit (f x)) {x : E} (hx : x ∈ s)
    {B D : ℝ} (hB : ‖Ring.inverse (f x)‖ ≤ B)
    (hD : ∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ D ^ i) :
    ‖iteratedFDerivWithin ℝ r (fun y ↦ Ring.inverse (f y)) s x‖ ≤
      (r.factorial : ℝ) * ((r.factorial : ℝ) * max 1 B ^ (r + 1)) * D ^ r := by
  apply norm_iteratedFDerivWithin_comp_le contDiffOn_ringInverse_units hf le_rfl
    Units.isOpen.uniqueDiffOn hs hu hx _ hD
  intro i hi
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := (Ring.inverse : A → A))
    i Units.isOpen (hu x hx)]
  exact norm_iteratedFDeriv_ringInverse_le_uniform hi (hu x hx) hB

end JanetCartan
