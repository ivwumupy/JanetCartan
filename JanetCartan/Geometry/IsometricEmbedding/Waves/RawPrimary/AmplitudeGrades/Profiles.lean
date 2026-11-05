module

public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget.Algebra

/-!
# Transfer of the retained primary budgets

For `app:ch_waves:thm:wkb`, the actual corrected-family producer exports
one-high bounds with reserve fourteen in the original immersion and initial
scalar. This file transfers precisely that kind of bound to a derivative
profile. It also records how the additional `r_par + 2` allowance pays for
the two subsequent derivatives. The ambient reconstruction and polynomial
estimates must still supply their actual budgets; none is a record field.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.RawPrimary.AmplitudeGrades

variable {E G X V W Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Two-input version of `app:cor:fixed-profile-transfer`, used for the
literal phase/leading/correction bounds retained by
`exists_finite_actual_corrected_family`. The constants contain neither the
fields nor the varying scale. In that application `d = 14`. -/
theorem profile_of_two_input_budget
    {K : Set E} {I : Set G} {J : Set X}
    {F : E → V} {r : G → W} {f : X → Y}
    {RF Rr d ν : ℕ} {L : ℝ} {AF Ar C : ℕ → ℝ}
    (hF : HasDerivativeProfile K F RF L AF)
    (hr : HasDerivativeProfile I r Rr L Ar)
    (hL : 1 ≤ L) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hC : ∀ j, 0 ≤ C j) (hRF : d + ν ≤ RF) (hRr : d + ν ≤ Rr)
    (hbudget : ∀ j, cNorm J j f ≤
      C j * (1 + cNorm K (j + d) F + cNorm I (j + d) r)) :
    HasDerivativeProfile J f ν L
      (fun j ↦ C j * (1 + AF (j + d) + Ar (j + d))) := by
  intro j
  have hFj : cNorm K (j + d) F ≤ AF (j + d) * L ^ (j - ν) :=
    (hF (j + d)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : j + d - RF ≤ j - ν)) (hAF _))
  have hrj : cNorm I (j + d) r ≤ Ar (j + d) * L ^ (j - ν) :=
    (hr (j + d)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : j + d - Rr ≤ j - ν)) (hAr _))
  exact (hbudget j).trans ((mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (one_le_pow₀ hL : 1 ≤ L ^ (j - ν)) hFj) hrj)
      (hC j)).trans_eq (by ring))

/-- A retained joint profile bounds each actual jet, including points on the
closed working ball (`app:ch_waves:eq:individual-grading`). Smoothness on a
neighborhood prevents any use of the unbounded-supremum convention. -/
theorem norm_iteratedFDeriv_le_profile
    {J Ω : Set X} (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    {f : X → Y} (hf : ContDiffOn ℝ ∞ f Ω)
    {ν : ℕ} {L : ℝ} {C : ℕ → ℝ} (hp : HasDerivativeProfile J f ν L C)
    (j : ℕ) {x : X} (hx : x ∈ J) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C j * L ^ (j - ν) :=
  (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
    (fun y hy ↦ (hf.contDiffAt (hΩ.mem_nhds (hJΩ hy))).of_le (by simp)) hx le_rfl).trans
      (hp j)

/-- The manuscript's additional `r_par+2` allowance covers two further
derivatives after the reserve-fourteen producer, without altering its
reserve (`app:ch_waves:thm:wkb`). This inequality is used for reconstruction
and the differentiated WKB polynomial, with `q ≤ 2` and `k ≤ r_par`. -/
theorem norm_iteratedFDeriv_le_profile_with_allowance
    {J Ω : Set X} (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    {f : X → Y} (hf : ContDiffOn ℝ ∞ f Ω)
    {rpar j k q : ℕ} {L : ℝ} {C : ℕ → ℝ}
    (hp : HasDerivativeProfile J f (rpar + 2) L C)
    (hL : 1 ≤ L) (hC : ∀ i, 0 ≤ C i) (hk : k ≤ rpar) (hq : q ≤ 2)
    {x : X} (hx : x ∈ J) :
    ‖iteratedFDeriv ℝ (j + k + q) f x‖ ≤ C (j + k + q) * L ^ j :=
  (norm_iteratedFDeriv_le_profile hJ hΩ hJΩ hf hp _ hx).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : j + k + q - (rpar + 2) ≤ j)) (hC _))

end JanetCartan.RawPrimary.AmplitudeGrades
