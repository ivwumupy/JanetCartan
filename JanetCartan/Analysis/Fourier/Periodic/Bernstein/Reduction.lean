module

public import JanetCartan.Analysis.ContDiff.Norm.Defs

/-!
# Reduction of Bernstein estimates to one derivative

For `main:lem:history` in paper.tex, an estimate for each successive derivative
supremum gives the sharp power `L ^ (s - r)` for the sum defining `cNorm`.
The analytic one-derivative estimate is an explicit premise here; this module
does not establish it from Fourier support.
-/

@[expose] public noncomputable section

namespace JanetCartan.Bernstein

/-- `main:lem:history`: iteration of a one-step bound for nonnegative derivative sizes.
Only steps between the baseline and the target order are needed. -/
theorem sum_range_le_of_step {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) {r s : ℕ} (hrs : r ≤ s)
    (hstep : ∀ j, r ≤ j → j < s → a (j + 1) ≤ B * L * a j) :
    (∑ j ∈ Finset.range (s + 1), a j) ≤
      (1 + B) ^ (s - r) * L ^ (s - r) * ∑ j ∈ Finset.range (r + 1), a j := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hsum : ∀ k, 0 ≤ ∑ j ∈ Finset.range (k + 1), a j :=
    fun _ ↦ Finset.sum_nonneg (fun j _ ↦ ha j)
  have hterm : ∀ k, a k ≤ ∑ j ∈ Finset.range (k + 1), a j :=
    fun k ↦ Finset.single_le_sum (fun j _ ↦ ha j) (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have haux : ∀ k, r ≤ k → k ≤ s →
      (∑ j ∈ Finset.range (k + 1), a j) ≤
        ((1 + B) * L) ^ (k - r) * ∑ j ∈ Finset.range (r + 1), a j := by
    intro k hrk
    induction k, hrk using Nat.le_induction with
    | base => intro _; simp
    | succ k hrk ih =>
      intro hks
      have hk : k < s := by omega
      have hbound := hstep k hrk hk
      have hsum_step : (∑ j ∈ Finset.range (k + 1 + 1), a j) ≤
          ((1 + B) * L) * ∑ j ∈ Finset.range (k + 1), a j := by
        rw [Finset.sum_range_succ]
        calc
          _ ≤ (∑ j ∈ Finset.range (k + 1), a j) +
              B * L * ∑ j ∈ Finset.range (k + 1), a j :=
            add_le_add le_rfl (hbound.trans (mul_le_mul_of_nonneg_left (hterm k)
              (mul_nonneg hB hL0)))
          _ ≤ ((1 + B) * L) * ∑ j ∈ Finset.range (k + 1), a j := by
            nlinarith [mul_le_mul_of_nonneg_right hL (hsum k)]
      calc
        _ ≤ ((1 + B) * L) * ∑ j ∈ Finset.range (k + 1), a j := hsum_step
        _ ≤ ((1 + B) * L) *
            (((1 + B) * L) ^ (k - r) * ∑ j ∈ Finset.range (r + 1), a j) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity)
        _ = ((1 + B) * L) ^ (k + 1 - r) *
            ∑ j ∈ Finset.range (r + 1), a j := by
          rw [show k + 1 - r = (k - r) + 1 by omega, pow_succ]
          ring
  simpa only [mul_pow] using haux s hrs le_rfl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:history`: convert successive derivative-supremum estimates to the
sharp `C^r` to `C^s` scaling. The one-step analytic estimates remain hypotheses. -/
theorem cNorm_le_of_derivative_sup_step {d : Set E} {f : E → F}
    {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) {r s : ℕ} (hrs : r ≤ s)
    (hstep : ∀ j, r ≤ j → j < s →
      sSup ((fun x ↦ ‖iteratedFDeriv ℝ (j + 1) f x‖) '' d) ≤
        B * L * sSup ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' d)) :
    cNorm d s f ≤ (1 + B) ^ (s - r) * L ^ (s - r) * cNorm d r f := by
  apply sum_range_le_of_step (a := fun j ↦ sSup ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' d))
    _ hB hL hrs hstep
  intro j
  apply Real.sSup_nonneg
  rintro _ ⟨x, _, rfl⟩
  exact norm_nonneg _

/-- `main:lem:history`: a pointwise bound for the derivative of each iterated
Fréchet derivative suffices for the sharp `cNorm` estimate. -/
theorem cNorm_le_of_fderiv_bound {d : Set E} (hd : d.Nonempty) {f : E → F}
    {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) {r s : ℕ} (hrs : r ≤ s)
    (hstep : ∀ j, r ≤ j → j < s → ∀ x ∈ d,
      ‖fderiv ℝ (iteratedFDeriv ℝ j f) x‖ ≤
        B * L * sSup ((fun y ↦ ‖iteratedFDeriv ℝ j f y‖) '' d)) :
    cNorm d s f ≤ (1 + B) ^ (s - r) * L ^ (s - r) * cNorm d r f := by
  apply cNorm_le_of_derivative_sup_step hB hL hrs
  intro j hrj hjs
  apply csSup_le (hd.image _)
  rintro _ ⟨x, hx, rfl⟩
  simpa only [norm_fderiv_iteratedFDeriv] using hstep j hrj hjs x hx

end JanetCartan.Bernstein
