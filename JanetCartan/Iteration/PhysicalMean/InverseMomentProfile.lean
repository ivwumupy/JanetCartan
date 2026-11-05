module

public import JanetCartan.Iteration.PhysicalMean.CurrentIndividual
public import JanetCartan.Iteration.PhysicalMean.Grades

/-!
# The current inverse preserves the original adjoint moment source budget

The analytic input is exactly the SAME current uncut inverse Sobolev estimate
`app:ch_background:eq:bg-r-inverse`, supplied by the current normal-inverse
producer. The finite convolution below retains the original positive-part
reserve and produces `app:ch_mean_pairs:eq:raw-adjoint-moments` after either
real adjoint theorem. No current inverse, source, or cutoff is selected here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace JanetCartan.PhysicalMean

/-- Insert the actual current-inverse Sobolev estimate into the original
finite moment budget. The constant depends only on the fixed inverse
profile and moment order, never on sample or band count or the source. -/
theorem inverseSource_moment_sum_le {n : ℕ}
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (e : ContinuumRow.OutputL2 n) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (q r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (hinverse : ∀ k, k ≤ q → periodicSobolevNorm k (Q₀ e) ≤
      C k * (periodicSobolevNorm k e + T ^ (k - r₀) * ‖e‖)) :
    (∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * periodicSobolevNorm k (Q₀ e)) ≤
      ((q : ℝ) + 2) * (∑ k ∈ Finset.range (q + 1), C k) *
        ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * periodicSobolevNorm k e := by
  let M := ∑ k ∈ Finset.range (q + 1), C k
  let S := ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * periodicSobolevNorm k e
  have hM : 0 ≤ M := Finset.sum_nonneg (fun k _ ↦ hC k)
  have hCk (k : ℕ) (hk : k ∈ Finset.range (q + 1)) : C k ≤ M :=
    Finset.single_le_sum (fun j _ ↦ hC j) hk
  have hterm (k : ℕ) : 0 ≤ T ^ (q - k - r₀) * periodicSobolevNorm k e :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) (Real.sqrt_nonneg _)
  have hlow : T ^ (q - r₀) * ‖e‖ ≤ S := by
    have h := Finset.single_le_sum (fun k _ ↦ hterm k)
      (show 0 ∈ Finset.range (q + 1) by simp)
    simpa only [Nat.sub_zero, Nat.cast_zero,
      periodicSobolevNorm_zero_eq_periodicL2Norm (Lp.memLp e), periodicL2Norm_coe] using h
  have hk (k : ℕ) (hk : k ∈ Finset.range (q + 1)) :
      T ^ (q - k - r₀) * periodicSobolevNorm k (Q₀ e) ≤
        M * (T ^ (q - k - r₀) * periodicSobolevNorm k e + T ^ (q - r₀) * ‖e‖) := by
    have hq : k ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hgrade := moment_source_scale_product_le hT (zero_le_one.trans hT) le_rfl
      (r₀ := r₀) hq
    calc
      _ ≤ T ^ (q - k - r₀) * (C k * (periodicSobolevNorm k e + T ^ (k - r₀) * ‖e‖)) :=
        mul_le_mul_of_nonneg_left (hinverse k hq) (pow_nonneg (zero_le_one.trans hT) _)
      _ ≤ T ^ (q - k - r₀) * (M * (periodicSobolevNorm k e + T ^ (k - r₀) * ‖e‖)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hT) _)
        exact mul_le_mul_of_nonneg_right (hCk k hk)
          (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) (norm_nonneg _)))
      _ = M * (T ^ (q - k - r₀) * periodicSobolevNorm k e +
          (T ^ (q - k - r₀) * T ^ (k - r₀)) * ‖e‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hgrade (norm_nonneg e))) hM
  calc
    _ ≤ ∑ k ∈ Finset.range (q + 1),
        M * (T ^ (q - k - r₀) * periodicSobolevNorm k e + T ^ (q - r₀) * ‖e‖) :=
      Finset.sum_le_sum hk
    _ = M * (S + ((q : ℝ) + 1) * (T ^ (q - r₀) * ‖e‖)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, S]
    _ ≤ M * (S + ((q : ℝ) + 1) * S) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hlow (show 0 ≤ (q : ℝ) + 1 by positivity))) hM
    _ = _ := by change M * (S + ((q : ℝ) + 1) * S) = ((q : ℝ) + 2) * M * S; ring

/-- Below the original reserve, the SAME current inverse moment budget costs
only `H^q(e)`. At `q = m0` and `r₀ = s0 = 2*m0` this is the precise lower
factor required by `app:ch_mean_pairs:eq:mean-quadratic-low`; no embedding or
additional source derivative is used. -/
theorem inverseSource_low_moment_sum_le {n : ℕ}
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (e : ContinuumRow.OutputL2 n) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (q r₀ : ℕ) (hqr : q ≤ r₀) (T : ℝ)
    (he : e ∈ periodicSobolevLevel n (Euclidean n) q)
    (hinverse : ∀ k, k ≤ q → periodicSobolevNorm k (Q₀ e) ≤
      C k * (periodicSobolevNorm k e + T ^ (k - r₀) * ‖e‖)) :
    (∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) * periodicSobolevNorm k (Q₀ e)) ≤
      2 * (∑ k ∈ Finset.range (q + 1), C k) * periodicSobolevNorm q e := by
  have hmono (k : ℕ) (hk : k ≤ q) : periodicSobolevNorm k e ≤ periodicSobolevNorm q e := by
    simpa only [periodicSobolevSeminorm_eq] using
      (periodicSobolevSeminorm_mono hk ⟨e, he⟩)
  have hl : ‖e‖ ≤ periodicSobolevNorm q e := by
    simpa only [Nat.cast_zero, periodicSobolevNorm_zero_eq_periodicL2Norm (Lp.memLp e),
      periodicL2Norm_coe] using hmono 0 (Nat.zero_le _)
  calc
    _ ≤ ∑ k ∈ Finset.range (q+1), 2*C k*periodicSobolevNorm q e := by
      apply Finset.sum_le_sum
      intro k hk
      have hkq : k ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hk0 : k-r₀ = 0 := by omega
      have hq0 : q-k-r₀ = 0 := by omega
      rw [hq0, pow_zero, one_mul]
      have hi := hinverse k hkq
      rw [hk0, pow_zero, one_mul] at hi
      exact (hi.trans (mul_le_mul_of_nonneg_left (add_le_add (hmono k hkq) hl) (hC k))).trans_eq (by ring)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The exact original source profile survives the SAME current inverse and
finite moment convolution. For an individual field tested at `s=ell+t`, use
`q=s+1=m0+t` and `r₀=s0=2*m0`, giving the sharp lower-factor grade `t-m0`.
The only finite counts are derivative orders, never samples or bands. -/
theorem inverseSource_profile_moment_sum_le {n : ℕ}
    (Q₀ : ContinuumRow.OutputL2 n →L[ℝ] ContinuumRow.OutputL2 n)
    (e : ContinuumRow.OutputL2 n) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (q r₀ : ℕ) {T R : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R) (hTR : T ≤ R)
    (M : ℝ) (hM : 0 ≤ M)
    (hinverse : ∀ k, k ≤ q → periodicSobolevNorm k (Q₀ e) ≤
      C k * (periodicSobolevNorm k e + T ^ (k - r₀) * ‖e‖))
    (hsource : ∀ k, k ≤ q → periodicSobolevNorm k e ≤ M*R^(k-r₀)) :
    (∑ k ∈ Finset.range (q+1), T^(q-k-r₀)*periodicSobolevNorm k (Q₀ e)) ≤
      ((q : ℝ)+2) * (∑ k ∈ Finset.range (q+1), C k) *
        ((q : ℝ)+1) * M * R^(q-r₀) := by
  have hsum : (∑ k ∈ Finset.range (q+1), T^(q-k-r₀)*periodicSobolevNorm k e) ≤
      ((q : ℝ)+1)*M*R^(q-r₀) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (q+1), M*R^(q-r₀) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkq : k ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        calc
          _ ≤ T^(q-k-r₀)*(M*R^(k-r₀)) :=
            mul_le_mul_of_nonneg_left (hsource k hkq) (pow_nonneg (zero_le_one.trans hT) _)
          _ = M*(T^(q-k-r₀)*R^(k-r₀)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (moment_source_scale_product_le hR (zero_le_one.trans hT) hTR hkq) hM
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring
  exact ((inverseSource_moment_sum_le Q₀ e C hC q r₀ hT hinverse).trans
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ ↦ hC k)))).trans_eq (by ring)

end JanetCartan.PhysicalMean
