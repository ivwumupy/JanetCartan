module

public import JanetCartan.Iteration.PhysicalMean.Precision

/-!
# The revised source derivative grades

These are the exact positive-part inequalities used after the ORIGINAL
sampled operator estimates in Steps 2, 3 and 6 of
`app:ch_mean_pairs:prop:canonical-estimates`. In particular the quadratic
profile retains `R^(s-s₀)_+`, not the insufficient `R^(s+1-s₀)_+`.
No operator or successful Picard estimate is assumed or produced here.
-/

@[expose] public noncomputable section

namespace JanetCartan.PhysicalMean

/-- Two reserve expenditures combine without consuming the reserve twice
(`new:eq:plus-subadditive`). -/
theorem sourceGrade_add_le (a b r₀ : ℕ) : (a - r₀) + (b - r₀) ≤ a + b - r₀ := by
  omega

/-- The exact exponent inequality at the even source order `s₀=2m₀`
(`new:lem:exponent-inequality`). The two hypotheses retain the asymmetric
choice of the smaller differentiated factor. -/
theorem quadratic_source_exponent_le {s i j m₀ : ℕ}
    (hij : i + j ≤ s) (hj : 2 * j ≤ s) :
    (s - i - j - 2 * m₀) + (i - 2 * m₀) + (j - m₀) ≤ s - 2 * m₀ := by
  omega

/-- The literal product of coefficient, adjoint-moment, source, and
smaller-factor powers is bounded by the revised quadratic source grade.
Thus no extra power of the fine cutoff or frequency is introduced in Step 6
(`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem quadratic_source_scale_product_le
    {R T : ℝ} (hR : 1 ≤ R) (hT : 0 ≤ T) (hTR : T ≤ R)
    {c r t k i m₀ : ℕ} (hik : i ≤ k) (hkr : k ≤ r) (htr : t ≤ r) :
    T ^ (c + r - k - 2 * m₀) * T ^ (k - i - 2 * m₀) *
      R ^ (i - 2 * m₀) * R ^ (t - m₀) ≤ R ^ (c + r + t - 2 * m₀) := by
  have hexp : (c + r - k - 2 * m₀) + (k - i - 2 * m₀) +
      (i - 2 * m₀) + (t - m₀) ≤ c + r + t - 2 * m₀ := by
    have hmerge := sourceGrade_add_le (c + r - k) (k - i) (2 * m₀)
    have hmain := quadratic_source_exponent_le (s := c + r + t) (i := i) (j := t)
      (m₀ := m₀) (by omega) (by omega)
    omega
  calc
    _ ≤ R ^ (c + r - k - 2 * m₀) * R ^ (k - i - 2 * m₀) *
        R ^ (i - 2 * m₀) * R ^ (t - m₀) := by
      gcongr
    _ = R ^ ((c + r - k - 2 * m₀) + (k - i - 2 * m₀) +
        (i - 2 * m₀) + (t - m₀)) := by simp only [pow_add]
    _ ≤ _ := pow_le_pow_right₀ hR hexp

/-- Physical measurement derivatives and the FULL high forward branch
spend the source reserve jointly, not twice. The branch phase count is
bounded by the high derivative order (`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem coefficient_branch_scale_product_le {T : ℝ} (hT : 1 ≤ T)
    {c r k s₀ : ℕ} (hkr : k ≤ r) :
    T^(c-s₀)*T^(r-k-s₀) ≤ T^(c+r-k-s₀) := by
  rw [← pow_add]
  apply pow_le_pow_right₀ hT
  have hh := sourceGrade_add_le c (r-k) s₀
  omega

/-- Summing the exact aggregate moment keeps the sharp final quadratic
source grade. The count is only the finite derivative budget `k+1`, never
a sample or shell count. This is the numerical final step after applying
the constructed balanced native cross row (`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem balanced_source_moment_sum_le
    {R T M Z h : ℝ} (hR : 1 ≤ R) (hT : 0 ≤ T) (hTR : T ≤ R)
    (hM : 0 ≤ M) (hZ : 0 ≤ Z)
    {c r t k m₀ : ℕ} (hkr : k ≤ r) (htr : t ≤ r) :
    T^(c+r-k-2*m₀) * (M*h*∑ i ∈ Finset.range (k+1), T^(k-i-2*m₀)*R^(i-2*m₀)) *
      (Z*h*R^(t-m₀)) ≤ ((k : ℝ)+1)*M*Z*h^2*R^(c+r+t-2*m₀) := by
  have hp : 0 ≤ M*Z*h^2 := by positivity
  calc
    _ = M*Z*h^2 * ∑ i ∈ Finset.range (k+1),
        T^(c+r-k-2*m₀)*T^(k-i-2*m₀)*R^(i-2*m₀)*R^(t-m₀) := by
      simp_rw [show ∀ i : ℕ,
        T^(c+r-k-2*m₀)*T^(k-i-2*m₀)*R^(i-2*m₀)*R^(t-m₀) =
          T^(c+r-k-2*m₀)*(T^(k-i-2*m₀)*R^(i-2*m₀))*R^(t-m₀) by intro i; ring]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ ≤ M*Z*h^2 * ∑ _i ∈ Finset.range (k+1), R^(c+r+t-2*m₀) := by
      apply mul_le_mul_of_nonneg_left _ hp
      apply Finset.sum_le_sum
      intro i hi
      exact quadratic_source_scale_product_le hR hT hTR
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hkr htr
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

/-- The moment grade convolution stays at its stated source order, before
summing the finitely many derivative terms
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem moment_source_scale_product_le
    {R T : ℝ} (hR : 1 ≤ R) (hT : 0 ≤ T) (hTR : T ≤ R)
    {q i r₀ : ℕ} (hi : i ≤ q) :
    T ^ (q - i - r₀) * R ^ (i - r₀) ≤ R ^ (q - r₀) := by
  calc
    _ ≤ R ^ (q - i - r₀) * R ^ (i - r₀) := by gcongr
    _ = R ^ ((q - i - r₀) + (i - r₀)) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ hR (by have := sourceGrade_add_le (q-i) i r₀; omega)

end JanetCartan.PhysicalMean
