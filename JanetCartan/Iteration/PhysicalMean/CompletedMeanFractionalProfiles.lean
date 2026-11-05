module
public import JanetCartan.Iteration.PhysicalPairs.FractionalSize

/-!
# The mean has the exact physical exponent at every real order

The consumer is the actual original-data Schwartz mean and the EVERY real
`r ≥ 0` clause of `main:eq:mean-size`. Reuse the existing physical `2πξ`
Fourier-weight split at the actual scale `R`: the high-frequency factor
`R ^ (r - ⌈r⌉₊)` cancels the extra integer derivative. This is a deduction
from integer profiles, not yet their actual original-data instantiation.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open scoped SchwartzMap
namespace JanetCartan.PhysicalMean
open PhysicalPairs.FractionalSize

/-- Lossless real-order mean estimate from integer estimates of the SAME real
Schwartz field. The existing coefficient `cost D r = D 0 + D ⌈r⌉₊` is independent
of the history and frequency whenever `D` is; no extra threshold is selected
(`main:eq:mean-size`). -/
theorem physicalMean_real_profile_of_integer {n N : ℕ}
    (V : 𝓢(Euclidean n, Euclidean N)) (D : ℕ → ℝ) (R : ℝ) (hR : 1 ≤ R)
    (h : ∀ k : ℕ, normAt k V ≤ D k * R^k)
    (r : ℝ) (hr : 0 ≤ r) : normAt r V ≤ cost D r * R^r := by
  let k := ⌈r⌉₊
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hzero : normAt 0 V ≤ D 0 := by simpa only [Nat.cast_zero,pow_zero,mul_one] using h 0
  have hcancel : R^(r-(k : ℝ)) * R^k = R^r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hRpos]
    congr 1
    ring
  calc
    normAt r V ≤ R^r * normAt 0 V + R^(r-k) * normAt k V :=
      split hRpos hr (Nat.le_ceil r) V
    _ ≤ R^r * D 0 + R^(r-k) * (D k * R^k) :=
      add_le_add (mul_le_mul_of_nonneg_left hzero (Real.rpow_nonneg hRpos.le _))
        (mul_le_mul_of_nonneg_left (h k) (Real.rpow_nonneg hRpos.le _))
    _ = D 0 * R^r + D k * (R^(r-k) * R^k) := by ring
    _ = (D 0 + D k) * R^r := by rw [hcancel]; ring
    _ = cost D r * R^r := rfl

end JanetCartan.PhysicalMean
end
#print axioms JanetCartan.PhysicalMean.physicalMean_real_profile_of_integer
