module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Fixed-order compression of a reserved envelope scale

At one total derivative order, the reserved profiles in
`app:ch_response:eq:fixed-factor-transfer` can be supplied to the original
finite-jet near-carrier estimates using a smaller scale. Natural subtraction
is essential: low derivative orders have size one. The consumers are the
finite-jet elliptic and characteristic envelope applications in the normalized
inverse construction; this arithmetic does not assert their analytic inputs.
-/

@[expose] public noncomputable section

namespace JanetCartan.FixedDomainInverse

/-- Effective scale for total order `m` and retained reserve `R`.
It equals one throughout the low-order plateau (`app:ch_response:eq:fixed-factor-transfer`). -/
def reservedEnvelopeScale (K : ℝ) (m R : ℕ) : ℝ :=
  K ^ (((m - R : ℕ) : ℝ) / (m : ℝ))

/-- The compressed envelope scale is admissible, including total order zero. -/
theorem one_le_reservedEnvelopeScale {K : ℝ} (hK : 1 ≤ K) (m R : ℕ) :
    1 ≤ reservedEnvelopeScale K m R :=
  Real.one_le_rpow hK (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Compression never increases the original scale, so its original
upper frequency bound is retained by every near-carrier application. -/
theorem reservedEnvelopeScale_le {K : ℝ} (hK : 1 ≤ K) (m R : ℕ) :
    reservedEnvelopeScale K m R ≤ K := by
  by_cases hm : m = 0
  · simpa [reservedEnvelopeScale, hm] using hK
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm)
  calc
    _ ≤ K ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hK
      apply (div_le_iff₀ hmpos).mpr
      simp
    _ = K := Real.rpow_one K

/-- Convert a finite power of the compressed scale to the original scale. -/
theorem reservedEnvelopeScale_pow {K : ℝ} (hK : 1 ≤ K) (m R j : ℕ) :
    reservedEnvelopeScale K m R ^ j =
      K ^ ((((m - R : ℕ) : ℝ) / (m : ℝ)) * (j : ℝ)) := by
  rw [reservedEnvelopeScale, ← Real.rpow_natCast,
    ← Real.rpow_mul (zero_le_one.trans hK)]

/-- Compression preserves the exact naturally truncated top-order profile. -/
theorem reservedEnvelopeScale_pow_top {K : ℝ} (hK : 1 ≤ K) (m R : ℕ) :
    reservedEnvelopeScale K m R ^ m = K ^ (m - R) := by
  by_cases hm : m = 0
  · simp [hm]
  rw [reservedEnvelopeScale_pow hK, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hm),
    Real.rpow_natCast]

private theorem sub_reserve_le_compressed_exponent {j m R : ℕ} (hjm : j ≤ m) :
    ((j - R : ℕ) : ℝ) ≤ (((m - R : ℕ) : ℝ) / (m : ℝ)) * (j : ℝ) := by
  by_cases hmR : m ≤ R
  · simp [Nat.sub_eq_zero_of_le hmR, Nat.sub_eq_zero_of_le (hjm.trans hmR)]
  have hRm : R ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  by_cases hjR : j ≤ R
  · simp only [Nat.sub_eq_zero_of_le hjR, Nat.cast_zero]
    positivity
  have hRj : R ≤ j := by omega
  rw [Nat.cast_sub hRj, Nat.cast_sub hRm, div_mul_eq_mul_div]
  apply (le_div_iff₀ hmpos).mpr
  have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  nlinarith [mul_le_mul_of_nonneg_left hjm' hR]

/-- Every lower reserved jet fits the same effective scale at total order `m`.
In particular, this does not replace natural subtraction by a negative power. -/
theorem reserved_power_le_reservedEnvelopeScale {K : ℝ} (hK : 1 ≤ K)
    {j m : ℕ} (hjm : j ≤ m) (R : ℕ) :
    K ^ (j - R) ≤ reservedEnvelopeScale K m R ^ j := by
  rw [reservedEnvelopeScale_pow hK, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hK (sub_reserve_le_compressed_exponent hjm)

/-- The finite symbol-jet reserve used by the original diagonal PDO theorem
also fits the compressed scale. The extra fixed reserve keeps its first low
derivatives on the size-one plateau (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem reserved_symbol_power_le_reservedEnvelopeScale {K : ℝ} (hK : 1 ≤ K)
    {j q m R Rorig : ℕ} (hj : j ≤ q + m + 2) (hR : R + q + 4 ≤ Rorig) :
    K ^ (j + 2 - Rorig) ≤
      reservedEnvelopeScale K m R ^ (j + 2 - (q + 3)) := by
  have hmid : j + 1 - (q + 3) ≤ m := by omega
  calc
    _ ≤ K ^ ((j + 1 - (q + 3)) - R) := by
      apply pow_le_pow_right₀ hK
      omega
    _ ≤ reservedEnvelopeScale K m R ^ (j + 1 - (q + 3)) :=
      reserved_power_le_reservedEnvelopeScale hK hmid R
    _ ≤ _ := by
      apply pow_le_pow_right₀ (one_le_reservedEnvelopeScale hK m R)
      omega

/-- The original phase-jet reserve compresses on the same finite range as
the symbol jets, without changing the low-order plateau. -/
theorem reserved_phase_power_le_reservedEnvelopeScale {K : ℝ} (hK : 1 ≤ K)
    {j q m R Rorig : ℕ} (hj : j ≤ q + m + 2) (hR : R + q + 4 ≤ Rorig) :
    K ^ (j - Rorig) ≤ reservedEnvelopeScale K m R ^ (j - (q + 3)) := by
  calc
    _ ≤ K ^ ((j - (q + 3)) - R) := by
      apply pow_le_pow_right₀ hK
      omega
    _ ≤ _ := reserved_power_le_reservedEnvelopeScale hK (by omega) R

end JanetCartan.FixedDomainInverse
