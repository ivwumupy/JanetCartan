module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Scalar raw-cutoff estimate
The pointwise inequality used in `main:eq:linear-two-errors`, before integrating
carrier energy or summing auxiliary Fourier energy. -/

@[expose] public noncomputable section

namespace JanetCartan.RawCutoffBounds

/-- `app:ch_background:defn:bg-mixed`: a squared contraction equal to one on
the inner band has a tail controlled by the Bessel weight. -/
theorem squaredMask_tail_le {K r m : ℝ} (hK : 0 < K) (hm : m ∈ Set.Icc (0 : ℝ) 1)
    (hone : r ≤ K → m = 1) (s : ℕ) :
    |1 - m ^ 2| ≤ (K ^ s)⁻¹ * Real.sqrt (1 + r ^ 2) ^ s := by
  have hw : 0 ≤ Real.sqrt (1 + r ^ 2) ^ s := by positivity
  by_cases hr : r ≤ K
  · simp [hone hr, mul_nonneg (inv_nonneg.mpr (pow_nonneg hK.le _)) hw]
  · have hkr : K ≤ Real.sqrt (1 + r ^ 2) := by
      apply (Real.le_sqrt hK.le (by positivity)).mpr
      have : K < r := lt_of_not_ge hr
      nlinarith
    have hpow := pow_le_pow_left₀ hK.le hkr s
    have hlow : 1 ≤ (K ^ s)⁻¹ * Real.sqrt (1 + r ^ 2) ^ s := by
      apply (le_inv_mul_iff₀ (pow_pos hK s)).mpr
      simpa using hpow
    apply le_trans _ hlow
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg m, hm.1, hm.2]

/-- The integer Bessel multiplier is precisely `(1+r²)^(s/2)`
(`app:ch_background:defn:bg-mixed`). -/
theorem sqrt_pow_eq_rpow (r : ℝ) (s : ℕ) :
    Real.sqrt (1 + r ^ 2) ^ s = (1 + r ^ 2) ^ ((s : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

end JanetCartan.RawCutoffBounds
