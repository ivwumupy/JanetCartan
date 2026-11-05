module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale

/-! # The Bessel inverse symbol
The symbol of `⟨D⟩⁻¹` in `app:ch_background:defn:bg-row`, with the unit-torus
physical frequencies of `app:not:fourier`. Used by the actual L² construction.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumRow

variable {n : ℕ}

/-- The order minus one symbol in `app:ch_background:defn:bg-row`. -/
def periodicBesselSymbol (k : Fin n → ℤ) : ℝ :=
  (Real.sqrt (1 + frequencyNorm k ^ 2))⁻¹

/-- The symbol is real and positive (`app:not:fourier`). -/
theorem periodicBesselSymbol_pos (k : Fin n → ℤ) : 0 < periodicBesselSymbol k := by
  unfold periodicBesselSymbol
  positivity

/-- The Bessel inverse is a contraction multiplier (`app:ch_background:defn:bg-row`). -/
theorem periodicBesselSymbol_le_one (k : Fin n → ℤ) : periodicBesselSymbol k ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg (frequencyNorm k)])

/-- Reality is preserved because the symbol is even (`app:not:fourier`). -/
@[simp] theorem periodicBesselSymbol_neg (k : Fin n → ℤ) :
    periodicBesselSymbol (-k) = periodicBesselSymbol k := by
  have h : (WithLp.toLp 2 (fun i ↦ ((-k) i : ℝ)) : EuclideanSpace ℝ (Fin n)) =
      -(WithLp.toLp 2 (fun i ↦ (k i : ℝ))) := by ext i; simp
  simp only [periodicBesselSymbol, frequencyNorm, h, norm_neg]

/-- The square-root formula is the exponent minus one half convention
(`app:not:fourier`). -/
theorem periodicBesselSymbol_eq_rpow (k : Fin n → ℤ) :
    periodicBesselSymbol k = (1 + frequencyNorm k ^ 2) ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  rfl

/-- The multiplier cancels exactly one Sobolev weight
(`app:ch_background:defn:bg-row`), including order zero. -/
theorem periodicSobolevWeight_succ_mul_bessel (s : ℕ) (k : Fin n → ℤ) :
    periodicSobolevWeight (s + 1) k * periodicBesselSymbol k =
      periodicSobolevWeight s k := by
  unfold periodicSobolevWeight periodicBesselSymbol
  rw [pow_succ, mul_inv_cancel_right₀ (by positivity)]

end JanetCartan.ContinuumRow
