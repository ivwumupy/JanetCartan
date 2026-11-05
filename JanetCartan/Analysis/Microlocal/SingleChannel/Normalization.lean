module

public import JanetCartan.Analysis.Microlocal.NormalComparison.FrequencyNormalization

/-!
# The extra half power in a single channel

The exact scalar identity in `app:ch_osc:prop:osc-channel`. The spatial slice
has dimension `d` and the physical channel has dimension `d + 1`.
-/

@[expose] public noncomputable section

namespace JanetCartan.NormalComparison

/-- The normalization in `app:ch_osc:prop:osc-channel` is precisely the slice
normalization times `sqrt (K / (2π))`. -/
theorem normalOperatorScale_succ (d : ℕ) {K : ℝ} (hK : 0 < K) :
    normalOperatorScale (d + 1) K =
      Real.sqrt (K / (2 * Real.pi)) * normalOperatorScale d K := by
  have hb : 0 < K / (2 * Real.pi) := div_pos hK (by positivity)
  unfold normalOperatorScale
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]
  congr 1
  push_cast
  ring

/-- Squaring the extra normalization gives the exact linear frequency loss
in `app:ch_osc:prop:osc-channel`. -/
theorem singleChannel_extraScale_sq {K : ℝ} (hK : 0 ≤ K) :
    Real.sqrt (K / (2 * Real.pi)) ^ 2 = K / (2 * Real.pi) :=
  Real.sq_sqrt (div_nonneg hK (by positivity))

end JanetCartan.NormalComparison
