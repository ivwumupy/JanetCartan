module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.FrequencyIntegration
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Noncomparable.SymbolBounds
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Shells

/-!
# Measure growth and fixed shell thresholds

Scalar bookkeeping for `app:ch_regular:eq:chain-tail`. Three frequency carriers
are measured at the input normalization, whereas the decay uses the larger
physical radius. Fixed real orders are allowed to be negative, and the smaller
frequency radius may equal one.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Pointwise
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
open Retarded.KernelDecay Retarded.KernelSobolev
variable {n : ℕ}

/-- A primitive normalized carrier contained in a dilation has the expected
`n`-dimensional measure growth. This supplies each of the three frequency
volume factors in `norm_shellOutputIntegral_le` (`app:ch_regular:eq:chain-tail`). -/
theorem volume_real_le_dilate {K B : Set (Euclidean n)} (hB : IsCompact B)
    {t : ℝ} (ht : 0 ≤ t) (hK : K ⊆ t • B) :
    volume.real K ≤ t ^ n * volume.real B := by
  apply (measureReal_mono hK (hB.smul t).measure_lt_top.ne).trans_eq
  simp only [Measure.real_def, Measure.addHaar_smul_of_nonneg volume ht,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht _)]
  simp [Euclidean, finrank_euclideanSpace]

/-- The three normalized carrier volumes cancel the three input Jacobians,
leaving exactly `R^(3*n)`. The carriers need not have comparable radii
(`app:ch_regular:eq:chain-tail`). -/
theorem three_frequency_volume_le {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R)
    {Kξ Kη Kζ Bξ Bη Bζ : Set (Euclidean n)}
    (hξ : IsCompact Bξ) (hη : IsCompact Bη) (hζ : IsCompact Bζ)
    (hsξ : Kξ ⊆ (R / ρ) • Bξ) (hsη : Kη ⊆ (R / ρ) • Bη)
    (hsζ : Kζ ⊆ (R / ρ) • Bζ) :
    ρ ^ (3 * n) * (volume.real Kξ * volume.real Kη * volume.real Kζ) ≤
      R ^ (3 * n) * (volume.real Bξ * volume.real Bη * volume.real Bζ) := by
  have ht := div_nonneg hR hρ.le
  have hi := volume_real_le_dilate hξ ht hsξ
  have hj := volume_real_le_dilate hη ht hsη
  have hk := volume_real_le_dilate hζ ht hsζ
  have hprod := mul_le_mul (mul_le_mul hi hj measureReal_nonneg (by positivity)) hk
    measureReal_nonneg (by positivity)
  apply (mul_le_mul_of_nonneg_left hprod (pow_nonneg hρ.le _)).trans_eq
  rw [show 3 * n = n + n + n by omega]
  simp only [pow_add, div_pow]
  field_simp

/-- Orders at three independent physical radii (full symbol, input mask,
output mask) have a uniform larger-radius majorant. Negative orders and the
bounded shoulder `σ = 1` are included. This is the order specialization of
`norm_shellOutputIntegral_le` (`app:ch_regular:eq:chain-tail`). -/
theorem three_symbol_orders_le {σA σi σo R : ℝ}
    (hA : 1 ≤ σA) (hi : 1 ≤ σi) (ho : 1 ≤ σo)
    (hAR : σA ≤ R) (hiR : σi ≤ R) (hoR : σo ≤ R) (sA si so : ℝ) :
    σA ^ sA * σi ^ si * σo ^ so ≤ R ^ (max 0 sA + max 0 si + max 0 so) := by
  have hR : 0 < R := zero_lt_one.trans_le (hA.trans hAR)
  rw [Real.rpow_add hR, Real.rpow_add hR]
  exact mul_le_mul
    (mul_le_mul (shell_symbol_order_le hA hAR sA) (shell_symbol_order_le hi hiR si)
      (Real.rpow_nonneg (zero_le_one.trans hi) _) (Real.rpow_nonneg hR.le _))
    (shell_symbol_order_le ho hoR so) (Real.rpow_nonneg (zero_le_one.trans ho) _)
    (mul_nonneg (Real.rpow_nonneg hR.le _) (Real.rpow_nonneg hR.le _))

/-- Combine all three Fourier volumes, the output differentiation cost, and
the fixed real symbol orders. The output complement includes the identity,
so its order is the positive part of `so`. This is the scalar input for the
actual kernel family in `exists_regularizedShellKernel_dyadic_bounds`
(`app:ch_regular:eq:chain-tail`). -/
theorem three_frequency_size_le {ρ R σA σi σo : ℝ}
    (hρ : 0 < ρ) (hR : 1 ≤ R)
    (hA : 1 ≤ σA) (hi : 1 ≤ σi) (ho : 1 ≤ σo)
    (hAR : σA ≤ R) (hiR : σi ≤ R) (hoR : σo ≤ R)
    {Kξ Kη Kζ Bξ Bη Bζ : Set (Euclidean n)}
    (hξ : IsCompact Bξ) (hη : IsCompact Bη) (hζ : IsCompact Bζ)
    (hsξ : Kξ ⊆ (R / ρ) • Bξ) (hsη : Kη ⊆ (R / ρ) • Bη)
    (hsζ : Kζ ⊆ (R / ρ) • Bζ) (sA si so : ℝ) (m : ℕ) :
    (ρ ^ (3 * n) * (volume.real Kξ * volume.real Kη * volume.real Kζ)) * R ^ m *
      (σA ^ sA * σi ^ si * σo ^ (max 0 so)) ≤
      (volume.real Bξ * volume.real Bη * volume.real Bζ) *
        R ^ ((3 * n + m : ℕ) + max 0 sA + max 0 si + max 0 so : ℝ) := by
  have hR0 := zero_lt_one.trans_le hR
  have hv := three_frequency_volume_le hρ hR0.le hξ hη hζ hsξ hsη hsζ
  have hs := three_symbol_orders_le hA hi ho hAR hiR hoR sA si (max 0 so)
  simp only [← max_assoc, max_self] at hs
  apply (mul_le_mul (mul_le_mul_of_nonneg_right hv (pow_nonneg hR0.le m)) hs
    (by positivity) (by positivity)).trans_eq
  simp only [Real.rpow_add hR0, Real.rpow_natCast, pow_add]
  ring

/-- A fixed integer threshold above the real dimension/order exponent yields
the existing summable shell weight. It does not enlarge the power of `ρ` or
the amplitude grade offset when requested accuracy `q` increases
(`app:ch_regular:eq:chain-tail`). -/
theorem real_shell_power_le_dyadicWeight {ρ L p : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (a q k : ℕ) (hp : p ≤ (a : ℝ)) :
    ((2 : ℝ) ^ k * ρ) ^ p * (L / ((2 : ℝ) ^ k * ρ)) ^ (q + a + 1) ≤
      ρ ^ p * dyadicShellWeight a q (L / ρ) k := by
  have ht : (0 : ℝ) < 2 ^ k := by positivity
  have he : L / ((2 : ℝ) ^ k * ρ) = (L / ρ) / (2 : ℝ) ^ k := by ring
  rw [Real.mul_rpow ht.le hρ.le, he]
  have hb : ((2 : ℝ) ^ k) ^ p ≤ ((2 : ℝ) ^ k) ^ a := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hp
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb
    (Real.rpow_nonneg hρ.le _)) (pow_nonneg (by positivity) _)).trans_eq
  unfold dyadicShellWeight
  ring

/-- The larger-radius shell powers are summable after a fixed threshold above
all dimension, symbol, and output orders (`app:ch_regular:eq:chain-tail`). -/
theorem summable_real_shell_power {ρ L p : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hLρ : L ≤ ρ) (a q : ℕ) (hp : p ≤ (a : ℝ)) :
    Summable (fun k : ℕ => ((2 : ℝ) ^ k * ρ) ^ p *
      (L / ((2 : ℝ) ^ k * ρ)) ^ (q + a + 1)) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => real_shell_power_le_dyadicWeight hρ hL a q k hp)
  exact (summable_dyadicShellWeight a q (div_nonneg hL hρ.le)
    ((div_le_one hρ).mpr hLρ)).mul_left (ρ ^ p)

/-- Summing the scalar majorants leaves the requested `(L/ρ)^q`, with fixed
power `p` independent of accuracy. The concrete shell-integral assembly uses
this after `three_frequency_volume_le` and `three_symbol_orders_le`
(`app:ch_regular:eq:chain-tail`). -/
theorem tsum_real_shell_power_le {ρ L p : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hLρ : L ≤ ρ) (a q : ℕ) (hp : p ≤ (a : ℝ)) :
    (∑' k : ℕ, ((2 : ℝ) ^ k * ρ) ^ p * (L / ((2 : ℝ) ^ k * ρ)) ^ (q + a + 1)) ≤
      2 * ρ ^ p * (L / ρ) ^ q := by
  have hθ := div_nonneg hL hρ.le
  have hθ' := (div_le_one hρ).mpr hLρ
  calc
    _ ≤ ∑' k, ρ ^ p * dyadicShellWeight a q (L / ρ) k :=
      (summable_real_shell_power hρ hL hLρ a q hp).tsum_le_tsum
        (fun k => real_shell_power_le_dyadicWeight hρ hL a q k hp)
        ((summable_dyadicShellWeight a q hθ hθ').mul_left _)
    _ = ρ ^ p * ∑' k, dyadicShellWeight a q (L / ρ) k := tsum_mul_left
    _ ≤ ρ ^ p * (2 * (L / ρ) ^ q) :=
      mul_le_mul_of_nonneg_left (tsum_dyadicShellWeight_le a q hθ hθ')
        (Real.rpow_nonneg hρ.le _)
    _ = _ := by ring

end JanetCartan.FiniteChain.Graph.KernelEstimates.Noncomparable
