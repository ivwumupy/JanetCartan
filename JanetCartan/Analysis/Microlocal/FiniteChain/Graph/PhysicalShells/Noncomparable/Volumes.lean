module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.Powers
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Retaining the small graph carrier in physical pair bounds

The consumer is the independent pair summation in `app:ch_regular:eq:chain-tail`.
Only the symbol scale is clipped below at one. The carrier radius remains its
actual, possibly arbitrarily small, physical radius. Primitive dilation
inclusions are supplied by `jc-graph-physical-cutoff-geometry`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Pointwise
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
open KernelEstimates.Noncomparable
variable {n : ℕ}

/-- Cancel the three input-normalization Jacobians without enlarging any
physical frequency carrier. In particular the graph factor `sξ^n` survives
as `sξ` tends to zero (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem independent_frequency_volume_le {ρ sξ sη sζ : ℝ}
    (hρ : 0 < ρ) (hξ : 0 ≤ sξ) (hη : 0 ≤ sη) (hζ : 0 ≤ sζ)
    {Kξ Kη Kζ Bξ Bη Bζ : Set (Euclidean n)}
    (hBξ : IsCompact Bξ) (hBη : IsCompact Bη) (hBζ : IsCompact Bζ)
    (hsξ : Kξ ⊆ (sξ / ρ) • Bξ) (hsη : Kη ⊆ (sη / ρ) • Bη)
    (hsζ : Kζ ⊆ (sζ / ρ) • Bζ) :
    ρ ^ (3 * n) * (volume.real Kξ * volume.real Kη * volume.real Kζ) ≤
      (sξ ^ n * sη ^ n * sζ ^ n) *
        (volume.real Bξ * volume.real Bη * volume.real Bζ) := by
  have hi := volume_real_le_dilate hBξ (div_nonneg hξ hρ.le) hsξ
  have hj := volume_real_le_dilate hBη (div_nonneg hη hρ.le) hsη
  have hk := volume_real_le_dilate hBζ (div_nonneg hζ hρ.le) hsζ
  have hprod := mul_le_mul (mul_le_mul hi hj measureReal_nonneg (by positivity)) hk
    measureReal_nonneg (by positivity)
  apply (mul_le_mul_of_nonneg_left hprod (pow_nonneg hρ.le _)).trans_eq
  rw [show 3 * n = n + n + n by omega]
  simp only [pow_add, div_pow]
  field_simp

/-- Fixed real symbol orders use a scale bounded below by one. Negative
orders therefore do not introduce an artificial singularity on shrinking
graph annuli (`app:ch_regular:eq:high-amplitude`). -/
theorem clipped_symbol_order_le {s R : ℝ} (hR : 1 ≤ R) (hs : s ≤ R) (order : ℝ) :
    (max 1 s) ^ order ≤ R ^ max 0 order :=
  Retarded.KernelDecay.shell_symbol_order_le (le_max_left _ _) (max_le hR hs) order

/-- Below unit radius all fixed symbol orders, including negative ones,
have exactly unit scale (`app:ch_regular:eq:high-amplitude`). -/
theorem clipped_symbol_order_eq_one {s : ℝ} (hs : s ≤ 1) (order : ℝ) :
    (max 1 s) ^ order = 1 := by
  rw [max_eq_left hs, Real.one_rpow]

/-- Simultaneous Fourier volumes, output derivatives, and arbitrary real
orders, retaining the small graph-volume factor. The complement's identity
term forces the positive part of the output order. The fixed profiles and
offsets in the pair estimate multiply this scalar inequality
(`app:ch_regular:eq:chain-tail`). -/
theorem independent_frequency_size_le {ρ sξ sη sζ R : ℝ}
    (hρ : 0 < ρ) (hξ : 0 ≤ sξ) (hη : 0 ≤ sη) (hζ : 0 ≤ sζ)
    (hR : 1 ≤ R) (hξR : sξ ≤ R) (hηR : sη ≤ R) (hζR : sζ ≤ R)
    {Kξ Kη Kζ Bξ Bη Bζ : Set (Euclidean n)}
    (hBξ : IsCompact Bξ) (hBη : IsCompact Bη) (hBζ : IsCompact Bζ)
    (hsξ : Kξ ⊆ (sξ / ρ) • Bξ) (hsη : Kη ⊆ (sη / ρ) • Bη)
    (hsζ : Kζ ⊆ (sζ / ρ) • Bζ) (sA si so : ℝ) (m : ℕ) :
    (ρ ^ (3 * n) * (volume.real Kξ * volume.real Kη * volume.real Kζ)) * R ^ m *
        ((max 1 sξ) ^ sA * (max 1 sη) ^ si * (max 1 sζ) ^ max 0 so) ≤
      (volume.real Bξ * volume.real Bη * volume.real Bζ) *
        (sξ ^ n * sη ^ n * sζ ^ n) *
          R ^ ((m : ℝ) + max 0 sA + max 0 si + max 0 so) := by
  have hR0 := zero_lt_one.trans_le hR
  have hv := independent_frequency_volume_le hρ hξ hη hζ hBξ hBη hBζ hsξ hsη hsζ
  have hs := three_symbol_orders_le (le_max_left 1 sξ) (le_max_left 1 sη)
    (le_max_left 1 sζ) (max_le hR hξR) (max_le hR hηR) (max_le hR hζR)
    sA si (max 0 so)
  simp only [← max_assoc, max_self] at hs
  apply (mul_le_mul (mul_le_mul_of_nonneg_right hv (pow_nonneg hR0.le m)) hs
    (by positivity) (by positivity)).trans_eq
  simp only [Real.rpow_add hR0, Real.rpow_natCast]
  ring

/-- The graph-volume decay near zero is summable in every positive dimension.
The zero-dimensional case must instead use that the actual annuli vanish
(`app:ch_regular:eq:chain-tail`). -/
theorem summable_contracting_radius_volume (hn : 0 < n) :
    Summable (fun j : ℕ => (((2 : ℝ) ^ j)⁻¹) ^ n) := by
  have hbase : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have hlt : (2 : ℝ)⁻¹ ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  convert summable_geometric_of_lt_one hbase hlt using 1
  ext j
  simp only [inv_pow, ← pow_mul, Nat.mul_comm]

/-- Small graph annuli may be summed against an independent summable output
majorant. There is no lower cutoff on the graph frequency
(`app:ch_regular:eq:chain-tail`). -/
theorem summable_contracting_pair_volume (hn : 0 < n)
    {F : ℕ → ℝ} (hF : Summable F) (hF0 : ∀ k, 0 ≤ F k) :
    Summable (fun p : ℕ × ℕ => (((2 : ℝ) ^ p.1)⁻¹) ^ n * F p.2) :=
  (summable_contracting_radius_volume hn).mul_of_nonneg hF (fun _ => by positivity) hF0

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
