module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.RefinedEstimates.PowerSums
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization

/-!
# Fourier and Hilbert estimates for the fixed two-shell refinement

The input is the shared complex `RefinedInput`, with its literal Lebesgue annular
measures. The inverse Fourier field retains the radian normalization of
`RawInputRealization`. The bounds in `app:ch_waves:eq:B-bounds` follow from
measurable uniformly bounded masks and the explicit ceiling `2^J ≤ C * K`.
The Hilbert estimate supplies the input half power for
`app:ch_waves:eq:individual-raw-slice`; it does not assert the physical slice
estimate. Rounded versions discharge the ceiling with `C = 4`.

Consumers are the raw square-partition construction and the raw-primary and
current-canonical constructions. They must supply the actual masks and their
bounds. No identification with the original wide-band spaces is needed here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawInputPartition
open RawInputRealization RawInputHilbert

/-- The explicit dimension/mask constant in `app:ch_waves:eq:B-bounds`.
It contains the literal unit-ball volume and the two-component geometric factor,
and is independent of the number of scales. -/
def refinedFourierConstant (n : ℕ) (M : ℝ) : ℝ :=
  M * Real.sqrt (unitBallVolume n * (1 + (2 : ℝ) ^ n))

/-- Nonnegativity needed when transferring the Fourier bound to a larger
ceiling in `app:ch_waves:eq:B-bounds`. -/
theorem refinedFourierConstant_nonneg (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ refinedFourierConstant n M :=
  mul_nonneg hM (Real.sqrt_nonneg _)

variable {n J : ℕ}

/-- Fourier `L¹` at the actual dyadic ceiling on the fixed two-component
input (`app:ch_waves:eq:B-bounds`). -/
theorem integral_norm_density_refined_le (hn : 1 ≤ n)
    {β : RefinedIndex J → Euclidean (n - 1) → ℂ} (hβ : ∀ i, Measurable (β i))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v : RefinedInput n J) :
    (∫ η, ‖density β v η‖) ≤
      refinedFourierConstant n M * ((2 : ℝ) ^ J) ^ ((n : ℝ) / 2) * ‖v‖ := by
  have hV : 0 ≤ unitBallVolume n := ENNReal.toReal_nonneg
  have hs : (∑ i : RefinedIndex J, (Real.sqrt (refinedRadius i) * M *
      Real.sqrt ((annularMeasure n (refinedRadius i) Set.univ).toReal)) ^ 2) ≤
      M ^ 2 * (unitBallVolume n * (1 + (2 : ℝ) ^ n)) * ((2 : ℝ) ^ J) ^ n := by
    calc
      _ ≤ ∑ i : RefinedIndex J, M ^ 2 * unitBallVolume n * refinedRadius i ^ n :=
        Finset.sum_le_sum (fun i _ ↦ channel_constant_sq_le hn (refinedRadius_pos i).le)
      _ = M ^ 2 * unitBallVolume n * ∑ i : RefinedIndex J, refinedRadius i ^ n :=
        (Finset.mul_sum ..).symm
      _ ≤ M ^ 2 * unitBallVolume n * ((1 + (2 : ℝ) ^ n) * ((2 : ℝ) ^ J) ^ n) :=
        mul_le_mul_of_nonneg_left (sum_refinedRadius_pow_le hn J)
          (mul_nonneg (sq_nonneg _) hV)
      _ = _ := by ring
  have he : Real.sqrt (M ^ 2 * (unitBallVolume n * (1 + (2 : ℝ) ^ n)) *
      ((2 : ℝ) ^ J) ^ n) =
      refinedFourierConstant n M * ((2 : ℝ) ^ J) ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg M),
      Real.sqrt_sq hM0, Real.sqrt_eq_rpow (((2 : ℝ) ^ J) ^ n),
      ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 2 ^ J)]
    dsimp [refinedFourierConstant]
    congr 2
    ring
  exact (integral_norm_density_le hβ hM0 hM v).trans
    ((mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hs) (norm_nonneg _)).trans_eq
      (congrArg (fun t ↦ t * ‖v‖) he))

/-- Fourier `L¹ ≤ C' K^(n/2) ‖v‖` under the explicit ceiling, with `C'`
independent of `J` (`app:ch_waves:eq:B-bounds`). -/
theorem integral_norm_density_refined_ceiling_le (hn : 1 ≤ n)
    {β : RefinedIndex J → Euclidean (n - 1) → ℂ} (hβ : ∀ i, Measurable (β i))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hceil : (2 : ℝ) ^ J ≤ C * K)
    (v : RefinedInput n J) :
    (∫ η, ‖density β v η‖) ≤
      (refinedFourierConstant n M * C ^ ((n : ℝ) / 2)) * K ^ ((n : ℝ) / 2) * ‖v‖ := by
  apply (integral_norm_density_refined_le hn hβ hM0 hM v).trans
  calc
    _ ≤ refinedFourierConstant n M * (C * K) ^ ((n : ℝ) / 2) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hceil (by positivity))
          (refinedFourierConstant_nonneg n hM0)) (norm_nonneg _)
    _ = _ := by rw [Real.mul_rpow hC hK]; ring

/-- Every initial derivative on the refined input obeys the Bernstein bound
in radian Fourier normalization (`app:ch_waves:eq:B-bounds`). -/
theorem norm_iteratedFDeriv_field_refined_le (hn : 1 ≤ n)
    {β : RefinedIndex J → Euclidean (n - 1) → ℂ} (hβ : ∀ i, Measurable (β i))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v : RefinedInput n J) (m : ℕ) (x : Euclidean (n - 1)) :
    ‖iteratedFDeriv ℝ m (field β v) x‖ ≤
      refinedFourierConstant n M * ((2 : ℝ) ^ J) ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖ := by
  have h := (norm_iteratedFDeriv_field_le hβ hM v (by positivity)
    refinedRadius_le_ceiling m x).trans
      (mul_le_mul_of_nonneg_left (integral_norm_density_refined_le hn hβ hM0 hM v)
        (by positivity))
  convert h using 1
  rw [Real.rpow_add (by positivity), Real.rpow_natCast]
  ring

/-- The initial `C^m` bound, in the shared sum-of-suprema convention, on any
set. The explicit constant depends only on `n`, `m`, the mask bound and the
ceiling factor (`app:ch_waves:eq:B-bounds`). -/
theorem cNorm_field_refined_ceiling_le (hn : 1 ≤ n)
    {β : RefinedIndex J → Euclidean (n - 1) → ℂ} (hβ : ∀ i, Measurable (β i))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 1 ≤ K) (hceil : (2 : ℝ) ^ J ≤ C * K)
    (v : RefinedInput n J) (m : ℕ) (s : Set (Euclidean (n - 1))) :
    cNorm s m (field β v) ≤
      (((m + 1 : ℕ) : ℝ) * refinedFourierConstant n M * C ^ ((m : ℝ) + (n : ℝ) / 2)) *
        K ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖ := by
  let B : ℝ := refinedFourierConstant n M * (C * K) ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖
  have hA := refinedFourierConstant_nonneg n hM0
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd : ∀ r ≤ m, ∀ x : Euclidean (n - 1), ‖iteratedFDeriv ℝ r (field β v) x‖ ≤ B := by
    intro r hr x
    apply (norm_iteratedFDeriv_field_refined_le hn hβ hM0 hM v r x).trans
    have he : ((2 : ℝ) ^ J) ^ ((r : ℝ) + (n : ℝ) / 2) ≤
        ((2 : ℝ) ^ J) ^ ((m : ℝ) + (n : ℝ) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
      linarith [show (r : ℝ) ≤ (m : ℝ) from Nat.cast_le.mpr hr]
    have hc : ((2 : ℝ) ^ J) ^ ((m : ℝ) + (n : ℝ) / 2) ≤
        (C * K) ^ ((m : ℝ) + (n : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hceil (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (he.trans hc) hA) (norm_nonneg _)
  calc
    _ ≤ ∑ _r ∈ Finset.range (m + 1), B :=
      cNorm_le_sum_of_bounds (fun _ _ ↦ hB) (fun r hr x _ ↦ hd r hr x)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, B,
        Real.mul_rpow hC (zero_le_one.trans hK)]
      ring

/-- The refined Hilbert synthesis costs only a half power of the ceiling.
The fixed factor `√3` comes from the two-shell radius sum and does not grow
with `J` (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_synthesis_refined_le {M : ℝ}
    {β : RefinedIndex J → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (refinedRadius i)))
    (hM : 0 ≤ M)
    (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (refinedRadius i), ‖β i η‖ ≤ M) :
    ‖synthesis hβ (fun _ ↦ hM) hb‖ ≤ (M * Real.sqrt 3) * Real.sqrt ((2 : ℝ) ^ J) := by
  have hs : (∑ i : RefinedIndex J, refinedRadius i * M ^ 2) ≤
      3 * ((2 : ℝ) ^ J) * M ^ 2 := by
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [pow_one, show (1 : ℝ) + 2 = 3 by norm_num] using
      sum_refinedRadius_pow_le (p := 1) le_rfl J
  calc
    _ ≤ Real.sqrt (∑ i : RefinedIndex J, refinedRadius i * M ^ 2) :=
      norm_synthesis_le (fun i ↦ (refinedRadius_pos i).le) hβ (fun _ ↦ hM) hb
    _ ≤ Real.sqrt (3 * ((2 : ℝ) ^ J) * M ^ 2) := Real.sqrt_le_sqrt hs
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hM]
      ring

/-- The Hilbert input estimate at a continuous ceiling. This is the input
half power used by `app:ch_waves:eq:individual-raw-slice`. -/
theorem norm_synthesis_refined_ceiling_le {M C K : ℝ}
    {β : RefinedIndex J → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (refinedRadius i)))
    (hM : 0 ≤ M)
    (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (refinedRadius i), ‖β i η‖ ≤ M)
    (hC : 0 ≤ C) (hceil : (2 : ℝ) ^ J ≤ C * K) :
    ‖synthesis hβ (fun _ ↦ hM) hb‖ ≤
      (M * Real.sqrt 3 * Real.sqrt C) * Real.sqrt K := by
  calc
    _ ≤ (M * Real.sqrt 3) * Real.sqrt ((2 : ℝ) ^ J) := norm_synthesis_refined_le hβ hM hb
    _ ≤ (M * Real.sqrt 3) * Real.sqrt (C * K) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hceil) (by positivity)
    _ = _ := by rw [Real.sqrt_mul hC]; ring

/-- Fourier `L¹` on the actual rounded partition, with its ceiling premise
discharged by `cutoffCount_plateau` (`app:ch_waves:eq:B-bounds`). -/
theorem integral_norm_density_refined_rounded_le (hn : 1 ≤ n) {K : ℝ} (hK : 1 ≤ K)
    {β : RefinedIndex (cutoffCount K) → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i η, ‖β i η‖ ≤ M) (v : RefinedInput n (cutoffCount K)) :
    (∫ η, ‖density β v η‖) ≤
      (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2)) * K ^ ((n : ℝ) / 2) * ‖v‖ :=
  integral_norm_density_refined_ceiling_le hn hβ hM0 hM (by norm_num)
    (zero_le_one.trans hK) (cutoffCount_ceiling hK) v

/-- Initial `C^m` on the actual rounded partition, with constants independent
of its scale count (`app:ch_waves:eq:B-bounds`). -/
theorem cNorm_field_refined_rounded_le (hn : 1 ≤ n) {K : ℝ} (hK : 1 ≤ K)
    {β : RefinedIndex (cutoffCount K) → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i η, ‖β i η‖ ≤ M) (v : RefinedInput n (cutoffCount K))
    (m : ℕ) (s : Set (Euclidean (n - 1))) :
    cNorm s m (field β v) ≤
      (((m + 1 : ℕ) : ℝ) * refinedFourierConstant n M * 4 ^ ((m : ℝ) + (n : ℝ) / 2)) *
        K ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖ :=
  cNorm_field_refined_ceiling_le hn hβ hM0 hM (by norm_num) hK (cutoffCount_ceiling hK) v m s

/-- Hilbert synthesis on the actual rounded partition costs `C √K`; the
ceiling is proved, not an additional input (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_synthesis_refined_rounded_le {M K : ℝ} (hK : 1 ≤ K)
    {β : RefinedIndex (cutoffCount K) → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n (refinedRadius i)))
    (hM : 0 ≤ M)
    (hb : ∀ i, ∀ᵐ η ∂annularMeasure n (refinedRadius i), ‖β i η‖ ≤ M) :
    ‖synthesis hβ (fun _ ↦ hM) hb‖ ≤
      (M * Real.sqrt 3 * Real.sqrt 4) * Real.sqrt K :=
  norm_synthesis_refined_ceiling_le hβ hM hb (by norm_num) (cutoffCount_ceiling hK)

end JanetCartan.RawInputPartition
