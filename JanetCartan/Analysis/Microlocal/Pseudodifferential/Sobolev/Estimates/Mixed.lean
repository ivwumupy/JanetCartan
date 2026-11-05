module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Basic

/-!
# Mixed amplitude and datum bounds at integer orders

The finite derivative estimate preceding the one-high interpolation step of
`app:ch_regular_base:eq:fio-input`. An amplitude budget of order `μ + j`
multiplies only a datum norm of order `s - j`, with `μ = 2 * (d + 1)`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The mixed sum in the integer proof of `app:ch_regular_base:eq:fio-input`.
The coefficient `B j` is a primitive amplitude budget through order `μ + j`. -/
def mixedAmplitudeSobolevSum (n : ℕ) (B : ℕ → ℝ) (f : Lp ℂ 2 (volume : Measure E)) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), B (n - k) * fourierSobolevNorm (k : ℝ) f

/-- Nonnegativity of the mixed sum in `app:ch_regular_base:eq:fio-input`. -/
theorem mixedAmplitudeSobolevSum_nonneg (n : ℕ) {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (f : Lp ℂ 2 (volume : Measure E)) :
    0 ≤ mixedAmplitudeSobolevSum n B f :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (hB _) (fourierSobolevNorm_nonneg _ _)

private theorem mixed_sum_succ_le (n : ℕ) {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hmono : Monotone B) (f : Lp ℂ 2 (volume : Measure E)) :
    mixedAmplitudeSobolevSum n B f ≤ mixedAmplitudeSobolevSum (n + 1) B f := by
  unfold mixedAmplitudeSobolevSum
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), B (n + 1 - k) * fourierSobolevNorm (k : ℝ) f :=
      Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right
        (hmono (by omega)) (fourierSobolevNorm_nonneg _ _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun k _ _ ↦ mul_nonneg (hB _) (fourierSobolevNorm_nonneg _ _))

private theorem mixed_sum_shift_le (n : ℕ) {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (f : Lp ℂ 2 (volume : Measure E)) :
    mixedAmplitudeSobolevSum n (fun j ↦ 2 * B (j + 1)) f ≤
      2 * mixedAmplitudeSobolevSum (n + 1) B f := by
  unfold mixedAmplitudeSobolevSum
  rw [Finset.mul_sum]
  calc
    _ = ∑ k ∈ Finset.range (n + 1), 2 * (B (n + 1 - k) * fourierSobolevNorm (k : ℝ) f) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      dsimp only
      rw [show n - k + 1 = n + 1 - k by omega]
      ring
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun k _ _ ↦ mul_nonneg (by norm_num)
        (mul_nonneg (hB _) (fourierSobolevNorm_nonneg _ _)))

private theorem mixed_sum_derivative_le (n : ℕ) {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) {f g : Lp ℂ 2 (volume : Measure E)} {i : Fin d}
    (hg : HasEuclideanL2CoordinateDerivative i f g)
    (hf : MemFourierSobolev ((n + 1 : ℕ) : ℝ) f) :
    mixedAmplitudeSobolevSum n B g ≤
      (2 * Real.pi) * mixedAmplitudeSobolevSum (n + 1) B f := by
  unfold mixedAmplitudeSobolevSum
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (2 * Real.pi) * (B (n - k) * fourierSobolevNorm ((k : ℝ) + 1) f) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : (k : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Finset.mem_range.mp hk
      have h := mul_le_mul_of_nonneg_left
        (hg.fourierSobolevNorm_le (by positivity) (hf.mono hkn)) (hB (n - k))
      nlinarith
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.sum_range_succ' (n := n + 1)]
      simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
      exact le_add_of_nonneg_right (mul_nonneg (hB _) (fourierSobolevNorm_nonneg _ _))

/-- Dimension and box constant in the integer mixed estimate for
`app:ch_regular_base:eq:fio-input`; it is independent of amplitude budgets. -/
def integerAmplitudeSobolevConstant (d : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  fixedBoxAmplitudeConstant d R * (1 + (d : ℝ) * (2 + 2 * Real.pi)) ^ n

/-- Nonnegativity of the fixed integer constant in
`app:ch_regular_base:eq:fio-input`. -/
theorem integerAmplitudeSobolevConstant_nonneg (d : ℕ) (R : ℝ) (n : ℕ) :
    0 ≤ integerAmplitudeSobolevConstant d R n :=
  mul_nonneg (fixedBoxAmplitudeConstant_nonneg d R) (by positivity)

/-- `app:ch_regular_base:eq:fio-input` before interpolation: the actual output
belongs to Hⁿ and satisfies the mixed derivative estimate with fixed shift
`μ = 2 * (d + 1)`. The only analytic premises are primitive physical amplitude
bounds, smoothness, and fixed support. -/
theorem twoPositionL2Operator_integer_mixed_bound
    (hd : 0 < d) (R : ℝ) (n : ℕ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hmono : Monotone B)
    (hbudget : ∀ j, j ≤ n → HasAmplitudeDerivativeBound b (2 * (d + 1) + j) (B j))
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    let f : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
    let v := twoPositionL2Operator hd R b hb hs (B 0) (by simpa using hbudget 0 (Nat.zero_le n)) f
    MemFourierSobolev (n : ℝ) v ∧
      fourierSobolevNorm (n : ℝ) v ≤
        integerAmplitudeSobolevConstant d R n * mixedAmplitudeSobolevSum n B f := by
  induction n generalizing b B u with
  | zero =>
    dsimp only
    constructor
    · simp
    · simpa [integerAmplitudeSobolevConstant, mixedAmplitudeSobolevSum, mul_assoc] using
        norm_twoPositionL2Operator_apply_le hd R b hb hs (B 0)
          (by simpa using hbudget 0 (Nat.zero_le 0))
          ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u)
  | succ n ih =>
    let f : Lp ℂ 2 (volume : Measure E) := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
    let hb0 : HasAmplitudeDerivativeBound b (2 * (d + 1)) (B 0) :=
      by simpa using hbudget 0 (by omega)
    let v := twoPositionL2Operator hd R b hb hs (B 0) hb0 f
    let du := fun i ↦ euclideanCoordinateDerivList [i] u
    let hdu := fun i ↦ contDiff_euclideanCoordinateDerivList hu [i]
    let hds := fun i ↦ hasCompactSupport_euclideanCoordinateDerivList hus [i]
    let df : Fin d → Lp ℂ 2 (volume : Measure E) := fun i ↦ ((hdu i).continuous.memLp_of_hasCompactSupport (hds i)).toLp (du i)
    let Bt := fun j ↦ 2 * B (j + 1)
    have hBt : ∀ j, 0 ≤ Bt j := fun j ↦ mul_nonneg (by norm_num) (hB _)
    have hmt : Monotone Bt := fun j k hjk ↦
      mul_le_mul_of_nonneg_left (hmono (Nat.add_le_add_right hjk 1)) (by norm_num)
    have hbt (i : Fin d) (j : ℕ) (hj : j ≤ n) :
        HasAmplitudeDerivativeBound (transferAmplitude b i) (2 * (d + 1) + j) (Bt j) := by
      apply hasAmplitudeDerivativeBound_transferAmplitude b
        (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id))
      simpa only [Nat.add_assoc] using hbudget (j + 1) (by omega)
    let t := fun i ↦ twoPositionL2Operator hd R (transferAmplitude b i)
      (contDiff_uncurry_transferAmplitude hb i)
      (supportedInCenteredBox_transferAmplitude b R hs i) (Bt 0)
      (by simpa using hbt i 0 (Nat.zero_le n)) f
    let w := fun i ↦ t i + twoPositionL2Operator hd R b hb hs (B 0) hb0 (df i)
    have hv := ih b hb hs B hB hmono (fun j hj ↦ hbudget j (by omega)) u hu hus
    have ht := fun i ↦ ih (transferAmplitude b i)
      (contDiff_uncurry_transferAmplitude hb i)
      (supportedInCenteredBox_transferAmplitude b R hs i) Bt hBt hmt (hbt i) u hu hus
    have hud := fun i ↦ ih b hb hs B hB hmono (fun j hj ↦ hbudget j (by omega))
      (du i) (hdu i) (hds i)
    have hwmem (i : Fin d) : MemFourierSobolev (n : ℝ) (w i) :=
      (ht i).1.add (hud i).1
    have hw (i : Fin d) : HasEuclideanL2CoordinateDerivative i v (w i) := by
      have h := twoPositionL2Operator_lineDeriv_transfer hd R b hb hs (B 1)
        (hbudget 1 (by omega)) i u hu hus
      change LineDeriv.lineDerivOp (EuclideanSpace.basisFun (Fin d) ℝ i)
        (v : 𝓢'(E, ℂ)) = (w i : 𝓢'(E, ℂ))
      rw [EuclideanSpace.basisFun_apply]
      change _ = (Lp.toTemperedDistributionCLM ℂ volume 2) (w i)
      dsimp only [w]
      rw [map_add]
      exact h
    have hnorm := fourierSobolevNorm_le_coordinateDerivatives (by positivity) hv.1 hwmem hw
    have hC := integerAmplitudeSobolevConstant_nonneg d R n
    let S := mixedAmplitudeSobolevSum (n + 1) B f
    have hvnorm : fourierSobolevNorm (n : ℝ) v ≤ integerAmplitudeSobolevConstant d R n * S :=
      hv.2.trans (mul_le_mul_of_nonneg_left (mixed_sum_succ_le n hB hmono f) hC)
    have hwnorm (i : Fin d) : fourierSobolevNorm (n : ℝ) (w i) ≤
        integerAmplitudeSobolevConstant d R n * ((2 + 2 * Real.pi) * S) := by
      calc
        _ ≤ fourierSobolevNorm (n : ℝ) (t i) +
            fourierSobolevNorm (n : ℝ) (twoPositionL2Operator hd R b hb hs (B 0) hb0 (df i)) :=
          fourierSobolevNorm_add_le (ht i).1 (hud i).1
        _ ≤ integerAmplitudeSobolevConstant d R n * (2 * S) +
            integerAmplitudeSobolevConstant d R n * ((2 * Real.pi) * S) := by
          apply add_le_add
          · exact (ht i).2.trans (mul_le_mul_of_nonneg_left (mixed_sum_shift_le n hB f) hC)
          · exact (hud i).2.trans (mul_le_mul_of_nonneg_left
              (mixed_sum_derivative_le n hB (hasEuclideanL2CoordinateDerivative_toLp u hu hus i)
                (memFourierSobolev_nat_toLp (n + 1) u hu hus)) hC)
        _ = _ := by ring
    constructor
    · simpa only [Nat.cast_add, Nat.cast_one] using
        hv.1.of_coordinateDerivatives (by positivity) hwmem hw
    · simp only [Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ _ := hnorm
        _ ≤ integerAmplitudeSobolevConstant d R n * S +
            ∑ _i : Fin d, integerAmplitudeSobolevConstant d R n * ((2 + 2 * Real.pi) * S) :=
          add_le_add hvnorm (Finset.sum_le_sum fun i _ ↦ hwnorm i)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            integerAmplitudeSobolevConstant, pow_succ]
          ring

end JanetCartan.Pseudodifferential
