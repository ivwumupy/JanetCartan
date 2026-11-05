module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Scalar
public import Mathlib.MeasureTheory.Function.Holder

/-! # Multipliers on the literal initial-variable carrier space
The carrier part of `app:ch_background:defn:bg-mixed` and
`main:eq:linear-two-errors`. The measure is `dz dη`; both complex quadratures
are retained. The weight assumption is pointwise domination of the transverse
Bessel weight, not an assumed tail bound. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.RawCutoffBounds
open ContinuumRow

variable {n : ℕ}

/-- Bounded real multiplication on the actual complex carrier input, considered
as a real Hilbert space (`app:ch_background:defn:bg-mixed`). -/
def carrierMultiplier (m : Lp ℝ ∞ (carrierMeasure n)) : CarrierL2 n →L[ℝ] CarrierL2 n :=
  (ContinuousLinearMap.lsmul ℝ ℝ).holderL (carrierMeasure n) ∞ 2 2 m

/-- Literal action in initial variables (`app:ch_background:defn:bg-mixed`). -/
theorem carrierMultiplier_coeFn (m : Lp ℝ ∞ (carrierMeasure n)) (h : CarrierL2 n) :
    carrierMultiplier m h =ᵐ[carrierMeasure n] fun x ↦ m x • h x :=
  (ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder m h

/-- The square acts on raw input before the footpoint cutoff
(`app:ch_background:defn:bg-mixed`). -/
def carrierSquaredCutoff (m : Lp ℝ ∞ (carrierMeasure n)) :
    CarrierL2 n →L[ℝ] CarrierL2 n := (carrierMultiplier m).comp (carrierMultiplier m)

/-- Exact squared mask on initial Fourier variables
(`app:ch_background:defn:bg-mixed`). -/
theorem carrierSquaredCutoff_coeFn (m : Lp ℝ ∞ (carrierMeasure n)) (h : CarrierL2 n) :
    carrierSquaredCutoff m h =ᵐ[carrierMeasure n] fun x ↦ (m x) ^ 2 • h x := by
  filter_upwards [carrierMultiplier_coeFn m (carrierMultiplier m h),
    carrierMultiplier_coeFn m h] with x hx hy
  change (carrierMultiplier m (carrierMultiplier m h)) x = _
  rw [hx, hy, smul_smul, pow_two]

/-- The weighted-energy domain in literal initial variables. A producer of the
paper's full `X^s` norm must provide this membership and the comparison of its
weight with the transverse Bessel weight (`app:ch_background:defn:bg-mixed`). -/
def CarrierWeightedMem (w : CarrierVariable n → ℝ) (h : CarrierL2 n) : Prop :=
  MemLp (fun x ↦ w x • h x) 2 (carrierMeasure n)

/-- Weighted carrier norm, used only with explicit weighted-energy membership
(`app:ch_background:defn:bg-mixed`). -/
def carrierWeightedNorm (w : CarrierVariable n → ℝ) (h : CarrierL2 n)
    (hw : CarrierWeightedMem w h) : ℝ := ‖hw.toLp (fun x ↦ w x • h x)‖

/-- `main:eq:linear-two-errors`: the carrier tail is derived from the mask.
The inner-band identity is needed only on the support of the input, allowing
the paper's high-frequency adjoint support. All assumptions are on the literal
initial-variable measure. -/
theorem carrierSquaredCutoff_tail {K : ℝ} (hK : 1 ≤ K) (s : ℕ)
    (m : Lp ℝ ∞ (carrierMeasure n)) (h : CarrierL2 n)
    (hm : ∀ᵐ x ∂carrierMeasure n, m x ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ᵐ x ∂carrierMeasure n, h x ≠ 0 → ‖x.2‖ ≤ K → m x = 1)
    (w : CarrierVariable n → ℝ) (hw : CarrierWeightedMem w h)
    (hweight : ∀ᵐ x ∂carrierMeasure n,
      Real.sqrt (1 + ‖x.2‖ ^ 2) ^ s ≤ w x) :
    ‖h - carrierSquaredCutoff m h‖ ≤ (K ^ s)⁻¹ * carrierWeightedNorm w h hw := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub h (carrierSquaredCutoff m h),
    carrierSquaredCutoff_coeFn m h, hw.coeFn_toLp, hm, hone, hweight]
      with x hsub hcut hweighted hm hone hweight
  rw [hsub, Pi.sub_apply, hcut, hweighted]
  by_cases hz : h x = 0
  · simp [hz]
  · have hp : 0 < K := lt_of_lt_of_le zero_lt_one hK
    have ht := squaredMask_tail_le hp hm (hone hz) s
    have hwpos : 0 ≤ w x := le_trans (by positivity) hweight
    rw [show h x - m x ^ 2 • h x = (1 - m x ^ 2) • h x by simp [sub_smul],
      norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hwpos]
    calc
      _ ≤ ((K ^ s)⁻¹ * Real.sqrt (1 + ‖x.2‖ ^ 2) ^ s) * ‖h x‖ :=
        mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ ≤ (K ^ s)⁻¹ * (w x * ‖h x‖) := by
        rw [mul_assoc]
        gcongr

/-- The assumed membership is exactly finite, convergent weighted L² energy:
the energy integral equals the squared weighted norm
(`app:ch_background:defn:bg-mixed`). -/
theorem carrierWeightedNorm_sq (w : CarrierVariable n → ℝ) (h : CarrierL2 n)
    (hw : CarrierWeightedMem w h) :
    carrierWeightedNorm w h hw ^ 2 =
      ∫ x, ‖w x • h x‖ ^ 2 ∂carrierMeasure n := by
  let v := hw.toLp (fun x ↦ w x • h x)
  have hid : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂carrierMeasure n := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) v v)
  exact hid.trans (integral_congr_ae (hw.coeFn_toLp.fun_comp (fun z ↦ ‖z‖ ^ 2)))

/-- Explicit convergence of the carrier energy integral
(`app:ch_background:defn:bg-mixed`). -/
theorem carrierWeightedEnergy_integrable (w : CarrierVariable n → ℝ) (h : CarrierL2 n)
    (hw : CarrierWeightedMem w h) :
    Integrable (fun x ↦ ‖w x • h x‖ ^ 2) (carrierMeasure n) :=
  hw.integrable_norm_pow (by decide)

/-- A measurable contraction mask defines an actual L∞ coefficient on the
Lebesgue initial variables (`app:ch_background:defn:bg-mixed`). -/
def carrierMask (m : CarrierVariable n → ℝ)
    (hmeas : AEStronglyMeasurable m (carrierMeasure n))
    (hm : ∀ᵐ x ∂carrierMeasure n, m x ∈ Set.Icc (0 : ℝ) 1) :
    Lp ℝ ∞ (carrierMeasure n) :=
  (memLp_top_of_bound hmeas 1 (hm.mono fun _ hx ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)).toLp m

/-- The bounded coefficient agrees with its given mask almost everywhere
(`app:ch_background:defn:bg-mixed`). -/
theorem carrierMask_coeFn (m : CarrierVariable n → ℝ)
    (hmeas : AEStronglyMeasurable m (carrierMeasure n))
    (hm : ∀ᵐ x ∂carrierMeasure n, m x ∈ Set.Icc (0 : ℝ) 1) :
    carrierMask m hmeas hm =ᵐ[carrierMeasure n] m := MemLp.coeFn_toLp _

/-- Support of the raw carrier square, before physical realization.
An outer band `C K` is obtained by taking `L = C * K`
(`app:ch_background:defn:bg-mixed`). -/
theorem carrierSquaredCutoff_support (m : Lp ℝ ∞ (carrierMeasure n))
    (h : CarrierL2 n) (L : ℝ)
    (hsupp : ∀ᵐ x ∂carrierMeasure n, L < ‖x.2‖ → m x = 0) :
    ∀ᵐ x ∂carrierMeasure n, L < ‖x.2‖ → carrierSquaredCutoff m h x = 0 := by
  filter_upwards [carrierSquaredCutoff_coeFn m h, hsupp] with x hx hsupp hL
  simp [hx, hsupp hL]

end JanetCartan.RawCutoffBounds
