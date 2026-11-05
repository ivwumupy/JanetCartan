module

public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Quantitative Fourier Sobolev norms on Euclidean L²

The scale used in `app:ch_regular_base:eq:fio-input` and the interpolation
following `app:ch_regular_base:eq:graph-derivative-transfer` is defined on
actual scalar L² classes. The weight is `(1 + ‖ξ‖²)^(s/2)`. Mathlib's Fourier
transform uses `exp (-2π i ⟪x, ξ⟫)`, so a coordinate derivative has multiplier
`2π i ξⱼ`. Thus this weight corresponds to `(1 - (2π)⁻² Δ)^(s/2)`, exactly
as in `TemperedDistribution.besselPotential`.

`fourierSobolevNorm` uses `ENNReal.toReal`; it is meaningful as a norm only
alongside `MemFourierSobolev`. In particular, every order comparison below
requires membership at the larger order before converting to real numbers.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}

/-- The Euclidean Bessel weight for `app:ch_regular_base:eq:fio-input`. -/
def euclideanSobolevWeight (s : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (s / 2)

/-- The weighted Fourier representative for
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
def weightedL2Fourier (s : ℝ) (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  euclideanSobolevWeight s ξ • (𝓕 u) ξ

/-- Membership accompanying the numerical norm in
`app:ch_regular_base:eq:fio-input`; the weighted Fourier transform is in L². -/
def MemFourierSobolev (s : ℝ) (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) : Prop :=
  MemLp (weightedL2Fourier s u) 2

/-- The Fourier Sobolev norm in `app:ch_regular_base:eq:fio-input`.
Use together with `MemFourierSobolev`, since `toReal ⊤ = 0`. -/
def fourierSobolevNorm (s : ℝ) (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) : ℝ :=
  (eLpNorm (weightedL2Fourier s u) 2 volume).toReal

/-- Positivity of the weight used in `app:ch_regular_base:eq:fio-input`. -/
theorem euclideanSobolevWeight_pos (s : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    0 < euclideanSobolevWeight s ξ :=
  Real.rpow_pos_of_pos (by positivity) _

/-- The weight is increasing with the order in
`app:ch_regular_base:eq:fio-input`. -/
theorem euclideanSobolevWeight_mono {s t : ℝ} (hst : s ≤ t)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    euclideanSobolevWeight s ξ ≤ euclideanSobolevWeight t ξ := by
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖])
    (div_le_div_of_nonneg_right hst (by norm_num))

/-- Order zero has unit weight in `app:ch_regular_base:eq:fio-input`. -/
@[simp] theorem euclideanSobolevWeight_zero (ξ : EuclideanSpace ℝ (Fin d)) :
    euclideanSobolevWeight 0 ξ = 1 := by
  simp [euclideanSobolevWeight]

/-- Addition of orders multiplies weights, as used after
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem euclideanSobolevWeight_add (s t : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    euclideanSobolevWeight (s + t) ξ =
      euclideanSobolevWeight s ξ * euclideanSobolevWeight t ξ := by
  simp only [euclideanSobolevWeight, add_div]
  exact Real.rpow_add (by positivity) _ _

/-- Regularity of the multiplier in `app:ch_regular_base:eq:fio-input`. -/
theorem continuous_euclideanSobolevWeight (s : ℝ) :
    Continuous (euclideanSobolevWeight (d := d) s) := by
  unfold euclideanSobolevWeight
  apply Continuous.rpow_const (by fun_prop)
  intro ξ
  left
  positivity

/-- The weight is an allowed multiplier on tempered distributions, matching
`app:ch_regular_base:eq:fio-input`. -/
theorem hasTemperateGrowth_euclideanSobolevWeight (s : ℝ) :
    (euclideanSobolevWeight (d := d) s).HasTemperateGrowth := by
  unfold euclideanSobolevWeight
  fun_prop

/-- Measurability needed for the Fourier norms in
`app:ch_regular_base:eq:fio-input`. -/
theorem aestronglyMeasurable_weightedL2Fourier (s : ℝ)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    AEStronglyMeasurable (weightedL2Fourier s u) volume :=
  (continuous_euclideanSobolevWeight s).aestronglyMeasurable.smul
    (Lp.memLp (𝓕 u)).aestronglyMeasurable

/-- Pointwise norm of the weighted representative for
`app:ch_regular_base:eq:fio-input`. -/
theorem norm_weightedL2Fourier (s : ℝ)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖weightedL2Fourier s u ξ‖ = euclideanSobolevWeight s ξ *
      ‖(𝓕 u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) ξ‖ := by
  rw [weightedL2Fourier, norm_smul, Real.norm_eq_abs,
    abs_of_pos (euclideanSobolevWeight_pos s ξ)]

/-- Order zero leaves the Fourier representative unchanged, for
`app:ch_regular_base:eq:fio-input`. -/
@[simp] theorem weightedL2Fourier_zero
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    weightedL2Fourier 0 u = ⇑(𝓕 u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) := by
  funext ξ
  simp [weightedL2Fourier]

/-- All L² data belong to order zero in `app:ch_regular_base:eq:fio-input`. -/
@[simp] theorem memFourierSobolev_zero (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    MemFourierSobolev 0 u := by
  unfold MemFourierSobolev
  rw [weightedL2Fourier_zero]
  exact Lp.memLp _

/-- Exact order-zero normalization by Plancherel, for
`app:ch_regular_base:eq:fio-input`. -/
@[simp] theorem fourierSobolevNorm_zero (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    fourierSobolevNorm 0 u = ‖u‖ := by
  rw [fourierSobolevNorm, weightedL2Fourier_zero, ← Lp.norm_def, Lp.norm_fourier_eq]

/-- Nonnegativity of the numerical norm in `app:ch_regular_base:eq:fio-input`. -/
theorem fourierSobolevNorm_nonneg (s : ℝ)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) : 0 ≤ fourierSobolevNorm s u :=
  ENNReal.toReal_nonneg

/-- Lower orders inherit membership in `app:ch_regular_base:eq:fio-input`. -/
theorem MemFourierSobolev.mono {s t : ℝ}
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hu : MemFourierSobolev t u) (hst : s ≤ t) : MemFourierSobolev s u := by
  apply MemLp.mono hu (aestronglyMeasurable_weightedL2Fourier s u)
  filter_upwards [] with ξ
  simp only [norm_weightedL2Fourier]
  exact mul_le_mul_of_nonneg_right (euclideanSobolevWeight_mono hst ξ) (norm_nonneg _)

/-- Quantitative order monotonicity for `app:ch_regular_base:eq:fio-input`.
The membership premise excludes the spurious value `toReal ⊤ = 0`. -/
theorem fourierSobolevNorm_mono {s t : ℝ}
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hu : MemFourierSobolev t u) (hst : s ≤ t) :
    fourierSobolevNorm s u ≤ fourierSobolevNorm t u := by
  apply ENNReal.toReal_mono hu.eLpNorm_ne_top
  apply eLpNorm_mono (aestronglyMeasurable_weightedL2Fourier s u)
  intro ξ
  simp only [norm_weightedL2Fourier]
  exact mul_le_mul_of_nonneg_right (euclideanSobolevWeight_mono hst ξ) (norm_nonneg _)

/-- Nonpositive orders contain every L² datum, for
`app:ch_regular_base:eq:fio-input`. -/
theorem memFourierSobolev_of_nonpos {s : ℝ} (hs : s ≤ 0)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) : MemFourierSobolev s u :=
  (memFourierSobolev_zero u).mono hs

/-- The positive-order norm controls L² in `app:ch_regular_base:eq:fio-input`. -/
theorem norm_le_fourierSobolevNorm {s : ℝ} (hs : 0 ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2} (hu : MemFourierSobolev s u) :
    ‖u‖ ≤ fourierSobolevNorm s u := by
  simpa using fourierSobolevNorm_mono hu hs

/-- Pointwise multiplication agrees with multiplication of distributions when
the product is in L². This is the representation step for the actual
derivatives in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem toTemperedDistribution_toLp_pointwise_smul
    (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : g.HasTemperateGrowth)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (hgu : MemLp (fun ξ ↦ g ξ • u ξ) 2) :
    (hgu.toLp _ : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ g
        (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [hgu.coeFn_toLp] with ξ hξ
  rw [hξ]
  simp [hg, smul_eq_mul, mul_left_comm, mul_assoc]

/-- Fourier membership supplies Mathlib's Bessel-potential membership for the
actual L² distribution, with exactly the weight in
`app:ch_regular_base:eq:fio-input`. -/
theorem MemFourierSobolev.memSobolev {s : ℝ}
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2} (hu : MemFourierSobolev s u) :
    TemperedDistribution.MemSobolev s 2 (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  apply TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mpr
  refine ⟨hu.toLp _, ?_⟩
  rw [Lp.fourier_toTemperedDistribution_eq]
  ext φ
  simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with ξ hξ
  rw [hξ]
  have hgc : (fun ξ : EuclideanSpace ℝ (Fin d) ↦
      (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  simp [hgc, weightedL2Fourier, euclideanSobolevWeight, mul_left_comm, mul_assoc]

end JanetCartan.Pseudodifferential
