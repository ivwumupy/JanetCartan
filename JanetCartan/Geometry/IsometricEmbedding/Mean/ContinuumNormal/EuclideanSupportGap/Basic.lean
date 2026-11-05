module

public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel
public import JanetCartan.Analysis.Microlocal.SingleChannel.TimeIntegration

/-!
# Euclidean frozen Fourier energy

The Plancherel and low-frequency deduction of `paper-v2.tex`,
`app:ch_background:prop:bg-frame`. Frequencies in Mathlib's L² transform are
cycles; the multiplier is evaluated at the physical radian covector `2πξ`.
The actual frozen symbol and its identification with the row remain obligations
of the parent continuum-normal construction.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ComplexInnerProductSpace

namespace JanetCartan.ContinuumNormal.EuclideanSupportGap

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "L²" => Lp (α := E) V 2 volume

/-- The literal Euclidean multiplier energy in
`app:ch_background:prop:bg-frame`, with the exact cycles-to-radians conversion. -/
def energy (b : E → V →L[ℂ] V) (u : L²) : ℝ :=
  ∫ ξ, (inner ℂ ((𝓕 u) ξ) (b ((2 * Real.pi) • ξ) ((𝓕 u) ξ))).re

/-- The explicit low-frequency constant for `app:ch_background:prop:bg-frame`.
The bad-frequency ball is measured in Mathlib's cycles coordinates. -/
def lowFrequencyConstant (n : ℕ) (c R₀ : ℝ) : ℝ :=
  c * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n))
    (R₀ / (2 * Real.pi)))).toReal

/-- Nonnegativity of the fixed loss used in `app:ch_background:prop:bg-frame`. -/
theorem lowFrequencyConstant_nonneg {c R₀ : ℝ} (hc : 0 ≤ c) :
    0 ≤ lowFrequencyConstant n c R₀ := mul_nonneg hc ENNReal.toReal_nonneg

/-- Plancherel for the existing L² transform, in the normalization used by
`energy` (`app:ch_background:prop:bg-frame`). -/
theorem integral_sq_fourier (u : L²) :
    (∫ ξ, ‖(𝓕 u) ξ‖ ^ 2) = ‖u‖ ^ 2 := by
  rw [SingleChannel.integral_norm_sq_eq_norm_sq, Lp.norm_fourier_eq]

/-- The L¹-to-L∞ bound for the existing L² transform follows from its proved
identification with the Fourier integral (`app:ch_background:prop:bg-frame`). -/
theorem ae_norm_fourier_le_integral (u : L²) (hu : Integrable (u : E → V)) :
    ∀ᵐ ξ, ‖(𝓕 u) ξ‖ ≤ ∫ x, ‖u x‖ := by
  filter_upwards [Localization.fourierTransform_coeFn_ae_integral_hilbert u hu]
    with ξ hξ
  rw [hξ]
  exact Real.norm_fourier_le_integral_norm _ _

/-- Bounded continuous symbols give an integrable energy density for every L²
input; no spectral positivity is needed here (`app:ch_background:prop:bg-frame`). -/
theorem integrable_energy (b : E → V →L[ℂ] V) (hb : Continuous b)
    {M : ℝ} (hM : ∀ k, ‖b k‖ ≤ M) (u : L²) :
    Integrable (fun ξ ↦ (inner ℂ ((𝓕 u) ξ)
      (b ((2 * Real.pi) • ξ) ((𝓕 u) ξ))).re) := by
  let f : E → V := (𝓕 u : L²)
  have hf2 : MemLp f 2 volume := Lp.memLp (𝓕 u)
  have hf := hf2.aestronglyMeasurable
  have hcont : Continuous (fun p : E × V ↦
      (inner ℂ p.2 (b ((2 * Real.pi) • p.1) p.2)).re) := by fun_prop
  have hp : AEStronglyMeasurable (fun ξ : E ↦ (ξ, f ξ)) volume :=
    aestronglyMeasurable_id.prodMk hf
  have he : AEStronglyMeasurable
      (fun ξ : E ↦ (inner ℂ (f ξ) (b ((2 * Real.pi) • ξ) (f ξ))).re) volume :=
    by
      have hh := hcont.comp_aestronglyMeasurable hp
      dsimp only at hh
      exact hh
  have hi : Integrable (fun ξ : E ↦ M * ‖f ξ‖ ^ 2) volume :=
    (hf2.norm.integrable_sq).const_mul M
  apply hi.mono' he
  filter_upwards [] with ξ
  calc
    ‖(inner ℂ (f ξ) (b ((2 * Real.pi) • ξ) (f ξ))).re‖
        ≤ ‖inner ℂ (f ξ) (b ((2 * Real.pi) • ξ) (f ξ))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖f ξ‖ * ‖b ((2 * Real.pi) • ξ) (f ξ)‖ := norm_inner_le_norm _ _
    _ ≤ ‖f ξ‖ * (M * ‖f ξ‖) := by
      gcongr
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
    _ = M * ‖f ξ‖ ^ 2 := by ring


/-- The Euclidean high-frequency gap with an explicit L¹-squared loss,
`app:ch_background:prop:bg-frame`. A Hermitian symbol is allowed; the argument
only uses the stated bounds on the real quadratic form. -/
theorem energy_ge_sub_low_frequency (b : E → V →L[ℂ] V) (hb : Continuous b)
    {c M R₀ : ℝ} (hc : 0 ≤ c) (hM : ∀ k, ‖b k‖ ≤ M)
    (hnonneg : ∀ k v, 0 ≤ (inner ℂ v (b k v)).re)
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v, c * ‖v‖ ^ 2 ≤ (inner ℂ v (b k v)).re)
    (u : L²) (hu : Integrable (u : E → V)) :
    c * ‖u‖ ^ 2 - lowFrequencyConstant n c R₀ * (∫ x, ‖u x‖) ^ 2 ≤ energy b u := by
  let B := Metric.ball (0 : E) (R₀ / (2 * Real.pi))
  let A := (∫ x, ‖u x‖) ^ 2
  have hB : MeasurableSet B := measurableSet_ball
  have hBfinite : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hI : Integrable (B.indicator (fun _ : E ↦ c * A)) volume :=
    (integrableOn_const (C := c * A) hBfinite).integrable_indicator hB
  have hpoint : ∀ᵐ ξ, c * ‖(𝓕 u) ξ‖ ^ 2 ≤
      (inner ℂ ((𝓕 u) ξ) (b ((2 * Real.pi) • ξ) ((𝓕 u) ξ))).re +
        B.indicator (fun _ ↦ c * A) ξ := by
    filter_upwards [ae_norm_fourier_le_integral u hu] with ξ hξ
    by_cases hξB : ξ ∈ B
    · rw [Set.indicator_of_mem hξB]
      have hsq : ‖(𝓕 u) ξ‖ ^ 2 ≤ A :=
        (sq_le_sq₀ (norm_nonneg _) (integral_nonneg (fun x ↦ norm_nonneg (u x)))).mpr hξ
      have := mul_le_mul_of_nonneg_left hsq hc
      linarith [hnonneg ((2 * Real.pi) • ξ) ((𝓕 u) ξ)]
    · rw [Set.indicator_of_notMem hξB, add_zero]
      apply hgap
      have hout : R₀ / (2 * Real.pi) ≤ ‖ξ‖ := by
        simpa only [B, Metric.mem_ball, dist_zero_right, not_lt] using hξB
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hout |>.trans_eq (mul_comm _ _)
  have h := integral_mono_ae (((Lp.memLp (𝓕 u)).norm.integrable_sq).const_mul c)
    ((integrable_energy b hb hM u).add hI) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_energy b hb hM u) hI, integral_const_mul,
    integral_sq_fourier, integral_indicator hB, setIntegral_const] at h
  change c * ‖u‖ ^ 2 ≤ energy b u + (volume B).toReal * (c * A) at h
  dsimp [lowFrequencyConstant, B, A] at *
  nlinarith

end JanetCartan.ContinuumNormal.EuclideanSupportGap
