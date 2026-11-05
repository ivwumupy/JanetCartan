module

public import JanetCartan.Analysis.Operator.Retarded.L2
public import Mathlib.Analysis.Complex.Exponential

/-!
# Literal retarded integration

The lower and upper time integrals from `app:ch_osc:setup:osc-retarded` and
`app:ch_osc:eq:retarded-literal-adjoint`. The transverse space is arbitrary;
Euclidean transverse rectangles are obtained by restricting their volume measure.

`lower_l2_bound` and `upper_l2_bound` prove L² membership and the squared norm
estimate with constant `(Cin * Cout * (b - a))²`. `adjoint_pairing` proves the
complex pairing identity by Fubini. The L² arguments only need real bounded,
almost-everywhere measurable cutoffs; the manuscript's smoothness and lower-end
buffer are needed for its separate Sobolev assertions. The modulation identities
hold pointwise for every real transverse phase, including `λ * ζ · y`.
-/

@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ComplexConjugate

namespace JanetCartan.Retarded

variable {Y : Type*}

/-- The actual lower-time integral in `app:ch_osc:setup:osc-retarded`.
The real cutoffs are evaluated in the same time/transverse coordinates as the input. -/
def lower (a : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ) (x : ℝ × Y) : ℂ :=
  χout x * ∫ s in a..x.1, (χin (s, x.2) : ℂ) * f (s, x.2)

/-- The upper-time literal adjoint in `app:ch_osc:eq:retarded-literal-adjoint`. -/
def upper (b : ℝ) (χin χout : ℝ × Y → ℝ) (v : ℝ × Y → ℂ) (x : ℝ × Y) : ℂ :=
  χin x * ∫ t in x.1..b, (χout (t, x.2) : ℂ) * v (t, x.2)

/-- Transverse multipliers commute with the lower integral
(`app:ch_osc:eq:osc-retarded-commute`). -/
theorem lower_mul_transverse (a : ℝ) (χin χout : ℝ × Y → ℝ)
    (f : ℝ × Y → ℂ) (m : Y → ℂ) (x : ℝ × Y) :
    lower a χin χout (fun z ↦ m z.2 * f z) x = m x.2 * lower a χin χout f x := by
  simp only [lower]
  simp_rw [mul_left_comm (χin _ : ℂ) (m _), intervalIntegral.integral_const_mul]
  ring

/-- Transverse multipliers also commute with the upper integral
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem upper_mul_transverse (b : ℝ) (χin χout : ℝ × Y → ℝ)
    (f : ℝ × Y → ℂ) (m : Y → ℂ) (x : ℝ × Y) :
    upper b χin χout (fun z ↦ m z.2 * f z) x = m x.2 * upper b χin χout f x := by
  simp only [upper]
  simp_rw [mul_left_comm (χout _ : ℂ) (m _), intervalIntegral.integral_const_mul]
  ring

/-- Exact modulation cancellation in `app:ch_osc:eq:osc-retarded-commute`.
Taking `φ y = λ * ζ · y` gives the manuscript's formula. -/
theorem lower_modulation (a : ℝ) (χin χout : ℝ × Y → ℝ)
    (f : ℝ × Y → ℂ) (φ : Y → ℝ) (x : ℝ × Y) :
    Complex.exp (-(Complex.I * φ x.2)) *
      lower a χin χout (fun z ↦ Complex.exp (Complex.I * φ z.2) * f z) x =
        lower a χin χout f x := by
  rw [lower_mul_transverse a χin χout f (fun y ↦ Complex.exp (Complex.I * φ y)),
    ← mul_assoc, ← Complex.exp_add]
  simp

/-- Exact modulation cancellation for the adjoint
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem upper_modulation (b : ℝ) (χin χout : ℝ × Y → ℝ)
    (f : ℝ × Y → ℂ) (φ : Y → ℝ) (x : ℝ × Y) :
    Complex.exp (-(Complex.I * φ x.2)) *
      upper b χin χout (fun z ↦ Complex.exp (Complex.I * φ z.2) * f z) x =
        upper b χin χout f x := by
  rw [upper_mul_transverse b χin χout f (fun y ↦ Complex.exp (Complex.I * φ y)),
    ← mul_assoc, ← Complex.exp_add]
  simp

/-- Fubini proves the literal adjoint pairing on each transverse fiber
(`app:ch_osc:eq:retarded-literal-adjoint`). Only integrability of the weighted
inputs on the fixed time interval is required. -/
theorem adjoint_pairing_time (a b : ℝ) (χin χout : ℝ × Y → ℝ)
    (f v : ℝ × Y → ℂ) (y : Y)
    (hf : IntegrableOn (fun s ↦ (χin (s, y) : ℂ) * f (s, y)) (Icc a b))
    (hv : IntegrableOn (fun t ↦ (χout (t, y) : ℂ) * v (t, y)) (Icc a b)) :
    (∫ t in Icc a b, lower a χin χout f (t, y) * conj (v (t, y))) =
      ∫ s in Icc a b, f (s, y) * conj (upper b χin χout v (s, y)) := by
  have hv' := Complex.conjCLE.toContinuousLinearMap.integrable_comp hv
  have h := integral_lower_mul_eq_mul_upper a b
    (fun s ↦ (χin (s, y) : ℂ) * f (s, y))
    (fun t ↦ conj ((χout (t, y) : ℂ) * v (t, y))) hf hv'
  simp only [map_mul, Complex.conj_ofReal] at h
  simp only [lower, upper, map_mul, Complex.conj_ofReal]
  calc
    _ = ∫ t in Icc a b, (∫ s in a..t, (χin (s, y) : ℂ) * f (s, y)) *
        ((χout (t, y) : ℂ) * conj (v (t, y))) := by
      congr 1; funext t; ring
    _ = _ := h
    _ = _ := by
      congr 1
      funext s
      rw [show (∫ t in s..b, (χout (t, y) : ℂ) * conj (v (t, y))) =
          conj (∫ t in s..b, (χout (t, y) : ℂ) * v (t, y)) by
        simpa only [map_mul, Complex.conj_ofReal] using
          intervalIntegral_conj s b (fun t ↦ (χout (t, y) : ℂ) * v (t, y))]
      ring

/-- Uniform time-fiber estimate for the lower integral
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem norm_lower_le (a b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) {Cin Cout : ℝ} (hCin : 0 ≤ Cin)
    (hin : ∀ s ∈ Icc a b, |χin (s, y)| ≤ Cin)
    (hout : ∀ t ∈ Icc a b, |χout (t, y)| ≤ Cout)
    (hf : IntegrableOn (fun s ↦ f (s, y)) (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖lower a χin χout f (t, y)‖ ≤ (Cout * Cin) * ∫ s in Icc a b, ‖f (s, y)‖ := by
  have hi := norm_integral_mask_le (volume.restrict (Icc a b))
    (fun s ↦ f (s, y)) (fun s ↦ (χin (s, y) : ℂ)) (fun s ↦ s ≤ t) hf hCin (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      simpa using hin s hs)
  rw [integral_lower_triangle a b t ht] at hi
  simp only [lower, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ Cout * (Cin * ∫ s in Icc a b, ‖f (s, y)‖) :=
      mul_le_mul (hout t ht) hi (norm_nonneg _) ((abs_nonneg _).trans (hout t ht))
    _ = _ := by ring

/-- Measurability of the lower integral on the fixed interval
(`app:ch_osc:setup:osc-retarded`). -/
theorem aestronglyMeasurable_lower_time (a b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) (hin : AEStronglyMeasurable (fun s ↦ (χin (s, y) : ℂ))
      (volume.restrict (Icc a b)))
    (hout : AEStronglyMeasurable (fun t ↦ (χout (t, y) : ℂ))
      (volume.restrict (Icc a b)))
    (hf : AEStronglyMeasurable (fun s ↦ f (s, y)) (volume.restrict (Icc a b))) :
    AEStronglyMeasurable (fun t ↦ lower a χin χout f (t, y))
      (volume.restrict (Icc a b)) := by
  have hkernel : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ if p.2 ≤ p.1 then (χin (p.2, y) : ℂ) * f (p.2, y) else 0)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) :=
    (hin.mul hf).comp_snd.indicator (measurableSet_le measurable_snd measurable_fst)
  apply (hout.mul hkernel.integral_prod_right').congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [Pi.mul_apply]
  rw [integral_lower_triangle a b t ht]
  rfl

/-- Uniform time-fiber estimate for the upper integral
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem norm_upper_le (a b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) {Cout Cin : ℝ} (hCout : 0 ≤ Cout)
    (hout : ∀ s ∈ Icc a b, |χout (s, y)| ≤ Cout)
    (hin : ∀ t ∈ Icc a b, |χin (t, y)| ≤ Cin)
    (hf : IntegrableOn (fun s ↦ f (s, y)) (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖upper b χin χout f (t, y)‖ ≤ (Cin * Cout) * ∫ s in Icc a b, ‖f (s, y)‖ := by
  have hi := norm_integral_mask_le (volume.restrict (Icc a b))
    (fun s ↦ f (s, y)) (fun s ↦ (χout (s, y) : ℂ)) (fun s ↦ t ≤ s) hf hCout (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      simpa using hout s hs)
  rw [integral_upper_triangle a b t ht] at hi
  simp only [upper, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ Cin * (Cout * ∫ s in Icc a b, ‖f (s, y)‖) :=
      mul_le_mul (hin t ht) hi (norm_nonneg _) ((abs_nonneg _).trans (hin t ht))
    _ = _ := by ring

/-- Measurability of the upper integral on the fixed interval
(`app:ch_osc:setup:osc-retarded`). -/
theorem aestronglyMeasurable_upper_time (a b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) (hout : AEStronglyMeasurable (fun s ↦ (χout (s, y) : ℂ))
      (volume.restrict (Icc a b)))
    (hin : AEStronglyMeasurable (fun t ↦ (χin (t, y) : ℂ))
      (volume.restrict (Icc a b)))
    (hf : AEStronglyMeasurable (fun s ↦ f (s, y)) (volume.restrict (Icc a b))) :
    AEStronglyMeasurable (fun t ↦ upper b χin χout f (t, y))
      (volume.restrict (Icc a b)) := by
  have hkernel : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ if p.1 ≤ p.2 then (χout (p.2, y) : ℂ) * f (p.2, y) else 0)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) :=
    (hout.mul hf).comp_snd.indicator (measurableSet_le measurable_fst measurable_snd)
  apply (hin.mul hkernel.integral_prod_right').congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [Pi.mul_apply]
  rw [integral_upper_triangle a b t ht]
  rfl

/-- The lower integral preserves L² on each time fiber
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem memLp_lower_time (a b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) {Cin Cout : ℝ} (hCin : 0 ≤ Cin)
    (hin : ∀ s ∈ Icc a b, |χin (s, y)| ≤ Cin)
    (hout : ∀ t ∈ Icc a b, |χout (t, y)| ≤ Cout)
    (hmin : AEStronglyMeasurable (fun s ↦ (χin (s, y) : ℂ)) (volume.restrict (Icc a b)))
    (hmout : AEStronglyMeasurable (fun t ↦ (χout (t, y) : ℂ)) (volume.restrict (Icc a b)))
    (hf : MemLp (fun s ↦ f (s, y)) 2 (volume.restrict (Icc a b))) :
    MemLp (fun t ↦ lower a χin χout f (t, y)) 2 (volume.restrict (Icc a b)) := by
  apply MemLp.of_bound (aestronglyMeasurable_lower_time a b χin χout f y hmin hmout
    hf.aestronglyMeasurable) ((Cout * Cin) * ∫ s in Icc a b, ‖f (s, y)‖)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact norm_lower_le a b χin χout f y hCin hin hout (hf.integrable (by norm_num)) ht

/-- Quantitative squared L² estimate for the lower integral on a time fiber
(`app:ch_osc:prop:osc-retarded-tube`). Combine with `memLp_lower_time` to
exclude the undefined-integral convention. -/
theorem integral_sq_lower_time_le (a b : ℝ) (hab : a ≤ b)
    (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) {Cin Cout : ℝ} (hCin : 0 ≤ Cin) (hCout : 0 ≤ Cout)
    (hin : ∀ s ∈ Icc a b, |χin (s, y)| ≤ Cin)
    (hout : ∀ t ∈ Icc a b, |χout (t, y)| ≤ Cout)
    (hf : MemLp (fun s ↦ f (s, y)) 2 (volume.restrict (Icc a b))) :
    (∫ t in Icc a b, ‖lower a χin χout f (t, y)‖ ^ 2) ≤
      (Cout * Cin) ^ 2 * (b - a) ^ 2 * ∫ s in Icc a b, ‖f (s, y)‖ ^ 2 := by
  have h := integral_sq_le_of_uniform_integral_bound (volume.restrict (Icc a b))
    (fun s ↦ f (s, y)) (fun t ↦ lower a χin χout f (t, y)) hf (mul_nonneg hCout hCin) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact norm_lower_le a b χin χout f y hCin hin hout (hf.integrable (by norm_num)) ht)
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

/-- The upper integral preserves L² on each time fiber
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem memLp_upper_time (a b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) {Cout Cin : ℝ} (hCout : 0 ≤ Cout)
    (hout : ∀ s ∈ Icc a b, |χout (s, y)| ≤ Cout)
    (hin : ∀ t ∈ Icc a b, |χin (t, y)| ≤ Cin)
    (hmout : AEStronglyMeasurable (fun s ↦ (χout (s, y) : ℂ)) (volume.restrict (Icc a b)))
    (hmin : AEStronglyMeasurable (fun t ↦ (χin (t, y) : ℂ)) (volume.restrict (Icc a b)))
    (hf : MemLp (fun s ↦ f (s, y)) 2 (volume.restrict (Icc a b))) :
    MemLp (fun t ↦ upper b χin χout f (t, y)) 2 (volume.restrict (Icc a b)) := by
  apply MemLp.of_bound (aestronglyMeasurable_upper_time a b χin χout f y hmout hmin
    hf.aestronglyMeasurable) ((Cin * Cout) * ∫ s in Icc a b, ‖f (s, y)‖)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact norm_upper_le a b χin χout f y hCout hout hin (hf.integrable (by norm_num)) ht

/-- Quantitative squared L² estimate for the upper integral on a time fiber
(`app:ch_osc:prop:osc-retarded-tube`). Combine with `memLp_upper_time` to
exclude the undefined-integral convention. -/
theorem integral_sq_upper_time_le (a b : ℝ) (hab : a ≤ b)
    (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) {Cout Cin : ℝ} (hCout : 0 ≤ Cout) (hCin : 0 ≤ Cin)
    (hout : ∀ s ∈ Icc a b, |χout (s, y)| ≤ Cout)
    (hin : ∀ t ∈ Icc a b, |χin (t, y)| ≤ Cin)
    (hf : MemLp (fun s ↦ f (s, y)) 2 (volume.restrict (Icc a b))) :
    (∫ t in Icc a b, ‖upper b χin χout f (t, y)‖ ^ 2) ≤
      (Cin * Cout) ^ 2 * (b - a) ^ 2 * ∫ s in Icc a b, ‖f (s, y)‖ ^ 2 := by
  have h := integral_sq_le_of_uniform_integral_bound (volume.restrict (Icc a b))
    (fun s ↦ f (s, y)) (fun t ↦ upper b χin χout f (t, y)) hf (mul_nonneg hCin hCout) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact norm_upper_le a b χin χout f y hCout hout hin (hf.integrable (by norm_num)) ht)
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

/-- Almost-everywhere measurability of the lower integral on a rectangle
(`app:ch_osc:setup:osc-retarded`). The product measure lists the transverse
coordinate first, so its iterated integral is the integral of time-fiber pairings. -/
theorem aestronglyMeasurable_lower [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (hin : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χin (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hout : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χout (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hf : AEStronglyMeasurable (fun p : Y × ℝ ↦ f (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b)))) :
    AEStronglyMeasurable (fun p : Y × ℝ ↦ lower a χin χout f (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b))) := by
  let μ := volume.restrict (Icc a b)
  have hkernel : AEStronglyMeasurable
      (fun p : (Y × ℝ) × ℝ ↦ if p.2 ≤ p.1.2 then (χin (p.2, p.1.1) : ℂ) * f (p.2, p.1.1) else 0)
      ((ν.prod μ).prod μ) :=
    ((hin.mul hf).comp_quasiMeasurePreserving
      ((quasiMeasurePreserving_fst (μ := ν) (ν := μ)).prodMap
        (MeasureTheory.QuasiMeasurePreserving.id μ))).indicator
        (measurableSet_le measurable_snd measurable_fst.snd)
  apply (hout.mul hkernel.integral_prod_right').congr
  have ht : ∀ᵐ p : Y × ℝ ∂ν.prod μ, p.2 ∈ Icc a b :=
    quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with p hp
  simp only [Pi.mul_apply]
  rw [integral_lower_triangle a b p.2 hp]
  rfl

/-- Almost-everywhere measurability of the upper integral on a rectangle
(`app:ch_osc:setup:osc-retarded`). The product measure lists the transverse
coordinate first, so its iterated integral is the integral of time-fiber pairings. -/
theorem aestronglyMeasurable_upper [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (hout : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χout (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hin : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χin (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hf : AEStronglyMeasurable (fun p : Y × ℝ ↦ f (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b)))) :
    AEStronglyMeasurable (fun p : Y × ℝ ↦ upper b χin χout f (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b))) := by
  let μ := volume.restrict (Icc a b)
  have hkernel : AEStronglyMeasurable
      (fun p : (Y × ℝ) × ℝ ↦ if p.1.2 ≤ p.2 then (χout (p.2, p.1.1) : ℂ) * f (p.2, p.1.1) else 0)
      ((ν.prod μ).prod μ) :=
    ((hout.mul hf).comp_quasiMeasurePreserving
      ((quasiMeasurePreserving_fst (μ := ν) (ν := μ)).prodMap
        (MeasureTheory.QuasiMeasurePreserving.id μ))).indicator
        (measurableSet_le measurable_fst.snd measurable_snd)
  apply (hin.mul hkernel.integral_prod_right').congr
  have ht : ∀ᵐ p : Y × ℝ ∂ν.prod μ, p.2 ∈ Icc a b :=
    quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with p hp
  simp only [Pi.mul_apply]
  rw [integral_upper_triangle a b p.2 hp]
  rfl

/-- L² preservation and the quantitative bound on the bounded rectangle
(`app:ch_osc:prop:osc-retarded-tube`). The transverse measure may itself be
restricted to any bounded rectangle. All measurability and integrability
obligations are discharged from the stated input hypotheses. -/
theorem lower_l2_bound [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    {Cin Cout : ℝ} (hCin : 0 ≤ Cin) (hCout : 0 ≤ Cout)
    (hin : ∀ y s, s ∈ Icc a b → |χin (s, y)| ≤ Cin)
    (hout : ∀ y t, t ∈ Icc a b → |χout (t, y)| ≤ Cout)
    (hmin : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χin (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hmout : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χout (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hf : MemLp (fun p : Y × ℝ ↦ f (p.2, p.1)) 2
      (ν.prod (volume.restrict (Icc a b)))) :
    MemLp (fun p : Y × ℝ ↦ lower a χin χout f (p.2, p.1)) 2
      (ν.prod (volume.restrict (Icc a b))) ∧
    (∫ p : Y × ℝ, ‖lower a χin χout f (p.2, p.1)‖ ^ 2
      ∂ν.prod (volume.restrict (Icc a b))) ≤
      (Cout * Cin) ^ 2 * (b - a) ^ 2 *
        ∫ p : Y × ℝ, ‖f (p.2, p.1)‖ ^ 2 ∂ν.prod (volume.restrict (Icc a b)) := by
  apply memLp_two_prod_of_fiber_estimate ν (volume.restrict (Icc a b)) _ _ hf
    (aestronglyMeasurable_lower ν a b χin χout f hmin hmout hf.aestronglyMeasurable)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hfi : Integrable (fun p : Y × ℝ ↦ ‖f (p.2, p.1)‖ ^ 2)
      (ν.prod (volume.restrict (Icc a b))) := hf.integrable_norm_pow (by norm_num)
  filter_upwards [hmin.prodMk_left, hmout.prodMk_left,
    hf.aestronglyMeasurable.prodMk_left, hfi.prod_right_ae] with y hmi hmo hfm hfi
  have hfy : MemLp (fun t ↦ f (t, y)) 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq_norm hfm).2 hfi
  exact ⟨memLp_lower_time a b χin χout f y hCin (hin y) (hout y) hmi hmo hfy,
    integral_sq_lower_time_le a b hab χin χout f y hCin hCout (hin y) (hout y) hfy⟩

/-- L² preservation and the quantitative bound on the bounded rectangle
(`app:ch_osc:prop:osc-retarded-tube`). The transverse measure may itself be
restricted to any bounded rectangle. All measurability and integrability
obligations are discharged from the stated input hypotheses. -/
theorem upper_l2_bound [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    {Cout Cin : ℝ} (hCout : 0 ≤ Cout) (hCin : 0 ≤ Cin)
    (hout : ∀ y s, s ∈ Icc a b → |χout (s, y)| ≤ Cout)
    (hin : ∀ y t, t ∈ Icc a b → |χin (t, y)| ≤ Cin)
    (hmout : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χout (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hmin : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χin (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hf : MemLp (fun p : Y × ℝ ↦ f (p.2, p.1)) 2
      (ν.prod (volume.restrict (Icc a b)))) :
    MemLp (fun p : Y × ℝ ↦ upper b χin χout f (p.2, p.1)) 2
      (ν.prod (volume.restrict (Icc a b))) ∧
    (∫ p : Y × ℝ, ‖upper b χin χout f (p.2, p.1)‖ ^ 2
      ∂ν.prod (volume.restrict (Icc a b))) ≤
      (Cin * Cout) ^ 2 * (b - a) ^ 2 *
        ∫ p : Y × ℝ, ‖f (p.2, p.1)‖ ^ 2 ∂ν.prod (volume.restrict (Icc a b)) := by
  apply memLp_two_prod_of_fiber_estimate ν (volume.restrict (Icc a b)) _ _ hf
    (aestronglyMeasurable_upper ν a b χin χout f hmout hmin hf.aestronglyMeasurable)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hfi : Integrable (fun p : Y × ℝ ↦ ‖f (p.2, p.1)‖ ^ 2)
      (ν.prod (volume.restrict (Icc a b))) := hf.integrable_norm_pow (by norm_num)
  filter_upwards [hmout.prodMk_left, hmin.prodMk_left,
    hf.aestronglyMeasurable.prodMk_left, hfi.prod_right_ae] with y hmo hmi hfm hfi
  have hfy : MemLp (fun t ↦ f (t, y)) 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq_norm hfm).2 hfi
  exact ⟨memLp_upper_time a b χin χout f y hCout (hout y) (hin y) hmo hmi hfy,
    integral_sq_upper_time_le a b hab χin χout f y hCout hCin (hout y) (hin y) hfy⟩

/-- The literal upper operator is the complex L² adjoint of the lower operator
on the rectangle (`app:ch_osc:eq:retarded-literal-adjoint`). Fubini and the
proved L² bounds discharge the integrability of both pairings. -/
theorem adjoint_pairing [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (χin χout : ℝ × Y → ℝ) (f v : ℝ × Y → ℂ)
    {Cin Cout : ℝ} (hCin : 0 ≤ Cin) (hCout : 0 ≤ Cout)
    (hin : ∀ y s, s ∈ Icc a b → |χin (s, y)| ≤ Cin)
    (hout : ∀ y t, t ∈ Icc a b → |χout (t, y)| ≤ Cout)
    (hmin : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χin (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hmout : AEStronglyMeasurable (fun p : Y × ℝ ↦ (χout (p.2, p.1) : ℂ))
      (ν.prod (volume.restrict (Icc a b))))
    (hf : MemLp (fun p : Y × ℝ ↦ f (p.2, p.1)) 2
      (ν.prod (volume.restrict (Icc a b))))
    (hv : MemLp (fun p : Y × ℝ ↦ v (p.2, p.1)) 2
      (ν.prod (volume.restrict (Icc a b)))) :
    (∫ p : Y × ℝ, lower a χin χout f (p.2, p.1) * conj (v (p.2, p.1))
      ∂ν.prod (volume.restrict (Icc a b))) =
    ∫ p : Y × ℝ, f (p.2, p.1) * conj (upper b χin χout v (p.2, p.1))
      ∂ν.prod (volume.restrict (Icc a b)) := by
  have hJ := (lower_l2_bound ν a b hab χin χout f hCin hCout hin hout hmin hmout hf).1
  have hJstar := (upper_l2_bound ν a b hab χin χout v hCout hCin hout hin hmout hmin hv).1
  have hl : Integrable (fun p : Y × ℝ ↦ lower a χin χout f (p.2, p.1) * conj (v (p.2, p.1)))
      (ν.prod (volume.restrict (Icc a b))) := hJ.integrable_mul hv.star
  have hr : Integrable (fun p : Y × ℝ ↦ f (p.2, p.1) * conj (upper b χin χout v (p.2, p.1)))
      (ν.prod (volume.restrict (Icc a b))) := hf.integrable_mul hJstar.star
  rw [integral_prod _ hl, integral_prod _ hr]
  apply integral_congr_ae
  filter_upwards [memLp_two_fiber_ae ν (volume.restrict (Icc a b)) hf,
    memLp_two_fiber_ae ν (volume.restrict (Icc a b)) hv,
    hmin.prodMk_left, hmout.prodMk_left] with y hfy hvy hmi hmo
  apply adjoint_pairing_time a b χin χout f v y
  · apply integrable_mul_cutoff _ _ hmi (hfy.integrable (by norm_num))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa using hin y s hs
  · apply integrable_mul_cutoff _ _ hmo (hvy.integrable (by norm_num))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa using hout y t ht

variable [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The uniform L² bounds for the compactly supported cutoffs of
`app:ch_osc:setup:osc-retarded`. Their common constant is chosen before the input
function. Smoothness and the positive lower-end buffer are unnecessary for this
L² part of `app:ch_osc:prop:osc-retarded-tube`. -/
theorem l2_bounds_of_continuous_hasCompactSupport (ν : Measure Y) [SFinite ν] (a b : ℝ) (hab : a ≤ b)
    (χin χout : ℝ × Y → ℝ) (hin : Continuous χin) (hout : Continuous χout)
    (hsin : HasCompactSupport χin) (hsout : HasCompactSupport χout) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ × Y → ℂ,
      MemLp (fun p : Y × ℝ ↦ f (p.2, p.1)) 2 (ν.prod (volume.restrict (Icc a b))) →
      MemLp (fun p : Y × ℝ ↦ lower a χin χout f (p.2, p.1)) 2
        (ν.prod (volume.restrict (Icc a b))) ∧
      MemLp (fun p : Y × ℝ ↦ upper b χin χout f (p.2, p.1)) 2
        (ν.prod (volume.restrict (Icc a b))) ∧
      (∫ p : Y × ℝ, ‖lower a χin χout f (p.2, p.1)‖ ^ 2
        ∂ν.prod (volume.restrict (Icc a b))) ≤
        C * ∫ p : Y × ℝ, ‖f (p.2, p.1)‖ ^ 2 ∂ν.prod (volume.restrict (Icc a b)) ∧
      (∫ p : Y × ℝ, ‖upper b χin χout f (p.2, p.1)‖ ^ 2
        ∂ν.prod (volume.restrict (Icc a b))) ≤
        C * ∫ p : Y × ℝ, ‖f (p.2, p.1)‖ ^ 2 ∂ν.prod (volume.restrict (Icc a b)) := by
  obtain ⟨Cin, hCin, hbi⟩ := exists_cutoff_bound χin hin hsin
  obtain ⟨Cout, hCout, hbo⟩ := exists_cutoff_bound χout hout hsout
  have hmi : Continuous (fun p : Y × ℝ ↦ (χin (p.2, p.1) : ℂ)) :=
    Complex.continuous_ofReal.comp (hin.comp continuous_swap)
  have hmo : Continuous (fun p : Y × ℝ ↦ (χout (p.2, p.1) : ℂ)) :=
    Complex.continuous_ofReal.comp (hout.comp continuous_swap)
  refine ⟨(Cout * Cin) ^ 2 * (b - a) ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
  intro f hf
  have hl := lower_l2_bound ν a b hab χin χout f hCin hCout
    (fun y s _ ↦ hbi (s, y)) (fun y t _ ↦ hbo (t, y))
    hmi.aestronglyMeasurable hmo.aestronglyMeasurable hf
  have hu := upper_l2_bound ν a b hab χin χout f hCout hCin
    (fun y s _ ↦ hbo (s, y)) (fun y t _ ↦ hbi (t, y))
    hmo.aestronglyMeasurable hmi.aestronglyMeasurable hf
  refine ⟨hl.1, hu.1, hl.2, ?_⟩
  simpa only [mul_comm Cin Cout] using hu.2

/-- Literal adjoint pairing for the compactly supported continuous cutoffs
of `app:ch_osc:setup:osc-retarded`; this proves
`app:ch_osc:eq:retarded-literal-adjoint` on the rectangle. -/
theorem adjoint_pairing_of_continuous_hasCompactSupport (ν : Measure Y) [SFinite ν] (a b : ℝ) (hab : a ≤ b)
    (χin χout : ℝ × Y → ℝ) (hin : Continuous χin) (hout : Continuous χout)
    (hsin : HasCompactSupport χin) (hsout : HasCompactSupport χout)
    (f v : ℝ × Y → ℂ)
    (hf : MemLp (fun p : Y × ℝ ↦ f (p.2, p.1)) 2 (ν.prod (volume.restrict (Icc a b))))
    (hv : MemLp (fun p : Y × ℝ ↦ v (p.2, p.1)) 2 (ν.prod (volume.restrict (Icc a b)))) :
    (∫ p : Y × ℝ, lower a χin χout f (p.2, p.1) * conj (v (p.2, p.1))
      ∂ν.prod (volume.restrict (Icc a b))) =
    ∫ p : Y × ℝ, f (p.2, p.1) * conj (upper b χin χout v (p.2, p.1))
      ∂ν.prod (volume.restrict (Icc a b)) := by
  obtain ⟨Cin, hCin, hbi⟩ := exists_cutoff_bound χin hin hsin
  obtain ⟨Cout, hCout, hbo⟩ := exists_cutoff_bound χout hout hsout
  apply adjoint_pairing ν a b hab χin χout f v hCin hCout
    (fun y s _ ↦ hbi (s, y)) (fun y t _ ↦ hbo (t, y)) _ _ hf hv
  · exact (Complex.continuous_ofReal.comp (hin.comp continuous_swap)).aestronglyMeasurable
  · exact (Complex.continuous_ofReal.comp (hout.comp continuous_swap)).aestronglyMeasurable

end JanetCartan.Retarded
