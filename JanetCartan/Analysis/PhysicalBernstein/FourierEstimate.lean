module

public import JanetCartan.Analysis.PhysicalBernstein.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Fourier integral estimates with compact frequency support

The analytic inputs of paper-v2 `new:lem:bernstein(ii)` are ordinary Euclidean
Fourier inversion, Cauchy–Schwarz on the frequency ball, and Plancherel.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.PhysicalBernstein

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The fixed dimension/order constant for the physical Bernstein estimate
`new:lem:bernstein(ii)`. The harmless added one makes positivity immediate,
including in dimension zero. -/
def bernsteinConstant (n r : ℕ) : ℝ :=
  (2 * Real.pi) ^ r *
    (1 + Real.sqrt (volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-- The Bernstein constant is positive and independent of bandwidth, stage,
accuracy, and the field (`main:eq:final-Cr`). -/
theorem bernsteinConstant_pos (n r : ℕ) : 0 < bernsteinConstant n r := by
  unfold bernsteinConstant
  positivity

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Differentiating the genuine Fourier integral costs one frequency per
derivative, not a Sobolev loss (`new:lem:bernstein(ii)`). -/
theorem norm_iteratedFDeriv_fourier_le_integral
    (g : SchwartzMap E F) {Λ : ℝ}
    (hs : ∀ ξ, Λ < ‖ξ‖ → g ξ = 0) (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (𝓕 (g : E → F)) x‖ ≤
      (2 * Real.pi) ^ r * Λ ^ r * ∫ ξ, ‖g ξ‖ := by
  rw [Real.iteratedFDeriv_fourier (N := ⊤)
    (fun k _ ↦ g.integrable_pow_mul volume k) g.continuous.aestronglyMeasurable (by simp)]
  apply (Real.norm_fourier_le_integral_norm _ x).trans
  calc
    (∫ ξ, ‖VectorFourier.fourierPowSMulRight (innerSL ℝ) (g : E → F) ξ r‖) ≤
        ∫ ξ, ((2 * Real.pi) ^ r * Λ ^ r) * ‖g ξ‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
        (g.integrable.norm.const_mul _) (Filter.Eventually.of_forall ?_)
      intro ξ
      by_cases hξ : Λ < ‖ξ‖
      · have hbound := VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) (g : E → F) ξ r
        simpa only [hs ξ hξ, norm_zero, mul_zero] using hbound
      · have hbound := VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) (g : E → F) ξ r
        apply hbound.trans
        dsimp only
        calc
          _ ≤ (2 * Real.pi * 1) ^ r * Λ ^ r * ‖g ξ‖ := by
            gcongr
            · exact norm_innerSL_le ℝ
            · exact le_of_not_gt hξ
          _ = _ := by rw [mul_one]
    _ = _ := integral_const_mul _ _

/-- Cauchy–Schwarz over the actual Euclidean frequency ball gives the sharp
`Λ^(n/2)` factor (`new:lem:bernstein(ii)`). -/
theorem integral_norm_le_band_volume
    (g : SchwartzMap E F) {Λ : ℝ} (hΛ : 0 < Λ)
    (hs : ∀ ξ, Λ < ‖ξ‖ → g ξ = 0) :
    (∫ ξ, ‖g ξ‖) ≤
      Real.sqrt (volume.real (Metric.closedBall (0 : E) 1)) *
        Λ ^ ((n : ℝ) / 2) * ‖g.toLp 2 volume‖ := by
  let s : Set E := Metric.closedBall 0 Λ
  have houtside (ξ : E) (hξ : ξ ∉ s) : g ξ = 0 := by
    exact hs ξ (by simpa [s, Metric.mem_closedBall, dist_zero_right, not_le] using hξ)
  have hnorm : (∫ ξ in s, ‖g ξ‖) = ∫ ξ, ‖g ξ‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by simp [houtside ξ hξ])
  have hsq : (∫ ξ in s, ‖g ξ‖ ^ 2) = ∫ ξ, ‖g ξ‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by simp [houtside ξ hξ])
  have hfinite : IsFiniteMeasure (volume.restrict s) :=
    ⟨by simpa [s] using (isCompact_closedBall (0 : E) Λ).measure_lt_top (μ := volume)⟩
  let := hfinite
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict s)
    Real.HolderConjugate.two_two
    (f := fun _ : E ↦ (1 : ℝ)) (g := fun ξ ↦ ‖g ξ‖)
    (Filter.Eventually.of_forall (fun _ ↦ zero_le_one))
    (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
    (by simpa using (memLp_const (1 : ℝ) (p := 2) (μ := volume.restrict s)))
    (by simpa using ((g.memLp 2 volume).restrict s).norm)
  have hnorm2 : Real.sqrt (∫ ξ, ‖g ξ‖ ^ 2) = ‖g.toLp 2 volume‖ := by
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    simp [Real.sqrt_eq_rpow]
  have hvol : Real.sqrt (volume.real s) =
      Real.sqrt (volume.real (Metric.closedBall (0 : E) 1)) * Λ ^ ((n : ℝ) / 2) := by
    rw [show volume.real s = Λ ^ n * volume.real (Metric.closedBall (0 : E) 1) by
      simpa [s] using Measure.addHaar_real_closedBall' volume (0 : E) hΛ.le]
    rw [Real.sqrt_mul (pow_nonneg hΛ.le n), mul_comm]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul hΛ.le]
    congr 1
    ring
  calc
    (∫ ξ, ‖g ξ‖) ≤ Real.sqrt (volume.real s) * Real.sqrt (∫ ξ, ‖g ξ‖ ^ 2) := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_two, hnorm, hsq, Measure.real,
        Measure.restrict_apply_univ] using hcs
    _ = _ := by rw [hvol, hnorm2]

/-- The sharp Euclidean estimate for a Fourier transform whose input has
frequency support in a ball (`new:lem:bernstein(ii)`). -/
theorem norm_iteratedFDeriv_fourier_le
    (g : SchwartzMap E F) {Λ : ℝ} (hΛ : 0 < Λ)
    (hs : ∀ ξ, Λ < ‖ξ‖ → g ξ = 0) (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (𝓕 (g : E → F)) x‖ ≤
      bernsteinConstant n r * Λ ^ ((r : ℝ) + (n : ℝ) / 2) * ‖g.toLp 2 volume‖ := by
  calc
    _ ≤ (2 * Real.pi) ^ r * Λ ^ r * ∫ ξ, ‖g ξ‖ :=
      norm_iteratedFDeriv_fourier_le_integral g hs r x
    _ ≤ (2 * Real.pi) ^ r * Λ ^ r *
        (Real.sqrt (volume.real (Metric.closedBall (0 : E) 1)) *
          Λ ^ ((n : ℝ) / 2) * ‖g.toLp 2 volume‖) := by
      exact mul_le_mul_of_nonneg_left (integral_norm_le_band_volume g hΛ hs) (by positivity)
    _ ≤ (2 * Real.pi) ^ r * Λ ^ r *
        ((1 + Real.sqrt (volume.real (Metric.closedBall (0 : E) 1))) *
          Λ ^ ((n : ℝ) / 2) * ‖g.toLp 2 volume‖) := by
      gcongr
      linarith
    _ = _ := by
      rw [bernsteinConstant, Real.rpow_add hΛ, Real.rpow_natCast]
      ring

end JanetCartan.PhysicalBernstein
