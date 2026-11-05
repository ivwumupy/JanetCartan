module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.FirstDerivatives.Coordinates

/-!
# First-derivative estimates for Euclidean Fourier Sobolev norms

The gain-one argument following `app:ch_regular_base:eq:graph-derivative-transfer`
uses the order-`s` norms of the input and its actual first derivatives to control
its order-`s + 1` norm. We prove the missing membership as well as the estimate.
The converse estimate retains the `2π i ξⱼ` Fourier convention from
`app:ch_regular_base:eq:fio-input`. All results include dimension zero.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}

private theorem euclideanSobolevWeight_one_sq (ξ : EuclideanSpace ℝ (Fin d)) :
    euclideanSobolevWeight 1 ξ ^ 2 = 1 + ‖ξ‖ ^ 2 := by
  rw [euclideanSobolevWeight, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]

private theorem norm_le_euclideanSobolevWeight_one (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖ξ‖ ≤ euclideanSobolevWeight 1 ξ := by
  have := euclideanSobolevWeight_one_sq ξ
  have := euclideanSobolevWeight_pos 1 ξ
  nlinarith [norm_nonneg ξ]

private theorem euclideanSobolevWeight_one_le_coordinateSymbols (ξ : EuclideanSpace ℝ (Fin d)) :
    euclideanSobolevWeight 1 ξ ≤ 1 + ∑ i, ‖euclideanCoordinateDerivativeSymbol i ξ‖ := by
  have hsum : ‖ξ‖ ≤ ∑ i, |ξ i| := by
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun i : Fin d ↦ |ξ i|) (fun i _ ↦ abs_nonneg (ξ i))
    have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin d ↦ ℝ) ξ
    simp only [Real.norm_eq_abs] at hn
    have hpos : 0 ≤ ∑ i, |ξ i| := Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
    nlinarith [norm_nonneg ξ]
  have hw : euclideanSobolevWeight 1 ξ ≤ 1 + ‖ξ‖ := by
    have := euclideanSobolevWeight_one_sq ξ
    have := euclideanSobolevWeight_pos 1 ξ
    nlinarith [norm_nonneg ξ]
  apply hw.trans
  apply add_le_add le_rfl
  apply hsum.trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_euclideanCoordinateDerivativeSymbol]
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  nlinarith [abs_nonneg (ξ i)]

private theorem norm_weightedL2Fourier_le_coordinateDerivatives_ae (s : ℝ)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : Fin d → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hv : ∀ i, HasEuclideanL2CoordinateDerivative i u (v i)) :
    ∀ᵐ ξ ∂volume, ‖weightedL2Fourier (s + 1) u ξ‖ ≤
      ‖weightedL2Fourier s u ξ‖ + ∑ i, ‖weightedL2Fourier s (v i) ξ‖ := by
  have hae := ae_all_iff.mpr (fun i ↦ (hv i).weightedL2Fourier_ae_eq s)
  filter_upwards [hae] with ξ hξ
  calc
    ‖weightedL2Fourier (s + 1) u ξ‖ =
        euclideanSobolevWeight 1 ξ * ‖weightedL2Fourier s u ξ‖ := by
      rw [norm_weightedL2Fourier, euclideanSobolevWeight_add, norm_weightedL2Fourier]
      ring
    _ ≤ (1 + ∑ i, ‖euclideanCoordinateDerivativeSymbol i ξ‖) *
        ‖weightedL2Fourier s u ξ‖ :=
      mul_le_mul_of_nonneg_right (euclideanSobolevWeight_one_le_coordinateSymbols ξ) (norm_nonneg _)
    _ = ‖weightedL2Fourier s u ξ‖ + ∑ i, ‖weightedL2Fourier s (v i) ξ‖ := by
      rw [add_mul, one_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← hξ i, norm_mul]

private theorem eLpNorm_weightedL2Fourier_le_coordinateDerivatives (s : ℝ)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : Fin d → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hv : ∀ i, HasEuclideanL2CoordinateDerivative i u (v i)) :
    eLpNorm (weightedL2Fourier (s + 1) u) 2 volume ≤
      eLpNorm (weightedL2Fourier s u) 2 volume +
      ∑ i, eLpNorm (weightedL2Fourier s (v i)) 2 volume := by
  let f := fun ξ ↦ ‖weightedL2Fourier s u ξ‖
  let g := fun i ξ ↦ ‖weightedL2Fourier s (v i) ξ‖
  calc
    _ ≤ eLpNorm (f + ∑ i, g i) 2 volume := by
      apply eLpNorm_mono_ae (aestronglyMeasurable_weightedL2Fourier _ _)
      filter_upwards [norm_weightedL2Fourier_le_coordinateDerivatives_ae s hv] with ξ hξ
      simpa [f, g, Real.norm_eq_abs, abs_of_nonneg (show
        0 ≤ ‖weightedL2Fourier s u ξ‖ + ∑ i, ‖weightedL2Fourier s (v i) ξ‖ by positivity)] using hξ
    _ ≤ eLpNorm f 2 volume + ∑ i, eLpNorm (g i) 2 volume :=
      (eLpNorm_add_le (by norm_num)).trans
        (add_le_add le_rfl (eLpNorm_sum_le (by norm_num)))
    _ = _ := by
      simp only [f, g, eLpNorm_norm _ (aestronglyMeasurable_weightedL2Fourier _ _)]

/-- Order `s` of the input and its actual coordinate derivatives implies order
`s + 1`, supplying the gain-one argument after
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem MemFourierSobolev.of_coordinateDerivatives {s : ℝ} (_hs : 0 ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : Fin d → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hu : MemFourierSobolev s u)
    (hv : ∀ i, MemFourierSobolev s (v i))
    (hderiv : ∀ i, HasEuclideanL2CoordinateDerivative i u (v i)) :
    MemFourierSobolev (s + 1) u := by
  apply (eLpNorm_weightedL2Fourier_le_coordinateDerivatives s hderiv).trans_lt
  exact ENNReal.add_lt_top.mpr ⟨hu.eLpNorm_lt_top,
    ENNReal.sum_lt_top.mpr (fun i _ ↦ (hv i).eLpNorm_lt_top)⟩

/-- Quantitative gain of one derivative with constant one, for
`app:ch_regular_base:eq:fio-input` and the argument following
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem fourierSobolevNorm_le_coordinateDerivatives {s : ℝ} (_hs : 0 ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : Fin d → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hu : MemFourierSobolev s u)
    (hv : ∀ i, MemFourierSobolev s (v i))
    (hderiv : ∀ i, HasEuclideanL2CoordinateDerivative i u (v i)) :
    fourierSobolevNorm (s + 1) u ≤
      fourierSobolevNorm s u + ∑ i, fourierSobolevNorm s (v i) := by
  have hvfinite := ENNReal.sum_ne_top.mpr (fun i (_ : i ∈ Finset.univ) ↦
    (hv i).eLpNorm_ne_top)
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hu.eLpNorm_ne_top, hvfinite⟩)
    (eLpNorm_weightedL2Fourier_le_coordinateDerivatives s hderiv)
  simpa only [ENNReal.toReal_add hu.eLpNorm_ne_top hvfinite,
    ENNReal.toReal_sum (fun i _ ↦ (hv i).eLpNorm_ne_top), fourierSobolevNorm] using h

private theorem coordinateDerivative_weightedL2Fourier_bound_ae (s : ℝ) {i : Fin d}
    {u v : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hv : HasEuclideanL2CoordinateDerivative i u v) :
    ∀ᵐ ξ ∂volume, ‖weightedL2Fourier s v ξ‖ ≤
      (2 * Real.pi) * ‖weightedL2Fourier (s + 1) u ξ‖ := by
  filter_upwards [hv.weightedL2Fourier_ae_eq s] with ξ hξ
  have hc : |ξ i| ≤ euclideanSobolevWeight 1 ξ :=
    (show |ξ i| ≤ ‖ξ‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i).trans
      (norm_le_euclideanSobolevWeight_one ξ)
  calc
    ‖weightedL2Fourier s v ξ‖ =
        (2 * Real.pi * |ξ i|) * ‖weightedL2Fourier s u ξ‖ := by
      rw [← hξ, norm_mul, norm_euclideanCoordinateDerivativeSymbol]
    _ ≤ (2 * Real.pi * euclideanSobolevWeight 1 ξ) * ‖weightedL2Fourier s u ξ‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity))
        (norm_nonneg _)
    _ = (2 * Real.pi) * ‖weightedL2Fourier (s + 1) u ξ‖ := by
      rw [norm_weightedL2Fourier, norm_weightedL2Fourier, euclideanSobolevWeight_add]
      ring

/-- Every actual coordinate derivative representative has order `s` when the
input has order `s + 1`, as used after
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem HasEuclideanL2CoordinateDerivative.memFourierSobolev {s : ℝ} (hs : 0 ≤ s)
    {i : Fin d} {u v : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hv : HasEuclideanL2CoordinateDerivative i u v)
    (hu : MemFourierSobolev (s + 1) u) : MemFourierSobolev s v := by
  obtain ⟨w, hw⟩ := hu.exists_coordinateDerivatives hs
  rw [hv.unique (hw i).1]
  exact (hw i).2

/-- A single coordinate derivative costs at most `2π` in the Fourier norm of
`app:ch_regular_base:eq:fio-input`, with the manuscript's derivative convention. -/
theorem HasEuclideanL2CoordinateDerivative.fourierSobolevNorm_le {s : ℝ} (_hs : 0 ≤ s)
    {i : Fin d} {u v : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hv : HasEuclideanL2CoordinateDerivative i u v)
    (hu : MemFourierSobolev (s + 1) u) :
    fourierSobolevNorm s v ≤ (2 * Real.pi) * fourierSobolevNorm (s + 1) u := by
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (aestronglyMeasurable_weightedL2Fourier s v) (coordinateDerivative_weightedL2Fourier_bound_ae s hv) 2
  have hfinite := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2 * Real.pi))
    hu.eLpNorm_ne_top
  have hre := ENNReal.toReal_mono hfinite he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.pi by positivity),
    fourierSobolevNorm] using hre

/-- The reverse first-derivative estimate with explicit dimension constant,
including dimension zero, for `app:ch_regular_base:eq:fio-input` and the gain-one
argument after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem fourierSobolevNorm_coordinateDerivatives_le {s : ℝ} (hs : 0 ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : Fin d → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hu : MemFourierSobolev (s + 1) u)
    (hderiv : ∀ i, HasEuclideanL2CoordinateDerivative i u (v i)) :
    fourierSobolevNorm s u + ∑ i, fourierSobolevNorm s (v i) ≤
      (1 + 2 * Real.pi * d) * fourierSobolevNorm (s + 1) u := by
  calc
    _ ≤ fourierSobolevNorm (s + 1) u +
        ∑ _i : Fin d, (2 * Real.pi) * fourierSobolevNorm (s + 1) u :=
      add_le_add (fourierSobolevNorm_mono hu (by linarith))
        (Finset.sum_le_sum (fun i _ ↦ (hderiv i).fourierSobolevNorm_le hs hu))
    _ = _ := by simp; ring

end JanetCartan.Pseudodifferential
