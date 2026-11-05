module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullScalarKernel.Integrability

/-!
# Removing the physical Fourier truncation

For `app:ch_osc:lem:osc-amplitude`, the summable physical coefficient bounds
justify integrating the exact Fourier expansion over compact frequency support
and all input positions. This gives pointwise convergence of the finite literal
kernels to the original amplitude kernel for every L² input.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology RealInnerProductSpace
namespace JanetCartan.AmplitudeBound

variable {d : ℕ}
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
  {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (hf : ∀ ξ, ContDiff ℝ ∞ (b ξ))
  (A : ℝ) (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)
  (hderiv : ∀ ξ i z,
    ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) z‖ ≤ A)

include hb hd hℓ hR hs hf A hzero hderiv

/-- Removing the physical Fourier truncation at any fixed frequency radius
recovers the literal original kernel, at every output point and for every L²
input (`app:ch_osc:lem:osc-amplitude`). The interchange follows from the exact
Fourier expansion and a summable integrable majorant. -/
theorem tendsto_boxFiniteAmplitudeKernel_fixed_frequency (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun s : Finset (Fin (2 * d) → ℤ) ↦
      boxFiniteAmplitudeKernel b ℓ s ρ f x) atTop
      (𝓝 (boxScalarAmplitudeKernel b ρ f x)) := by
  classical
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (Metric.closedBall 0 ρ)
  let w (k : Fin (2 * d) → ℤ) : ℝ :=
    (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A)) * twoPositionWeight d k
  let F (k : Fin (2 * d) → ℤ)
      (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℂ :=
    Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I) *
      ((boxCellCutoff ℓ x * UnitAddTorus.mFourier k (leftPositionChart ℓ x)) *
        UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ (b p.1)) k *
        (boxCellCutoff ℓ p.2 * UnitAddTorus.mFourier k (rightPositionChart ℓ p.2))) * f p.2
  have hw : Summable w := (summable_twoPositionWeight d).mul_left _
  have hA : 0 ≤ A := (norm_nonneg (b 0 0)).trans (hzero 0 0)
  have hc (ξ : EuclideanSpace ℝ (Fin d)) (k : Fin (2 * d) → ℤ) :
      ‖UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ (b ξ)) k‖ ≤ w k :=
    norm_mFourierCoeff_le_twoPositionWeight hd
      (isSmoothPeriodic_boxAmplitudePeriodization hℓ hR (hs ξ) (hf ξ))
      (norm_boxAmplitudePeriodization_le_factor (hzero ξ) ℓ)
      (norm_pureDeriv_boxAmplitudePeriodization_le_factor hℓ hR (hs ξ) (hf ξ) hA
        (hderiv ξ)) k
  have hFm (k : Fin (2 * d) → ℤ) : AEStronglyMeasurable (F k) (μ.prod volume) := by
    have hp : Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I)) := by fun_prop
    have hcoeff := (stronglyMeasurable_parameter_mFourierCoeff
      (fun ξ ↦ boxAmplitudePeriodization ℓ (b ξ))
      (stronglyMeasurable_boxAmplitudePeriodization hb ℓ) k)
    have hr := ((UnitAddTorus.mFourier k).continuous.measurable.comp
      (measurable_rightPositionChart ℓ)).stronglyMeasurable
    exact (hp.aestronglyMeasurable.mul
      ((aestronglyMeasurable_const.mul hcoeff.aestronglyMeasurable.comp_fst).mul
        ((aestronglyMeasurable_boxCellCutoff ℓ).comp_snd.mul
          hr.aestronglyMeasurable.comp_snd))).mul (Lp.aestronglyMeasurable f).comp_snd
  have hbound (k : Fin (2 * d) → ℤ)
      (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
      ‖F k p‖ ≤ w k * ‖boxCellCutoff ℓ p.2 * f p.2‖ := by
    dsimp only [F]
    simp only [norm_mul, ← Real.fourierChar_apply, Circle.norm_coe, one_mul]
    calc
      _ ≤ ((1 * 1) * w k * (‖boxCellCutoff ℓ p.2‖ * 1)) * ‖f p.2‖ := by
        gcongr
        · simpa using (norm_nonneg _).trans (hc p.1 k)
        · exact norm_boxCellCutoff_le ℓ x
        · exact norm_mFourier_apply_le_one k _
        · exact hc p.1 k
        · exact norm_mFourier_apply_le_one k _
      _ = _ := by ring
  -- Compact frequency volume and the physical cutoff make the majorant integrable.
  have hmajor (c : ℝ) : Integrable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        c * ‖boxCellCutoff ℓ p.2 * f p.2‖) (μ.prod volume) := by
    have hi : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) ↦ c)
        (Metric.closedBall 0 ρ) :=
      integrableOn_const (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ).measure_ne_top
    exact hi.mul_prod (integrable_boxCellCutoff_mul hℓ.ne' f).norm
  have hFi (k : Fin (2 * d) → ℤ) : Integrable (F k) (μ.prod volume) :=
    (hmajor (w k)).mono' (hFm k) (Eventually.of_forall (hbound k))
  -- Integrate the exact Fourier expansion using its summable coefficient bounds.
  have hsum := hasSum_integral_of_dominated_convergence
    (μ := μ.prod volume) (F := F)
    (f := fun p ↦ Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I) *
      b p.1 (pairedPosition x p.2) * f p.2)
    (fun k p ↦ w k * ‖boxCellCutoff ℓ p.2 * f p.2‖) hFm
    (fun k ↦ Eventually.of_forall (hbound k))
    (Eventually.of_forall (fun p ↦ hw.mul_right ‖boxCellCutoff ℓ p.2 * f p.2‖))
    (by simpa only [tsum_mul_right] using hmajor (∑' k, w k))
    (Eventually.of_forall (fun p ↦
      ((hasSum_boxAmplitude_expansion hd hℓ hR (hs p.1) (hf p.1)
        (hzero p.1) (hderiv p.1) x p.2).mul_left
          (Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I))).mul_right (f p.2)))
  -- Fubini identifies both product integrals with the literal iterated kernels.
  have hfull : (∫ p, Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I) *
      b p.1 (pairedPosition x p.2) * f p.2 ∂μ.prod volume) =
      boxScalarAmplitudeKernel b ρ f x :=
    integral_prod _ (integrable_boxScalarAmplitudeKernel_prod b hb hℓ hR hs A hzero ρ f x)
  rw [hfull] at hsum
  have hfinite (s : Finset (Fin (2 * d) → ℤ)) :
      (∑ k ∈ s, ∫ p, F k p ∂μ.prod volume) = boxFiniteAmplitudeKernel b ℓ s ρ f x := by
    rw [← integral_finsetSum s (fun k _ ↦ hFi k),
      integral_prod _ (integrable_finsetSum s (fun k _ ↦ hFi k))]
    simp only [boxFiniteAmplitudeKernel, regularizedPhysicalAmplitudeKernel,
      finiteCutoffAmplitude, Finset.mul_sum, Finset.sum_mul, F, μ]
  change Tendsto (fun s ↦ ∑ k ∈ s, ∫ p, F k p ∂μ.prod volume) atTop
    (𝓝 (boxScalarAmplitudeKernel b ρ f x)) at hsum
  simpa only [hfinite] using hsum

end JanetCartan.AmplitudeBound
