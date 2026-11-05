module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierRegularization.BoundedKernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Kernel

/-!
# Finite carrier masks

The finite regularization of `app:ch_background:eq:bg-T`, on the literal initial
product measure and normalized output torus. The geometric producers supply joint
kernel measurability and the amplitude bound. No operator estimate or adjoint
identity is included among the inputs. The continuum row and normal reduction
consume the constructed operator and its two almost-everywhere formulas.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace JanetCartan.ContinuumRow.CarrierRegularization

variable {n N : ℕ}

/-- Explicit mask on the literal carrier kernel (`app:ch_background:eq:bg-T`). -/
def maskedKernel (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (x : Torus n) (u : CarrierVariable n) : EuclideanSpace ℂ (Fin n) :=
  (m u : ℂ) • carrierKernel d x u

/-- Oscillation does not increase the real amplitude norm
(`app:ch_background:eq:bg-T`). -/
theorem norm_carrierKernel_le (d : CarrierData n N) (x : Torus n)
    (u : CarrierVariable n) : ‖carrierKernel d x u‖ ≤ ‖carrierAmplitude d x u‖ := by
  classical
  by_cases hx : x ∈ d.outputChart
  · simp [carrierKernel, hx, norm_smul, Complex.norm_exp,
      euclideanComplexInclusion_norm]
  · simp [carrierKernel, hx]

/-- Pointwise analytic inputs for finite regularization of
`app:ch_background:eq:bg-T`. `Z` is a fixed compact carrier-parameter set,
`R` the frequency radius, and `M` a bound for the real mask. These are supplied
by the geometric construction, not by an assumed L² bound. -/
structure MaskHypotheses (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (Z : Set CarrierParameter) (R M C : ℝ) : Prop where
  compact_parameters : IsCompact Z
  radius_nonneg : 0 ≤ R
  mask_bound_nonneg : 0 ≤ M
  amplitude_bound_nonneg : 0 ≤ C
  kernel_measurable : StronglyMeasurable (Function.uncurry (carrierKernel d))
  mask_measurable : StronglyMeasurable m
  mask_support : ∀ u, u ∉ Z ×ˢ Metric.closedBall 0 R → m u = 0
  mask_bound : ∀ u, |m u| ≤ M
  amplitude_bound : ∀ x u, ‖carrierAmplitude d x u‖ ≤ C * Real.sqrt ‖u.2‖

variable {d : CarrierData n N} {m : CarrierVariable n → ℝ}
  {Z : Set CarrierParameter} {R M C : ℝ}
  (h : MaskHypotheses d m Z R M C)

include h

namespace MaskHypotheses

/-- Joint measurability of the masked kernel (`app:ch_background:eq:bg-T`). -/
theorem maskedKernel_measurable : StronglyMeasurable (Function.uncurry (maskedKernel d m)) :=
  (Complex.continuous_ofReal.comp_stronglyMeasurable
    (h.mask_measurable.comp_measurable measurable_snd)).smul h.kernel_measurable

/-- The mask confines the source to a finite-measure product
(`app:ch_background:eq:bg-T`). -/
theorem mask_support_finite : carrierMeasure n (Z ×ˢ Metric.closedBall 0 R) ≠ ∞ := by
  rw [carrierMeasure, Measure.prod_prod]
  exact ENNReal.mul_ne_top h.compact_parameters.measure_lt_top.ne
    (isCompact_closedBall (0 : Euclidean (n - 1)) R).measure_lt_top.ne

/-- Literal compact source support (`app:ch_background:eq:bg-T`). -/
theorem maskedKernel_support (x : Torus n) (u : CarrierVariable n)
    (hu : u ∉ Z ×ˢ Metric.closedBall 0 R) : maskedKernel d m x u = 0 := by
  simp [maskedKernel, h.mask_support u hu]

/-- The finite-frequency bound, before any oscillatory estimate
(`app:ch_background:eq:bg-T`). -/
theorem maskedKernel_bound (x : Torus n) (u : CarrierVariable n) :
    ‖maskedKernel d m x u‖ ≤ M * C * Real.sqrt R := by
  by_cases hu : u ∈ Z ×ˢ Metric.closedBall 0 R
  · have hr : ‖u.2‖ ≤ R := by simpa using hu.2
    calc
      ‖maskedKernel d m x u‖ = |m u| * ‖carrierKernel d x u‖ := by
        simp [maskedKernel, norm_smul]
      _ ≤ M * (C * Real.sqrt ‖u.2‖) := mul_le_mul
        (h.mask_bound u) ((norm_carrierKernel_le d x u).trans (h.amplitude_bound x u))
        (norm_nonneg _) h.mask_bound_nonneg
      _ ≤ M * (C * Real.sqrt R) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr) h.amplitude_bound_nonneg)
        h.mask_bound_nonneg
      _ = _ := by ring
  · rw [h.maskedKernel_support x u hu, norm_zero]
    exact mul_nonneg (mul_nonneg h.mask_bound_nonneg h.amplitude_bound_nonneg)
      (Real.sqrt_nonneg _)

/-- The actual bounded complex finite regularization
(`app:ch_background:eq:bg-T`). -/
def operator : CarrierL2 n →L[ℂ] ComplexOutputL2 n :=
  boundedKernelOperator h.maskedKernel_measurable
    (h.compact_parameters.measurableSet.prod measurableSet_closedBall)
    h.mask_support_finite h.maskedKernel_support h.maskedKernel_bound

/-- AE integral formula on the full initial L² quotient
(`app:ch_background:eq:bg-T`). -/
theorem operator_ae (f : CarrierL2 n) :
    h.operator f =ᵐ[volume] regularizedCarrierIntegral d m f := by
  filter_upwards [boundedKernelOperator_ae h.maskedKernel_measurable
    (h.compact_parameters.measurableSet.prod measurableSet_closedBall)
    h.mask_support_finite h.maskedKernel_support h.maskedKernel_bound f] with x hx
  change h.operator f x = _ at hx
  rw [hx]
  unfold regularizedCarrierIntegral carrierTestIntegral
  apply integral_congr_ae
  exact Eventually.of_forall fun u ↦ by
    simp only [maskedKernel, smul_smul, mul_comm]

/-- Actual Hilbert adjoint on the full output L² quotient. The real mask is
unchanged by conjugation (`app:ch_background:eq:bg-realification`). -/
theorem operator_adjoint_ae (w : ComplexOutputL2 n) :
    h.operator.adjoint w =ᵐ[carrierMeasure n]
      fun u ↦ (m u : ℂ) * carrierAdjointIntegral d w u := by
  filter_upwards [boundedKernelOperator_adjoint_ae h.maskedKernel_measurable
    (h.compact_parameters.measurableSet.prod measurableSet_closedBall)
    h.mask_support_finite h.maskedKernel_support h.maskedKernel_bound w] with u hu
  change h.operator.adjoint w u = _ at hu
  rw [hu]
  simp only [maskedKernel, inner_smul_left]
  simp [carrierAdjointIntegral, integral_const_mul]

/-- Independence of the source representative in the L² quotient
(`app:ch_background:eq:bg-T`). -/
theorem operator_ae_of_representative (f : CarrierL2 n)
    (g : CarrierVariable n → ℂ) (hg : (f : CarrierVariable n → ℂ) =ᵐ[carrierMeasure n] g) :
    h.operator f =ᵐ[volume] regularizedCarrierIntegral d m g := by
  filter_upwards [h.operator_ae f] with x hx
  rw [hx]
  unfold regularizedCarrierIntegral carrierTestIntegral
  exact integral_congr_ae (hg.mono (fun u hu ↦ by dsimp only; rw [hu]))

/-- Independence of the output representative in the literal Hilbert adjoint
(`app:ch_background:eq:bg-realification`). -/
theorem operator_adjoint_ae_of_representative (w : ComplexOutputL2 n)
    (v : Torus n → EuclideanSpace ℂ (Fin n))
    (hv : (w : Torus n → EuclideanSpace ℂ (Fin n)) =ᵐ[volume] v) :
    h.operator.adjoint w =ᵐ[carrierMeasure n]
      fun u ↦ (m u : ℂ) * carrierAdjointIntegral d v u := by
  filter_upwards [h.operator_adjoint_ae w] with u hu
  rw [hu]
  congr 1
  exact integral_congr_ae (hv.mono (fun x hx ↦ by dsimp only; rw [hx]))

/-- The literal masked source integral is absolutely convergent for every
output point and every L² input (`app:ch_background:eq:bg-T`). -/
theorem integrable_regularized_source (f : CarrierL2 n) (x : Torus n) :
    Integrable (fun u ↦ ((m u : ℂ) * f u) • carrierKernel d x u)
      (carrierMeasure n) := by
  have hi := integrable_source h.maskedKernel_measurable
    (h.compact_parameters.measurableSet.prod measurableSet_closedBall)
    h.mask_support_finite h.maskedKernel_support h.maskedKernel_bound f x
  simpa only [maskedKernel, smul_smul, mul_comm] using hi

/-- Absolute integrability of the literal product pairing proves the Fubini
step for all L² inputs and outputs (`app:ch_background:eq:bg-realification`). -/
theorem integrable_regularized_pairing (f : CarrierL2 n) (w : ComplexOutputL2 n) :
    Integrable (fun p : Torus n × CarrierVariable n ↦
      inner ℂ (((m p.2 : ℂ) * f p.2) • carrierKernel d p.1 p.2) (w p.1))
      (volume.prod (carrierMeasure n)) := by
  have hi := integrable_pairing h.maskedKernel_measurable
    (h.compact_parameters.measurableSet.prod measurableSet_closedBall)
    h.mask_support_finite h.maskedKernel_support h.maskedKernel_bound f w
  simpa only [maskedKernel, smul_smul, mul_comm] using hi

end MaskHypotheses

end JanetCartan.ContinuumRow.CarrierRegularization
