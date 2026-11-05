module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.TransportAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RawBandBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Disintegration
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.OutputTransfer

/-!
# Literal transport bands for the canonical cross row

Construct the zero endpoint of `app:ch_waves:eq:colored-normal-comparison`
from the same principal matrix and the same detector, high-pass and smooth
band. The phase is the actual transport differential, rather than the
nonzero quotient evaluated at zero. A supplied continuous phase extension
need agree with the original differential only where the measured coefficient
is nonzero. The constructor uses the existing `BandKernelData`; its inputs
are continuity, support and coefficient bounds.

The Fourier scalar of `RawKernel.bandKernelData` remains explicit in the
forward comparison with `ContinuumRow.carrierKernel`. Consequently the
normal reconstruction must retain its square and the original carrier weight.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison

open ContinuumRow CurrentMean LeadingWave Sampling Sampling.RawKernel
open Sampling.MeanNormalBound SamplingKernelBounds RawInputPartition PeriodicLocalL2
open AmplitudeBound

variable {n N bands : ℕ}

/-- The zero-endpoint cross coefficient, with the original detector and
high-pass and the uncut principal background
(`app:ch_waves:eq:colored-normal-comparison`). -/
def transportCrossBandAmplitude (d : CarrierData n N)
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    (z : SeparatedSampling.Point) (x : Euclidean n) (η : Euclidean (n - 1)) :
    EuclideanSpace ℂ (Fin n) :=
  (d.angularCutoff (carrierSamplingEquiv.symm z) (‖η‖⁻¹ • η) * d.highCutoff ‖η‖) •
    complexCrossMeasurement (C x)
      ((principalMatrix (d.normalField x (carrierSamplingEquiv.symm z))
        (d.covector x (carrierSamplingEquiv.symm z))).map Complex.ofReal)
      ((principalMatrix (d.normalField x (carrierSamplingEquiv.symm z))
        (d.covector x (carrierSamplingEquiv.symm z))).map Complex.ofReal)

variable (d : CarrierData n N)
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    (Yext : SeparatedSampling.Point × Euclidean n → Euclidean (n - 1))
    (hY : Continuous Yext)
    (hA : Continuous (fun q : (SeparatedSampling.Point × Euclidean n) ×
      Euclidean (n - 1) ↦ transportCrossBandAmplitude d C q.1.1 q.1.2 q.2))
    (K : Set (Euclidean n)) (hK : IsCompact K)
    (hsupport : ∀ z x η, x ∉ K → transportCrossBandAmplitude d C z x η = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z x η, ‖transportCrossBandAmplitude d C z x η‖ ≤ M)

/-- A transport sampling band from the supplied continuous phase extension,
using the unchanged smooth radial partition and physical Fourier normalization
(`app:ch_waves:eq:colored-normal-comparison`, `app:ch_background:eq:bg-T`). -/
def transportCrossBandKernelData : BandKernelData (Fin bands × SeparatedSampling.Point) n :=
  let D := bandKernelData (J := bands) (fun _ _ _ ↦ (0 : ℝ))
    (transportCrossBandAmplitude d C) (fun _ ↦ 0) (fun _ ↦ 1) (fun _ ↦ 1)
    continuous_const hA continuous_const continuous_const (fun _ ↦ one_ne_zero)
    continuous_const K hK hsupport M 1 hM zero_le_one hbound (fun _ ↦ by simp)
  { D with
    phase := fun q ↦ inner ℝ (Yext (q.1.1.2, q.2)) q.1.2
    phase_continuous :=
      (hY.comp (f := fun q : ((Fin bands × SeparatedSampling.Point) ×
        Euclidean (n - 1)) × Euclidean n ↦ (q.1.1.2, q.2)) (by fun_prop)).inner
        (by fun_prop) }

local notation "D₀" => transportCrossBandKernelData (bands := bands) d C Yext hY hA K hK hsupport M hM hbound

/-- The constructed kernel vanishes off its ORIGINAL wide band. This uses
the smooth radial mask, not a sharp indicator in the amplitude
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem transportCrossBandKernelData_eq_zero_off_wideBand
    (j : Fin bands) (z : SeparatedSampling.Point) (η : Euclidean (n - 1))
    (x : Euclidean n) (hη : η ∉ wideBand n j.val) :
    (D₀).kernel (j, z) η x = 0 := by
  simp [BandKernelData.kernel, bandKernel, transportCrossBandKernelData,
    bandKernelData, measuredBandAmplitude, radialBand_eq_zero_off_wideBand hη]

variable (hpoint : ∀ x, d.chartPoint x = centeredTorusRepresentative x)
    (hC : ∀ x, C (centeredTorusRepresentative x) = preparationMeasurement d x)
    (hphase : ∀ x z η, transportCrossBandAmplitude d C (carrierSamplingEquiv z)
      (centeredTorusRepresentative x) η ≠ 0 →
      inner ℝ (Yext (carrierSamplingEquiv z, centeredTorusRepresentative x)) η =
        carrierPhase d x (z, η))

include hpoint hC in
/-- The original continuum kernel has the same measured principal coefficient
as the transport sampling constructor. The equality retains the original
local phase and uses no global extension of the carrier data
(`app:ch_background:eq:bg-T`, `app:ch_waves:eq:colored-normal-comparison`). -/
theorem carrierKernel_eq_transportCrossAmplitude
    (x : Torus n) (z : CarrierParameter) (η : Euclidean (n - 1)) :
    carrierKernel d x (z, η) =
      Complex.exp (Complex.I * (carrierPhase d x (z, η) : ℂ)) •
        (Real.sqrt ‖η‖ : ℂ) •
          transportCrossBandAmplitude d C (carrierSamplingEquiv z)
            (centeredTorusRepresentative x) η := by
  rw [carrierKernel_eq_principal_cross]
  simp only [transportCrossBandAmplitude, MeasurableEquiv.symm_apply_apply, hpoint, hC,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  ring_nf
  rfl

include hpoint hC hphase

/-- The actual constructed zero kernel is the original continuum kernel
times its smooth band and the explicit Fourier scalar. All measurements,
normal fields, covectors, cutoffs and phases are those of the SAME `d`
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem transportCrossBandKernelData_kernel_on_torus
    (j : Fin bands) (z : CarrierParameter) (η : Euclidean (n - 1)) (x : Torus n) :
    (D₀).kernel (j, carrierSamplingEquiv z) η (centeredTorusRepresentative x) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * radialBand n j.val η) •
        carrierKernel d x (z, η) := by
  rw [carrierKernel_eq_transportCrossAmplitude d C hpoint hC]
  simp only [BandKernelData.kernel, bandKernel, transportCrossBandKernelData,
    bandKernelData, measuredBandAmplitude, zero_add, one_smul, mul_one]
  by_cases ha : transportCrossBandAmplitude d C (carrierSamplingEquiv z)
      (centeredTorusRepresentative x) η = 0
  · simp only [ha, smul_zero]
  rw [hphase x z η ha]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_mul, smul_smul]
  congr 1
  push_cast
  simp only [mul_comm, mul_assoc]
  rfl

/-- The literal zero transport band on the original raw wide-band space
has the original continuum slice integral after output-only torus transfer.
No adjoint or normal equality is a hypothesis
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem transportCrossBandKernelData_wideOperator_ae_slice
    (j : Fin bands) (z : CarrierParameter) (f : WideBandL2 n j.val) :
    transferOutputOperator (wideBandKernelOperator D₀ j.val (j, carrierSamplingEquiv z)) f
      =ᵐ[volume] regularizedCarrierSliceIntegral d
        (fun u ↦ (2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j.val u) z f := by
  have hf := wideBandKernelOperator_ae_integral D₀ j.val (j, carrierSamplingEquiv z)
    (fun η hη x ↦ transportCrossBandKernelData_eq_zero_off_wideBand
      d C Yext hY hA K hK hsupport M hM hbound j _ η x hη) f
  filter_upwards [toTorus_coe (𝕜 := ℂ)
      (wideBandKernelOperator D₀ j.val (j, carrierSamplingEquiv z) f),
    measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp hf.restrict]
      with x hx he
  change toTorus (𝕜 := ℂ) (wideBandKernelOperator D₀ j.val (j, carrierSamplingEquiv z) f) x = _
  rw [hx, he]
  dsimp only [Function.comp_apply]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη ↦ by
    rw [transportCrossBandKernelData_eq_zero_off_wideBand
      d C Yext hY hA K hK hsupport M hM hbound j _ η _ hη, smul_zero])]
  dsimp only [Function.comp_apply, regularizedCarrierSliceIntegral, maskedCarrierKernel,
    carrierBand]
  apply integral_congr_ae
  filter_upwards [] with η
  rw [transportCrossBandKernelData_kernel_on_torus d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase]
  rfl

end JanetCartan.CanonicalRowComparison
