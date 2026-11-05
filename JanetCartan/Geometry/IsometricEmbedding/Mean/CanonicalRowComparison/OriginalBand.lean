module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.TransportNormal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.CarrierBands

/-!
# Identify a transport band with the original raw carrier cutoff

The fixed external sampling weight equals one on the retained detector.
Consequently it disappears from the literal kernel, including at zero
weights. The existing continuum realization supplies its literal adjoint
formula. This identifies the constructed band with that SAME operator
composed with the original raw band multiplier. The Fourier scalar remains
explicit; neither the operator nor the inverse is reselected.

Consumers: the finite reference normal in `CanonicalTailRealization.RawNormal`
and the original-row comparison for `app:ch_mean_pairs:eq:mean-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison
open ContinuumRow RawInputPartition RawCutoffBounds CanonicalTailRealization
open SeparatedSampling PeriodicLocalL2 AmplitudeBound

variable {n N : ℕ}

/-- The original external-weight plateau removes the square root of the
sampling weight only on the SAME detector support. The physical Fourier
scalar and smooth band are unchanged (`app:ch_waves:eq:sampling-prefix-normal`,
`app:ch_background:eq:bg-T`). -/
theorem maskedCarrierKernel_transportBandMask_eq_original
    (d : CarrierData n N) (j : ℕ) (ψ : Point → ℝ)
    (hψone : ∀ z η, d.angularCutoff z η ≠ 0 → ψ (carrierSamplingEquiv z) = 1)
    (x : Torus n) (u : CarrierVariable n) :
    maskedCarrierKernel d (transportBandMask n j ψ) x u =
      (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        maskedCarrierKernel d (carrierBand n j) x u := by
  by_cases ha : d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) = 0
  · have hz : carrierKernel d x u = 0 := by
      classical
      by_cases hx : x ∈ d.outputChart <;>
        simp [carrierKernel, carrierAmplitude, hx, ha]
    simp [maskedCarrierKernel, hz]
  · simp only [maskedCarrierKernel, transportBandMask, hψone _ _ ha,
      Real.sqrt_one, mul_one, Complex.ofReal_mul, mul_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl

variable {bands : ℕ}
    (d : CarrierData n N)
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    (Yext : Point × Euclidean n → Euclidean (n - 1))
    (hY : Continuous Yext)
    (hA : Continuous (fun q : (Point × Euclidean n) × Euclidean (n - 1) ↦
      transportCrossBandAmplitude d C q.1.1 q.1.2 q.2))
    (K : Set (Euclidean n)) (hK : IsCompact K)
    (hsupport : ∀ z x η, x ∉ K → transportCrossBandAmplitude d C z x η = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z x η, ‖transportCrossBandAmplitude d C z x η‖ ≤ M)
    (hpoint : ∀ x, d.chartPoint x = centeredTorusRepresentative x)
    (hC : ∀ x, C (centeredTorusRepresentative x) = CurrentMean.preparationMeasurement d x)
    (hphase : ∀ x z η, transportCrossBandAmplitude d C (carrierSamplingEquiv z)
      (centeredTorusRepresentative x) η ≠ 0 →
      inner ℝ (Yext (carrierSamplingEquiv z, centeredTorusRepresentative x)) η =
        carrierPhase d x (z, η))
    (ψ : Point → ℝ) {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ)
    (hψone : ∀ z η, d.angularCutoff z η ≠ 0 → ψ (carrierSamplingEquiv z) = 1)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ q, U.adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral d q)

local notation "T" => transportBandContinuumOperator (bands := bands) d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase

include hψone hU

/-- The constructed transport band has the original raw adjoint, followed
by the SAME band multiplier. `hU` is precisely the literal-adjoint conclusion
of the continuum-row realization; no normal comparison is assumed. Both
complex quadratures and the real polarization factor two are retained
(`app:ch_background:eq:bg-realification`, `app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem transportBandContinuumOperator_adjoint_eq_original
    (j : Fin bands) (q : ComplexOutputL2 n) :
    (T j ψ hψ hc).adjoint q =
      (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        carrierMultiplier (dyadicCarrierBandMask n j.val) (U.adjoint q) := by
  apply Lp.ext
  filter_upwards [carrier_adjoint_ae_eq_integral d (transportBandMask n j.val ψ)
      (transportBandFiniteKernelBounds d C Yext hY hA K hK hsupport M hM hbound
        hpoint hC hphase j ψ hψ hc) (T j ψ hψ hc)
      (transportBandContinuumOperator_ae d C Yext hY hA K hK hsupport M hM hbound
        hpoint hC hphase j ψ hψ hc) q,
    Lp.coeFn_smul ((2 * Real.pi) ^ (-(n : ℝ) / 2))
      (carrierMultiplier (dyadicCarrierBandMask n j.val) (U.adjoint q)),
    carrierMultiplier_coeFn (dyadicCarrierBandMask n j.val) (U.adjoint q),
    dyadicCarrierBandMask_coeFn n j.val, hU q] with u ht hs hm hb hu
  rw [ht, hs, Pi.smul_apply, hm, hb, hu]
  simp_rw [maskedCarrierKernel_transportBandMask_eq_original d j.val ψ hψone]
  simp only [maskedCarrierKernel, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
    Complex.conj_ofReal, integral_const_mul, smul_eq_mul, carrierAdjointIntegral]
  simp only [RCLike.conj_ofReal]
  rfl

/-- Identify the actual real transport band with a cutoff of the ORIGINAL
carrier. The raw multiplier remains before the operator and hence after its
adjoint, before the fixed inverse is ever applied
(`app:ch_mean_pairs:defn:mean-canonical`, `main:eq:linear-two-errors`). -/
theorem real_transportBandContinuumOperator_eq_original
    (j : Fin bands) :
    realQuadratureChannel (T j ψ hψ hc) =
      (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        (carrierChannel U).comp (carrierMultiplier (dyadicCarrierBandMask n j.val)) := by
  apply ContinuousLinearMap.adjoint.injective
  rw [map_smul, ContinuousLinearMap.adjoint_comp, carrierMultiplier_adjoint]
  ext1 q
  rw [realQuadratureChannel_adjoint_apply,
    transportBandContinuumOperator_adjoint_eq_original d C Yext hY hA K hK hsupport M hM hbound
      hpoint hC hphase ψ hψ hc hψone U hU,
    smul_apply, ContinuousLinearMap.comp_apply,
    carrierChannel_adjoint_apply, map_smul]
  exact smul_comm _ _ _

end JanetCartan.CanonicalRowComparison
