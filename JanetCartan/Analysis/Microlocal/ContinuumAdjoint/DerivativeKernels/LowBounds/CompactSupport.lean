module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension.Tests

/-!
# Compact regularization of modified kernels

Primitive support and continuity give absolute convergence of the normal
integrand for `app:ch_background:prop:bg-adjoint`. No bound on the unregularized
operator is used. The input measure remains the shared literal `dz dη` measure.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open ContinuumRow NormalComparison

variable {n : ℕ}

/-- Joint continuity for the actual compact regularization of an arbitrary
modified amplitude (`app:ch_background:prop:bg-adjoint`). -/
theorem continuous_modifiedCarrierKernel
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
    (ha : Continuous (fun p : Euclidean n × CarrierVariable n ↦ a p.2.1 p.1 p.2.2))
    (hm : Continuous m) :
    Continuous (Function.uncurry (modifiedCarrierKernel Φ a m)) := by
  exact ((Complex.continuous_ofReal.comp (hm.comp continuous_snd)).mul
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul hΦ))).cexp).mul
      ha.star

/-- Compact carrier regularization and a common compact measurement support
give joint compact support (`app:ch_background:prop:bg-adjoint`). -/
theorem hasCompactSupport_modifiedCarrierKernel
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hm : HasCompactSupport m)
    (ha : ∀ u : CarrierVariable n, ∀ x, x ∉ K → a u.1 x u.2 = 0) :
    HasCompactSupport (Function.uncurry (modifiedCarrierKernel Φ a m)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hK.prod hm)
  intro p hp
  constructor
  · by_contra hx
    exact hp (by simp [Function.uncurry, modifiedCarrierKernel, ha p.2 p.1 hx])
  · by_contra hu
    exact hp (by simp [Function.uncurry, modifiedCarrierKernel,
      image_eq_zero_of_notMem_tsupport hu])

/-- Compact carrier support alone suffices for absolute integrability of the
paired kernel at any two measurement positions
(`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_modifiedNormalKernel_integrand
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (hΦ : Continuous (fun p : Euclidean n × CarrierVariable n ↦ Φ p.2.1 p.1 p.2.2))
    (ha : Continuous (fun p : Euclidean n × CarrierVariable n ↦ a p.2.1 p.1 p.2.2))
    (hm : Continuous m) (hs : HasCompactSupport m) (x y : Euclidean n) :
    Integrable (fun u ↦ oscillatoryFactor 1 (Φ u.1 x u.2 - Φ u.1 y u.2) *
      modifiedNormalDensity a m x y u) (carrierMeasure n) := by
  have hc := continuous_modifiedCarrierKernel Φ a m hΦ ha hm
  have hx : Continuous (modifiedCarrierKernel Φ a m x) :=
    hc.comp (continuous_const.prodMk continuous_id)
  have hy : Continuous (modifiedCarrierKernel Φ a m y) :=
    hc.comp (continuous_const.prodMk continuous_id)
  have hsx : HasCompactSupport (modifiedCarrierKernel Φ a m x) := by
    apply HasCompactSupport.of_support_subset_isCompact hs
    intro u hu
    by_contra hn
    exact hu (by simp [modifiedCarrierKernel, image_eq_zero_of_notMem_tsupport hn])
  have hi := (hx.mul hy.star).integrable_of_hasCompactSupport (μ := carrierMeasure n)
    hsx.mul_right
  change Integrable (fun u ↦ modifiedCarrierKernel Φ a m x u *
    star (modifiedCarrierKernel Φ a m y u)) (carrierMeasure n) at hi
  simpa only [modifiedCarrierKernel_mul_star] using hi

/-- The literal adjoint of a compact regularization uses the same published
`chartAdjoint` as the derivative recursion
(`app:ch_background:prop:bg-adjoint`). -/
theorem integral_star_modifiedCarrierKernel
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ)
    (v : Euclidean n → ℂ) (u : CarrierVariable n) :
    (∫ x, star (modifiedCarrierKernel Φ a m x u) * v x) =
      (m u : ℂ) * chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v := by
  rw [chartAdjoint, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have he : star (oscillatoryFactor 1 (Φ u.1 x u.2)) =
      oscillatoryFactor (-1) (Φ u.1 x u.2) := by
    unfold oscillatoryFactor
    change (starRingEnd ℂ) (Complex.exp _) = _
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, one_mul, neg_one_mul,
      Complex.ofReal_neg]
    ring
  simp only [modifiedCarrierKernel, star_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_conj] at he ⊢
  rw [he]
  ring

/-- Compact regularizations converging to one recover the literal adjoint
pointwise. No interchange of limits and a noncompact integral is needed
(`app:ch_background:prop:bg-adjoint`). -/
theorem tendsto_integral_star_modifiedCarrierKernel
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (a : AdjointAmplitude n) (m : ℕ → CarrierVariable n → ℝ)
    (v : Euclidean n → ℂ) (u : CarrierVariable n)
    (hm : Tendsto (fun k ↦ m k u) atTop (𝓝 1)) :
    Tendsto (fun k ↦ ∫ x, star (modifiedCarrierKernel Φ a (m k) x u) * v x)
      atTop (𝓝 (chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v)) := by
  simp_rw [integral_star_modifiedCarrierKernel]
  simpa only [Function.comp_def, Complex.ofReal_one, one_mul] using
    ((Complex.continuous_ofReal.tendsto 1).comp hm).mul_const
      (chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v)

/-- Absolute integrability survives the genuine inverse-Jacobian substitution
at fixed spectator. This discharges the sectionwise change-of-variables
obligation without assuming an integrability statement about the transformed
density (`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_modifiedInverseDensity
    (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (x y : Euclidean n)
    (e : Euclidean n ≃ᵐ TransportKernel.SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (v : Euclidean 2) (hD : MeasurableSet (D v))
    (hΨ : ∀ t ∈ D v, HasFDerivWithinAt (Ψ v) (J v t) (D v) t)
    (hinj : InjOn (Ψ v) (D v)) (hU : ∀ t ∈ D v, U v (Ψ v t) = t)
    (hJ : ∀ t ∈ D v, (J v t).det ≠ 0)
    (hint : IntegrableOn (fun t ↦ modifiedNormalDensity a m x y
      (TransportKernel.chartCarrierVariable e v t)) (D v)) :
    Integrable (modifiedInverseDensity a m x y e D Ψ U J v) := by
  apply (integrable_indicator_iff (measurable_image_of_fderivWithin hD hΨ hinj)).mpr
  apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD hΨ hinj _).mpr
  apply hint.congr
  filter_upwards [ae_restrict_mem hD] with t ht
  simp only [hU t ht, smul_smul,
    mul_inv_cancel₀ (abs_ne_zero.mpr (hJ t ht)), one_smul]

end JanetCartan.ContinuumAdjoint.DerivativeKernels
