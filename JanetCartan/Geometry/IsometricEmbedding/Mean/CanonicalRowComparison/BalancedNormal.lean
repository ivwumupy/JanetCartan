module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.BalancedTransport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.OriginalPrefix

/-!
# Construct and reassemble the balanced transport bands

The bounded-kernel construction is applied to the literal balanced weights
and angular masks. Their measurability, compact support and kernel bounds
are derived from the original transport band. The normal densities then
identify their finite sum with the parent transport normal, on the original
carrier measure and with the original Fourier scalar.

Consumer: the finite-copy transport endpoint in
`app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison
open ContinuumRow RawInputPartition Sampling SeparatedSampling AmplitudeBound

variable {n N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- The SAME balanced detector and shared carrier weight, on the literal
initial variables. The zero-atom background has no such input mask
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_waves:eq:background-quadrature`). -/
def balancedTransportBandMask (n j : ℕ) (ψ : Point → ℝ) (b : I → Point → ℝ)
    (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ a, ηb a ≠ 0) (hr : ∀ a, 0 < r a) (s : Finset I) (a : s)
    (u : CarrierVariable n) : ℝ :=
  transportBandMask n j (balancedCarrierSubsetWeight ψ b s) u *
    balancedSubsetAngularMask ηb r hηb hr s a u.2

/-- The balanced mask multiplies only the ORIGINAL transport input kernel;
it preserves the phase, measurement and half derivative
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem maskedCarrierKernel_balancedTransportBandMask
    (d : CarrierData n N) (j : ℕ) (ψ : Point → ℝ) (b : I → Point → ℝ)
    (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ a, ηb a ≠ 0) (hr : ∀ a, 0 < r a)
    (s : Finset I) (a : s) (x : Torus n) (u : CarrierVariable n) :
    maskedCarrierKernel d (balancedTransportBandMask n j ψ b ηb r hηb hr s a) x u =
      (balancedSubsetAngularMask ηb r hηb hr s a u.2 : ℂ) •
        maskedCarrierKernel d (transportBandMask n j (balancedCarrierSubsetWeight ψ b s)) x u := by
  simp only [maskedCarrierKernel, balancedTransportBandMask, Complex.ofReal_mul, smul_smul,
    mul_comm]

/-- The original continuous carrier bumps give continuous shared weights
(`app:ch_waves:eq:background-quadrature`). -/
theorem continuous_balancedCarrierSubsetWeight (ψ : Point → ℝ) (b : I → Point → ℝ)
    (hc : Continuous ψ) (hbc : ∀ a, Continuous (b a)) (s : Finset I) :
    Continuous (balancedCarrierSubsetWeight ψ b s) := by
  unfold balancedCarrierSubsetWeight carrierSubsetWeight
  fun_prop

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
    (b : I → Point → ℝ) (hb : ∀ a z, b a z ∈ Set.Icc (0 : ℝ) 1)
    (hbc : ∀ a, Continuous (b a))
    (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ a, ηb a ≠ 0) (hr : ∀ a, 0 < r a)

/-- Compact bounds for the actual balanced band are derived from the
original band and the explicit square-root label-count factor. No normal
bound, forward identity or adjoint identity is an input
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def balancedTransportBandFiniteKernelBounds (j : Fin bands) (s : Finset I) (a : s) :
    FiniteCarrierKernelBounds d (balancedTransportBandMask n j.val ψ b ηb r hηb hr s a) := by
  let h := transportBandFiniteKernelBounds d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase j (balancedCarrierSubsetWeight ψ b s)
    (balancedCarrierSubsetWeight_patchBounds ψ b hψ hb s)
    (continuous_balancedCarrierSubsetWeight ψ b hc hbc s)
  have hmeas : Measurable (balancedSubsetAngularMask ηb r hηb hr s a) :=
    measurable_of_continuousOn_compl_singleton 0 (fun η hη ↦
      ((balancedSubsetAngularMask_spec ηb r hηb hr s a).1 η hη).continuousAt.continuousWithinAt)
  have hmask (η) : |balancedSubsetAngularMask ηb r hηb hr s a η| ≤ Real.sqrt s.card := by
    rw [balancedSubsetAngularMask, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (canonicalAngularSquareMask_abs_le _ _ _ _ a η)
      (Real.sqrt_nonneg _)).trans_eq (mul_one _)
  refine ⟨h.carrierSupport, h.isCompact_carrierSupport, h.frequencyRadius,
    h.frequencyRadius_nonneg, Real.sqrt s.card * h.bound,
    mul_nonneg (Real.sqrt_nonneg _) h.bound_nonneg, ?_, ?_, ?_⟩
  · simp_rw [maskedCarrierKernel_balancedTransportBandMask]
    exact ((Complex.continuous_ofReal.measurable.comp hmeas).comp
      measurable_snd.snd).stronglyMeasurable.smul h.stronglyMeasurable
  · intro x u
    rw [maskedCarrierKernel_balancedTransportBandMask, norm_smul,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hmask u.2) (h.norm_le x u) (norm_nonneg _) (Real.sqrt_nonneg _)
  · intro x z η hz
    rw [maskedCarrierKernel_balancedTransportBandMask, h.eq_zero x z η hz, smul_zero]

/-- The balanced continuum channel is constructed on the original carrier
Lebesgue space from its literal weighted kernel
(`app:ch_background:eq:bg-T`, `app:ch_waves:eq:sampling-prefix-normal`). -/
def balancedTransportBandContinuumOperator (j : Fin bands) (s : Finset I) (a : s) :
    CarrierL2 n →L[ℂ] ComplexOutputL2 n :=
  let h := balancedTransportBandFiniteKernelBounds d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase ψ hψ hc b hb hbc ηb r hηb hr j s a
  CarrierRegularization.boundedKernelOperator
    (K := maskedCarrierKernel d (balancedTransportBandMask n j.val ψ b ηb r hηb hr s a))
    h.stronglyMeasurable h.isCompact_initialSupport.measurableSet
    h.isCompact_initialSupport.measure_lt_top.ne h.kernel_eq_zero_off_initialSupport h.norm_le

/-- The constructed balanced channel has the SAME masked forward integral;
no raw measure, Fourier scalar or background is changed
(`app:ch_background:eq:bg-T`). -/
theorem balancedTransportBandContinuumOperator_ae (j : Fin bands) (s : Finset I) (a : s)
    (f : CarrierL2 n) :
    balancedTransportBandContinuumOperator d C Yext hY hA K hK hsupport M hM hbound
      hpoint hC hphase ψ hψ hc b hb hbc ηb r hηb hr j s a f =ᵐ[volume]
        regularizedCarrierIntegral d (balancedTransportBandMask n j.val ψ b ηb r hηb hr s a) f := by
  let h := balancedTransportBandFiniteKernelBounds d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase ψ hψ hc b hb hbc ηb r hηb hr j s a
  filter_upwards [CarrierRegularization.boundedKernelOperator_ae
    (K := maskedCarrierKernel d (balancedTransportBandMask n j.val ψ b ηb r hηb hr s a))
    h.stronglyMeasurable h.isCompact_initialSupport.measurableSet
    h.isCompact_initialSupport.measure_lt_top.ne h.kernel_eq_zero_off_initialSupport h.norm_le f]
      with x hx
  exact hx.trans (regularizedCarrierIntegral_eq_masked d _ f x).symm

local notation "T" => balancedTransportBandContinuumOperator d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase ψ hψ hc b hb hbc ηb r hηb hr
local notation "H" => balancedTransportBandFiniteKernelBounds d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase ψ hψ hc b hb hbc ηb r hηb hr
local notation "T₀" => transportBandContinuumOperator d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase

/-- The normals of the CONSTRUCTED balanced channels sum to the parent
transport band. All adjoint formulas and integral exchanges follow from
their derived finite kernel bounds. The covering input concerns the SAME
original nonzero detector and high-pass, not a normal identity
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_balancedTransportBandContinuumOperator_normal (j : Fin bands)
    (hcover : ∀ z η, ψ z ≠ 0 →
      d.angularCutoff (carrierSamplingEquiv.symm z) (‖η‖⁻¹ • η) ≠ 0 →
      d.highCutoff ‖η‖ ≠ 0 →
      ∃ a, b a z = 1 ∧ NormedSpace.normalize η ∈
        Metric.ball (NormedSpace.normalize (ηb a))
          (ContinuumRow.CanonicalConic.angularWidth (ηb a) (r a) / 4)) :
    (∑ c : (s : Finset I) × s, (T j c.1 c.2).comp (T j c.1 c.2).adjoint) =
      (T₀ j ψ hψ hc).comp (T₀ j ψ hψ hc).adjoint := by
  classical
  let mask := fun c : (s : Finset I) × s ↦
    balancedTransportBandMask n j.val ψ b ηb r hηb hr c.1 c.2
  ext1 w
  simp only [sum_apply]
  apply Lp.ext
  have heach := Filter.eventually_all.mpr (fun c : (s : Finset I) × s ↦
    carrier_normal_ae_eq_matrix_integral d (mask c) (H j c.1 c.2) (T j c.1 c.2)
      (balancedTransportBandContinuumOperator_ae d C Yext hY hA K hK hsupport M hM hbound
        hpoint hC hphase ψ hψ hc b hb hbc ηb r hηb hr j c.1 c.2) w)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun c : (s : Finset I) × s ↦ ((T j c.1 c.2).comp (T j c.1 c.2).adjoint) w), heach,
    carrier_normal_ae_eq_matrix_integral d (transportBandMask n j.val ψ)
      (transportBandFiniteKernelBounds d C Yext hY hA K hK hsupport M hM hbound
        hpoint hC hphase j ψ hψ hc) (T₀ j ψ hψ hc)
      (transportBandContinuumOperator_ae d C Yext hY hA K hK hsupport M hM hbound
        hpoint hC hphase j ψ hψ hc) w] with x hx ht hu
  rw [hx]
  apply PiLp.ext
  intro i
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [ht]
  rw [← integral_finsetSum Finset.univ
    (fun c _ ↦ integrable_carrierNormal_matrix_action (H j c.1 c.2) w x i), hu i]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul, ← integral_finsetSum Finset.univ
    (fun c _ ↦ TransportKernel.integrable_carrierNormalDensity (H j c.1 c.2) x y i k)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  change (∑ c : (s : Finset I) × s, carrierNormalDensity d
    (fun v ↦ transportBandMask n j.val (balancedCarrierSubsetWeight ψ b c.1) v *
      balancedSubsetAngularMask ηb r hηb hr c.1 c.2 v.2) x y i k u) = _
  simpa only [Fintype.sum_sigma] using
    sum_balanced_transportBand_normalDensity d j.val ηb r hηb hr ψ b hψ hb hcover x y i k u

variable (hcover : ∀ z η, ψ z ≠ 0 →
      d.angularCutoff (carrierSamplingEquiv.symm z) (‖η‖⁻¹ • η) ≠ 0 →
      d.highCutoff ‖η‖ ≠ 0 →
      ∃ a, b a z = 1 ∧ NormedSpace.normalize η ∈
        Metric.ball (NormedSpace.normalize (ηb a))
          (ContinuumRow.CanonicalConic.angularWidth (ηb a) (r a) / 4))

include hcover

/-- Balanced reassembly retains BOTH input quadratures and the exact
factor four in the normal of the factor-two real channel
(`app:ch_waves:eq:real-normal`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem sum_real_balancedTransportBandContinuumOperator_normal (j : Fin bands) :
    (∑ c : (s : Finset I) × s, (realQuadratureChannel (T j c.1 c.2)).comp
      (realQuadratureChannel (T j c.1 c.2)).adjoint) =
      (realQuadratureChannel (T₀ j ψ hψ hc)).comp
        (realQuadratureChannel (T₀ j ψ hψ hc)).adjoint := by
  have he : (∑ c : (s : Finset I) × s, (realQuadratureChannel (T j c.1 c.2)).comp
      (realQuadratureChannel (T j c.1 c.2)).adjoint) =
      (4 : ℝ) • realOutputCompression
        (∑ c : (s : Finset I) × s, (T j c.1 c.2).comp (T j c.1 c.2).adjoint) := by
    simp_rw [realQuadratureChannel_normal_eq_four_realPart]
    ext1 q
    simp [realOutputCompression, Finset.smul_sum]
  rw [he, sum_balancedTransportBandContinuumOperator_normal d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase ψ hψ hc b hb hbc ηb r hηb hr j hcover,
    realQuadratureChannel_normal_eq_four_realPart]

/-- The actual balanced detector copies and every original band in a
retained prefix give the SAME continuum carrier's rounded raw square.
The plateau is used only after reassembling the copied weights. The original
adjoint and the squared Fourier scalar remain explicit
(`app:ch_waves:eq:sampling-prefix-normal`, `main:eq:linear-two-errors`). -/
theorem balanced_transport_prefix_normal_eq_original
    (hψone : ∀ z η, d.angularCutoff z η ≠ 0 → ψ (carrierSamplingEquiv z) = 1)
    (hhigh : ∀ t, t ≤ 1 → d.highCutoff t = 0)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ q, U.adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral d q)
    (cutoff : ℝ) (hL : cutoffCount cutoff ≤ bands) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin bands ↦ j.val < cutoffCount cutoff),
      ∑ c : (s : Finset I) × s, (realQuadratureChannel (T j c.1 c.2)).comp
        (realQuadratureChannel (T j c.1 c.2)).adjoint) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2)) ^ 2 • (carrierChannel U).comp
        ((RawCutoffBounds.carrierSquaredCutoff (roundedCarrierMask n cutoff)).comp
          (carrierChannel U).adjoint) := by
  classical
  simp_rw [sum_real_balancedTransportBandContinuumOperator_normal d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase ψ hψ hc b hb hbc ηb r hηb hr hcover,
    real_transportBandContinuumOperator_eq_original d C Yext hY hA K hK hsupport M hM hbound
      hpoint hC hphase ψ hψ hc hψone U hU,
    map_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, ← pow_two]
  rw [← Finset.smul_sum, originalCarrier_band_normals_eq_rounded d hhigh U hU cutoff hL]

end JanetCartan.CanonicalRowComparison
