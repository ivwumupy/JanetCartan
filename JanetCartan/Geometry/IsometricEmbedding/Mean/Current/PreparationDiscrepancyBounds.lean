module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationIntegralBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.SmoothFamilyNorms.Measured
public import JanetCartan.Geometry.IsometricEmbedding.Mean.DensityDiscrepancy.Polarization

/-!
# Finite-jet bounds for the literal measured preparation integrand

The original measurement and Hermitian product act on the shared smooth
periodic families. Leibniz and polarization retain the current/transport
gain before the carrier integral of `app:ch_mean_pairs:eq:mean-density-lipschitz`.
No estimate for a discrepancy or preparation iterate is assumed.
-/

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean
open ContinuumRow SmoothPeriodicFamily

variable {n N : ℕ}

/-- The smooth measured polarization of a single original atom, retaining
its representative before the carrier integral. Both constituent maps are
the shared smooth-family maps (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def preparationMeasuredBilinear
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C) :
    SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) →ₗ[ℝ]
      SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) →ₗ[ℝ] SmoothResidual n :=
  (tensorBilinear (fun _ : Unit ↦ (1 : ℝ))).compr₂ (measurementFamily C hC)

/-- The smooth measured polarization has its literal pointwise value
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationMeasuredBilinear_apply
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (u v : SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ)) (x : Torus n) :
    (preparationMeasuredBilinear C hC u v).val x () =
      C x (hermitianBilinear (u.val x ()) (v.val x ())) := by
  simp [preparationMeasuredBilinear, tensorBilinear, measurementFamily,
    weightedHermitianBilinear]

/-- Two applications of the proved finite-jet Leibniz bound control the
actual measured tensor. Constants depend on the fixed coefficient jets,
never the coloring (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationMeasuredBilinear_cSeminorm_le
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (s : ℕ) (u v : SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ)) :
    componentCSeminorm s () (preparationMeasuredBilinear C hC u v) ≤
      ((2 : ℝ) ^ s * 2 ^ s * cNorm (fundamentalCell n) s (periodicLift C)) *
        componentCSeminorm s () u * componentCSeminorm s () v := by
  let ev := (ContinuousLinearMap.apply ℝ (Euclidean n) (E' := MetricTensor n)).flip
  have hev : ‖ev‖ ≤ 1 := ev.opNorm_le_bound₂ zero_le_one (fun A u ↦ by
    simpa only [ev, ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply, one_mul]
      using A.le_opNorm u)
  let H := hermitianContinuousBilinear (m := Fin N) (n := Fin n)
  have hh := (H.contDiff.comp (smooth u ()).2).clm_apply (smooth v ()).2
  have h₁ := cNorm_bilinear_le_of_opNorm_le ev (isCompact_fundamentalCell n)
    (hC.2.of_le (by simp : (s : ℕ∞ω) ≤ ∞)) (hh.of_le (by simp : (s : ℕ∞ω) ≤ ∞)) hev
  have h₂ := cNorm_bilinear_le_of_opNorm_le H (isCompact_fundamentalCell n)
    ((smooth u ()).2.of_le (by simp : (s : ℕ∞ω) ≤ ∞))
    ((smooth v ()).2.of_le (by simp : (s : ℕ∞ω) ≤ ∞)) norm_hermitianContinuousBilinear_le
  simp only [mul_one] at h₁ h₂
  have h := h₁.trans (mul_le_mul_of_nonneg_left h₂
    (mul_nonneg (by positivity) (cNorm_nonneg _ _ _)))
  change cNorm (fundamentalCell n) s
    (periodicLift (fun x ↦ (preparationMeasuredBilinear C hC u v).val x ())) ≤
    ((2 : ℝ) ^ s * 2 ^ s * cNorm (fundamentalCell n) s (periodicLift C)) *
      cNorm (fundamentalCell n) s (periodicLift (fun x ↦ u.val x ())) *
      cNorm (fundamentalCell n) s (periodicLift (fun x ↦ v.val x ()))
  simp only [preparationMeasuredBilinear_apply]
  convert h using 1
  · rfl
  · ring

section Atoms

variable {A κ : Type*} [AddCommGroup A] [Module ℝ A]
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (χ : CarrierParameter → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (U T : κ → CarrierParameter → A →ₗ[ℝ]
      SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))

/-- The actual carrier integrand formed from the original linear current and
transport maps on smooth initial data. The original external cutoff is squared
exactly once (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def preparationAtomIntegrand (a : A) (c : κ) (p : Torus n × CarrierParameter) : Euclidean n :=
  χ p.2 ^ 2 • C p.1 (hermitianTensor ((U c p.2 a).val p.1 ()) -
    hermitianTensor ((T c p.2 a).val p.1 ()))

/-- The shared polarization is exactly the literal integrand, before
integration or estimates (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationAtomIntegrand_eq (a : A) (c : κ) (p : Torus n × CarrierParameter) :
    preparationAtomIntegrand C χ U T a c p = χ p.2 ^ 2 •
      (DensityDiscrepancy.squareDiscrepancy (preparationMeasuredBilinear C hC)
        (U c p.2) (T c p.2) a).val p.1 () := by
  simp only [DensityDiscrepancy.squareDiscrepancy, Submodule.coe_sub, Pi.sub_apply,
    preparationMeasuredBilinear_apply, hermitianBilinear, LinearMap.mk₂_apply,
    mixedHermitianTensor_self, ← map_sub]
  rfl

variable
    (hUc : ∀ a c, Continuous (fun p : Torus n × CarrierParameter ↦ (U c p.2 a).val p.1 ()))
    (hTc : ∀ a c, Continuous (fun p : Torus n × CarrierParameter ↦ (T c p.2 a).val p.1 ()))
    (hU : ∀ a c, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      (U c p.2 a).val (torusQuotient p.1) ()))
    (hT : ∀ a c, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      (T c p.2 a).val (torusQuotient p.1) ()))

include hC hχ hUc hTc hU hT in
/-- Joint regularity comes from the original linear atom extensions, with
no regularity assumption on the discrepancy (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationAtomIntegrand_regular (a : A) (c : κ) :
    Continuous (preparationAtomIntegrand C χ U T a c) ∧
    ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      preparationAtomIntegrand C χ U T a c (torusQuotient p.1,p.2)) :=
  preparationHermitianIntegrand_regular C hC χ hχ _ _ (hUc a c) (hTc a c) (hU a c) (hT a c)

/-- The integrand has the original compact carrier support
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationAtomIntegrand_zero_off (a : A) (c : κ) (x : Torus n)
    (z : CarrierParameter) (hz : z ∉ tsupport χ) :
    preparationAtomIntegrand C χ U T a c (x,z) = 0 := by
  simp [preparationAtomIntegrand, image_eq_zero_of_notMem_tsupport hz]

variable [Fintype κ]
    (mask : κ → CarrierParameter → ℝ)
    (hm : ∀ c, Measurable (mask c)) (hm0 : ∀ c z, 0 ≤ mask c z)
    (hmask : ∀ z, ∑ c, mask c z = 1)

/-- The same measured colored integral, with the atom maps still linear in
the original initial amplitude (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def preparationAtomDiscrepancy (a : A) : Torus n → Euclidean n :=
  fun x ↦ ∫ z, ∑ c, mask c z • preparationAtomIntegrand C χ U T a c (x,z)
    ∂(volume.prod volume)

include hC hχ hχc hm hm0 hmask hUc hTc hU hT in
/-- The integral is smooth for every smooth-domain initial amplitude. This
is the SAME representative to which the Sobolev estimate applies
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem isSmoothPeriodic_preparationAtomDiscrepancy (a : A) :
    IsSmoothPeriodic (preparationAtomDiscrepancy C χ U T mask a) :=
  isSmoothPeriodic_preparationColoredIntegral mask hm hm0 hmask _
    (fun c ↦ (preparationAtomIntegrand_regular C hC χ hχ U T hUc hTc hU hT a c).1)
    (fun c ↦ (preparationAtomIntegrand_regular C hC χ hχ U T hUc hTc hU hT a c).2)
    hχc (preparationAtomIntegrand_zero_off C χ U T a)

include hC hχ hχc hm hm0 hmask hUc hTc hU hT

/-- Literal integrability, proved from joint regularity and the original
carrier support (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem integrable_preparationAtomIntegrand (a : A) (x : Torus n) :
    Integrable (fun z ↦ ∑ c, mask c z • preparationAtomIntegrand C χ U T a c (x,z))
      (volume.prod volume) := by
  apply integrable_finsetSum
  intro c _
  exact integrable_preparationMaskedSection (mask c) (hm c) (hm0 c)
    (fun z ↦ (Finset.single_le_sum (fun i _ ↦ hm0 i z) (Finset.mem_univ c)).trans_eq (hmask z))
    _ (preparationAtomIntegrand_regular C hC χ hχ U T hUc hTc hU hT a c).1
    hχc (preparationAtomIntegrand_zero_off C χ U T a c) x

/-- Linear current/transport bounds and their small difference imply the
Sobolev bound for the literal discrepancy. The measured square estimate and
the carrier integration are both proved here; neither is an input. Constants
are independent of the number and smallest weight of the colors
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem periodicSobolevNorm_preparationAtomDiscrepancy_le
    (s : ℕ) (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    {M L δ : ℝ} (_hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hχM : ∀ z, |χ z| ≤ M)
    (hUb : ∀ c z a, componentCSeminorm s () (U c z a) ≤ L * p a)
    (hTb : ∀ c z a, componentCSeminorm s () (T c z a) ≤ L * p a)
    (hDb : ∀ c z a, componentCSeminorm s () ((U c z - T c z) a) ≤ δ * L * p a)
    (a : A) :
    periodicSobolevNorm s (preparationAtomDiscrepancy C χ U T mask a) ≤
      sobolevPeriodicJetConstant n s * (s + 1 : ℕ) *
        ((M ^ 2 * (2 * ((2 : ℝ) ^ s * 2 ^ s * cNorm (fundamentalCell n) s (periodicLift C)) *
          L ^ 2 * δ * p a ^ 2)) * (volume.prod volume).real (tsupport χ)) := by
  let B := (2 : ℝ) ^ s * 2 ^ s * cNorm (fundamentalCell n) s (periodicLift C)
  have hB : 0 ≤ B := mul_nonneg (by positivity) (cNorm_nonneg _ _ _)
  have hb (c : κ) (z : CarrierParameter) :
      componentCSeminorm s () (DensityDiscrepancy.squareDiscrepancy
        (preparationMeasuredBilinear C hC) (U c z) (T c z) a) ≤
      2 * B * L ^ 2 * δ * p a ^ 2 :=
    DensityDiscrepancy.squareDiscrepancy_le (preparationMeasuredBilinear C hC)
      (U c z) (T c z) p (componentCSeminorm s ())
      (componentCSeminorm s ()) hB hL hδ hp (fun v ↦ apply_nonneg _ v)
      (preparationMeasuredBilinear_cSeminorm_le C hC s) (hUb c z) (hTb c z) (hDb c z) a
  apply periodicSobolevNorm_preparationColoredIntegral_le_cNorm mask hm hm0 hmask _
    (fun c ↦ (preparationAtomIntegrand_regular C hC χ hχ U T hUc hTc hU hT a c).1)
    (fun c ↦ (preparationAtomIntegrand_regular C hC χ hχ U T hUc hTc hU hT a c).2)
    hχc (preparationAtomIntegrand_zero_off C χ U T a) s (by positivity)
  intro c z _
  simp_rw [preparationAtomIntegrand_eq C hC]
  let e := DensityDiscrepancy.squareDiscrepancy (preparationMeasuredBilinear C hC) (U c z) (T c z) a
  change cNorm (fundamentalCell n) s ((χ z ^ 2) • periodicLift (fun x ↦ e.val x ())) ≤ _
  rw [cNorm_smul (χ z ^ 2) ((smooth e ()).2.of_le (by simp))]
  have hm : ‖χ z ^ 2‖ ≤ M ^ 2 := by
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hχM z) 2
  exact mul_le_mul hm (hb c z) (cNorm_nonneg _ _ _) (sq_nonneg M)

/-- The same integration argument preserves the small factor in the
Lipschitz difference. Polarization derives this from the original linear
atom estimates; no nonlinear Lipschitz bound is assumed
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem periodicSobolevNorm_preparationAtomDiscrepancy_sub_le
    (s : ℕ) (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    {M L δ : ℝ} (_hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hχM : ∀ z, |χ z| ≤ M)
    (hUb : ∀ c z a, componentCSeminorm s () (U c z a) ≤ L * p a)
    (hTb : ∀ c z a, componentCSeminorm s () (T c z a) ≤ L * p a)
    (hDb : ∀ c z a, componentCSeminorm s () ((U c z - T c z) a) ≤ δ * L * p a)
    (a b : A) :
    periodicSobolevNorm s
      (preparationAtomDiscrepancy C χ U T mask a - preparationAtomDiscrepancy C χ U T mask b) ≤
      sobolevPeriodicJetConstant n s * (s + 1 : ℕ) *
        ((M ^ 2 * (2 * ((2 : ℝ) ^ s * 2 ^ s * cNorm (fundamentalCell n) s (periodicLift C)) *
          L ^ 2 * δ * (p a + p b) * p (a - b))) * (volume.prod volume).real (tsupport χ)) := by
  let B := (2 : ℝ) ^ s * 2 ^ s * cNorm (fundamentalCell n) s (periodicLift C)
  have hB : 0 ≤ B := mul_nonneg (by positivity) (cNorm_nonneg _ _ _)
  let e (c : κ) (z : CarrierParameter) :=
    DensityDiscrepancy.squareDiscrepancy (preparationMeasuredBilinear C hC) (U c z) (T c z) a -
      DensityDiscrepancy.squareDiscrepancy (preparationMeasuredBilinear C hC) (U c z) (T c z) b
  have hb (c : κ) (z : CarrierParameter) : componentCSeminorm s () (e c z) ≤
      2 * B * L ^ 2 * δ * (p a + p b) * p (a - b) :=
    DensityDiscrepancy.squareDiscrepancy_sub_le (preparationMeasuredBilinear C hC)
      (U c z) (T c z) p (componentCSeminorm s ()) (componentCSeminorm s ()) hB hL hδ hp
      (fun v ↦ apply_nonneg _ v) (preparationMeasuredBilinear_cSeminorm_le C hC s)
      (hUb c z) (hTb c z) (hDb c z) a b
  let f (c : κ) (p : Torus n × CarrierParameter) :=
    preparationAtomIntegrand C χ U T a c p - preparationAtomIntegrand C χ U T b c p
  have heq : preparationAtomDiscrepancy C χ U T mask a - preparationAtomDiscrepancy C χ U T mask b =
      fun x ↦ ∫ z, ∑ c, mask c z • f c (x,z) ∂(volume.prod volume) := by
    funext x
    simp only [preparationAtomDiscrepancy, Pi.sub_apply]
    rw [← integral_sub
      (integrable_preparationAtomIntegrand C hC χ hχ hχc U T hUc hTc hU hT mask hm hm0 hmask a x)
      (integrable_preparationAtomIntegrand C hC χ hχ hχc U T hUc hTc hU hT mask hm hm0 hmask b x)]
    simp only [f, smul_sub, Finset.sum_sub_distrib]
  rw [heq]
  have hreg := preparationAtomIntegrand_regular C hC χ hχ U T hUc hTc hU hT
  have hpab := hp (a-b)
  have hpa := hp a
  have hpb := hp b
  apply periodicSobolevNorm_preparationColoredIntegral_le_cNorm mask hm hm0 hmask f
    (fun c ↦ (hreg a c).1.sub (hreg b c).1)
    (fun c ↦ (hreg a c).2.sub (hreg b c).2) hχc
    (fun c x z hz ↦ by simp only [f, preparationAtomIntegrand_zero_off C χ U T _ c x z hz, sub_self])
    s (by positivity)
  intro c z _
  have hf : (fun y ↦ f c (torusQuotient y,z)) =
      (χ z ^ 2) • periodicLift (fun x ↦ (e c z).val x ()) := by
    funext y
    simp only [f, preparationAtomIntegrand_eq C hC, e, Submodule.coe_sub, Pi.sub_apply,
      Pi.smul_apply, periodicLift, Function.comp_apply, smul_sub]
  rw [hf, cNorm_smul (χ z ^ 2) ((smooth (e c z) ()).2.of_le (by simp))]
  have hm : ‖χ z ^ 2‖ ≤ M ^ 2 := by
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hχM z) 2
  exact mul_le_mul hm (hb c z) (cNorm_nonneg _ _ _) (sq_nonneg M)

end Atoms

section Identification
variable {A κ : Type*} [AddCommGroup A] [Module ℝ A] [Fintype κ]

/-- The estimated integral is exactly the discrepancy of the existing
preparation run when the same initial amplitude and transported scalar are
used. Agreement is required only on the original measurement/carrier support;
no global physical strain identity is invoked
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationAtomDiscrepancy_eq_colored
    (d : CarrierData n N) (χ : CarrierParameter → ℝ) (mask : κ → CarrierParameter → ℝ)
    (current : κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r v : CarrierVariable n → ℝ)
    (U T : κ → CarrierParameter → A →ₗ[ℝ]
      SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ)) (a : A)
    (hcurrent : ∀ c x, x ∈ d.outputChart → ∀ z, χ z ≠ 0 →
      (U c z a).val x () = current c z (fun p ↦ positiveDensityAmplitude (r p) (v p)) x)
    (htransport : ∀ c x, x ∈ d.outputChart → ∀ z, χ z ≠ 0 →
      (T c z a).val x () = densityTransportMatrix d v x z) :
    preparationAtomDiscrepancy (preparationMeasurement d) χ U T mask a =
      coloredPreparationDiscrepancy d χ mask current r v := by
  funext x
  rw [coloredPreparationDiscrepancy_eq_measuredIntegral]
  apply integral_congr_ae
  filter_upwards [] with z
  apply Finset.sum_congr rfl
  intro c _
  by_cases hx : x ∈ d.outputChart
  · by_cases hz : χ z = 0
    · simp [preparationAtomIntegrand, hz]
    · simp only [preparationAtomIntegrand, hcurrent c x hx z hz, htransport c x hx z hz]
  · simp [preparationAtomIntegrand, preparationMeasurement, hx]

end Identification

end JanetCartan.CurrentMean
