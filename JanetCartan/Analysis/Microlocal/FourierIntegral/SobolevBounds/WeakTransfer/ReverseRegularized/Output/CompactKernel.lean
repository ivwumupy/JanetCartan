module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized.Cutoff
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.GraphDifferentiation.CompactIntegral
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Compact reverse kernels and output differentiation

The analytic inputs to output integration by parts in
`app:ch_regular_base:eq:graph-derivative-transfer`. The frequency/source
carrier supplies Fubini and differentiation under the integral. The original
physical support supplies compact output support.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.ReverseRegularized.Output
variable {n r : ℕ}
local notation "E" => Euclidean n
variable {K : Set (Euclidean n × Euclidean n)} {C : FullAmplitude n r}
  {S : Euclidean n → Euclidean n → ℝ} {χ : Euclidean n → ℂ} {u : Euclidean n → Fin r → ℂ}

/-- The reverse integrand arranged as `(y,(η,x))` for the output parameter
integral; the amplitude itself retains `(x,y,η)` order.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def integrand (S : E → E → ℝ) (C : FullAmplitude n r) (u : E → Fin r → ℂ)
    (p : E × (E × E)) : Fin r → ℂ :=
  star (graphOscillation S p.2.2 p.1 p.2.1) • (C p.2.2 p.1 p.2.1).mulVec (u p.2.2)

/-- Joint smoothness of the cutoff integrand, used in the compact parameter
integral. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem smooth_integrand (hC : ReverseAmplitudeAdmissible K C)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : (0 : E) ∉ tsupport χ)
    (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (integrand S (frequencyCutFullAmplitude χ C) u) := by
  let M : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) :=
    (Matrix.mulVecBilin ℝ ℝ).toContinuousBilinearMap
  have hc := (hC.contDiff_reverseOscillatory_frequencyCut S hS χ hχ hχ0).comp
    ((contDiff_snd.snd.prodMk contDiff_fst).prodMk contDiff_snd.fst)
  have hm : ContDiff ℝ ∞ (fun p : E × (E × E) ↦
      (star (graphOscillation S p.2.2 p.1 p.2.1) •
        frequencyCutFullAmplitude χ C p.2.2 p.1 p.2.1).mulVec (u p.2.2)) :=
    (M.contDiff.comp hc).clm_apply (hu.comp contDiff_snd.snd)
  change ContDiff ℝ ∞ (fun p : E × (E × E) ↦
    star (graphOscillation S p.2.2 p.1 p.2.1) •
      (frequencyCutFullAmplitude χ C p.2.2 p.1 p.2.1).mulVec (u p.2.2))
  simpa only [Matrix.smul_mulVec] using hm

private theorem integrand_eq_zero_off_carrier (y : E) (p : E × E)
    (hp : p ∉ tsupport χ ×ˢ tsupport u) :
    integrand S (frequencyCutFullAmplitude χ C) u (y, p) = 0 := by
  by_cases hη : p.1 ∈ tsupport χ
  · have hx : p.2 ∉ tsupport u := fun hx ↦ hp ⟨hη, hx⟩
    simp [integrand, image_eq_zero_of_notMem_tsupport hx]
  · simp [integrand, frequencyCutFullAmplitude, image_eq_zero_of_notMem_tsupport hη]

/-- Absolute frequency/source integrability, the Fubini input for the literal
reverse operator. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem integrable_integrand (hC : ReverseAmplitudeAdmissible K C)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : (0 : E) ∉ tsupport χ)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) (y : E) :
    Integrable (fun p ↦ integrand S (frequencyCutFullAmplitude χ C) u (y, p))
      (volume.prod volume) := by
  exact GraphDifferentiation.integrable_section (U := univ) (hχs.prod hus)
    (smooth_integrand hC hS hχ hχ0 hu).continuous.continuousOn
    (fun z _ p hp ↦ integrand_eq_zero_off_carrier z p hp) (mem_univ y)

private theorem reverseGraphOperator_eq_product_integral
    (hC : ReverseAmplitudeAdmissible K C)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : (0 : E) ∉ tsupport χ)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) (y : E) :
    reverseGraphOperator S (frequencyCutFullAmplitude χ C) u y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ •
        ∫ p, integrand S (frequencyCutFullAmplitude χ C) u (y, p)
          ∂(volume.prod volume) := by
  exact congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·)
    (integral_prod _ (integrable_integrand hC hS hχ hχs hχ0 hu hus y)).symm

/-- Smoothness of the actual reverse output, from compact frequency/source
integration. Consumed by output integration by parts.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem smooth_reverseGraphOperator (hC : ReverseAmplitudeAdmissible K C)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : (0 : E) ∉ tsupport χ)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    ContDiff ℝ ∞ (reverseGraphOperator S (frequencyCutFullAmplitude χ C) u) := by
  let μ : Measure (E × E) := volume.prod volume
  have hc : IsCompact (tsupport χ ×ˢ tsupport u) := hχs.prod hus
  let : IsFiniteMeasure (μ.restrict (tsupport χ ×ˢ tsupport u)) :=
    isFiniteMeasure_restrict.mpr hc.measure_lt_top.ne
  have hs := contDiffOn_compactParameterIntegral (μ := μ) (U := (univ : Set E))
    isOpen_univ isOpen_univ hc (subset_univ _)
    (smooth_integrand hC hS hχ hχ0 hu).contDiffOn
  have he : reverseGraphOperator S (frequencyCutFullAmplitude χ C) u =
      fun y ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ •
        ∫ p in tsupport χ ×ˢ tsupport u,
          integrand S (frequencyCutFullAmplitude χ C) u (y, p) ∂μ := by
    funext y
    rw [reverseGraphOperator_eq_product_integral hC hS hχ hχs hχ0 hu hus y]
    exact congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·)
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun p hp ↦ integrand_eq_zero_off_carrier y p hp)).symm
  rw [he]
  exact (contDiffOn_univ.mp hs).const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)

/-- The original output mask confines the reverse output to the second
projection of the physical support. Consumed by pairing integrability.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem compactSupport_reverseGraphOperator (hC : ReverseAmplitudeAdmissible K C)
    (hK : IsCompact K) :
    HasCompactSupport (reverseGraphOperator S (frequencyCutFullAmplitude χ C) u) := by
  have hc := hK.image continuous_snd
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hc.isClosed
  intro y hy
  by_contra hn
  have hz (x η : E) : C x y η = 0 := by
    by_contra hne
    have hp : ((x, y), η) ∈ tsupport (fun p : (E × E) × E ↦ C p.1.1 p.1.2 p.2) :=
      subset_tsupport _ hne
    exact hn ⟨(x, y), hC.support hp, rfl⟩
  exact hy (by simp [reverseGraphOperator, frequencyCutFullAmplitude, hz])

private theorem partialDeriv_reverseGraphOperator_integral
    (hC : ReverseAmplitudeAdmissible K C)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : (0 : E) ∉ tsupport χ)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) (y : E) (i : Fin n) :
    partialDeriv (reverseGraphOperator S (frequencyCutFullAmplitude χ C) u) y i =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
        partialDeriv (fun z ↦ integrand S (frequencyCutFullAmplitude χ C) u (z, (η, x))) y i := by
  let μ : Measure (E × E) := volume.prod volume
  have hf := smooth_integrand hC hS hχ hχ0 hu
  have hs : ∀ z ∈ (univ : Set E), ∀ p ∉ tsupport χ ×ˢ tsupport u,
      integrand S (frequencyCutFullAmplitude χ C) u (z, p) = 0 :=
    fun z _ p hp ↦ integrand_eq_zero_off_carrier z p hp
  have hd := GraphDifferentiation.hasFDerivAt_integral (μ := μ)
    isOpen_univ (hχs.prod hus) hf.contDiffOn hs (mem_univ y)
  have hdi := GraphDifferentiation.integrable_section (μ := μ) (hχs.prod hus)
    (contDiffOn_parameterFDeriv isOpen_univ isOpen_univ hf.contDiffOn).continuousOn
    (fun z hz p hp ↦ GraphDifferentiation.fderiv_section_eq_zero isOpen_univ hs hz hp)
    (mem_univ y)
  have he : reverseGraphOperator S (frequencyCutFullAmplitude χ C) u =
      fun z ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ •
        ∫ p, integrand S (frequencyCutFullAmplitude χ C) u (z, p) ∂μ :=
    funext (reverseGraphOperator_eq_product_integral hC hS hχ hχs hχ0 hu hus)
  rw [he]
  have hscaled := hd.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)
  change (fderiv ℝ _ y) (EuclideanSpace.single i 1) = _
  have heval := congrArg (fun L : E →L[ℝ] (Fin r → ℂ) ↦
    L (EuclideanSpace.single i 1)) hscaled.fderiv
  refine heval.trans ?_
  change ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    (∫ p, fderiv ℝ (fun z ↦ integrand S (frequencyCutFullAmplitude χ C) u (z, p)) y ∂μ)
      (EuclideanSpace.single i 1) = _
  rw [ContinuousLinearMap.integral_apply hdi]
  exact congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·)
    (integral_prod _ ((ContinuousLinearMap.apply ℝ (Fin r → ℂ)
      (EuclideanSpace.single i 1)).integrable_comp hdi))

/-- Output differentiation of the literal reverse integral gives exactly the
first output amplitude. All derivative domination follows from the compact
carrier. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem partialDeriv_reverseGraphOperator (hC : ReverseAmplitudeAdmissible K C)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχ0 : (0 : E) ∉ tsupport χ)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) (y : E) (i : Fin n) :
    partialDeriv (reverseGraphOperator S (frequencyCutFullAmplitude χ C) u) y i =
      reverseGraphOperator S (frequencyCutFullAmplitude χ (reverseFirstOutputAmplitude C i)) u y := by
  rw [partialDeriv_reverseGraphOperator_integral hC hS hχ hχs hχ0 hu hus y i]
  apply congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·)
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with x
  have ha : ContDiff ℝ ∞ (fun z ↦ frequencyCutFullAmplitude χ C x z η) :=
    (hC.contDiff_frequencyCut χ hχ hχ0).comp
    ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have he : ContDiff ℝ ∞ (fun z ↦ star (graphOscillation S x z η) •
      frequencyCutFullAmplitude χ C x z η) :=
    (hC.contDiff_reverseOscillatory_frequencyCut S hS χ hχ hχ0).comp
    ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  change partialDeriv (fun z ↦ star (graphOscillation S x z η) •
    (frequencyCutFullAmplitude χ C x z η).mulVec (u x)) y i = _
  simp_rw [← Matrix.smul_mulVec]
  rw [ResponseTransfer.partialDeriv_matrix_mulVec _ (fun _ ↦ u x) y i
    (he.differentiable (by simp) y) (differentiableAt_const _)]
  rw [partialDeriv_reverseGraphOscillation_smul_amplitude S _ x y η i
    (ha.differentiable (by simp) y), reverseFirstOutputAmplitude_frequencyCutFullAmplitude]
  simp [partialDeriv]

end JanetCartan.FourierIntegral.ReverseRegularized.Output
