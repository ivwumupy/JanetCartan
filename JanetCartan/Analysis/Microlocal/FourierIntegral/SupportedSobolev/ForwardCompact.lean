module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.GraphDifferentiation.CompactIntegral
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.GraphDifferentiation.Integrand

/-!
# Supported compact-frequency forward kernels

Analytic prerequisites of the weak pairing in
`app:ch_regular_base:eq:graph-derivative-transfer`. Integrability and smoothness
of the actual integrals follow from primitive smoothness and compact carriers.
The phase is differentiated only on the buffered supported chart, including
all frequency and physical cutoff shoulders.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev.ForwardRegularized
open FourierIntegral.ForwardRegularized FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ}

variable {U : Set (Point n)} {X Y F : Set (Euclidean n)} {S : (Euclidean n) → (Euclidean n) → ℝ} {A : FullAmplitude n r}
  {u : (Euclidean n) → Fin r → ℂ}

/-- Joint smoothness of the literal kernel on all variables. The support gap
removes the phase singularity at zero without altering its values on the
amplitude support (`app:ch_regular_base:eq:graph-derivative-transfer`). -/
theorem smooth_integrand (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F)
    (hF0 : (0 : (Euclidean n)) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (integrand S A u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hc : ((p.1, p.2.2), p.2.1) ∈ (X ×ˢ Y) ×ˢ F
  · have hη : p.2.1 ≠ 0 := fun hz ↦ hF0 (hz ▸ hc.2)
    have hp : ContDiffAt ℝ ∞ (fun q : (Euclidean n) × ((Euclidean n) × (Euclidean n)) ↦
        graphOscillation S q.1 q.2.2 q.2.1) p :=
      (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        (((hS _ (hcarrier hc) hη).comp p (contDiffAt_fst.prodMk contDiffAt_snd.fst)).sub
          (contDiffAt_snd.snd.inner ℝ contDiffAt_snd.fst)))).cexp
    let M : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) :=
      (Matrix.mulVecBilin ℝ ℝ).toContinuousBilinearMap
    exact hp.smul ((M.contDiff.contDiffAt.comp p (hA.smooth.contDiffAt.comp p
      (contDiffAt_fst.prodMk (contDiffAt_snd.snd.prodMk contDiffAt_snd.fst)))).clm_apply
        (hu.contDiffAt.comp p contDiffAt_snd.snd))
  · have hz : integrand S A u =ᶠ[𝓝 p] fun _ ↦ 0 := by
      have ho := ((hX.prod hY).prod hF).isOpen_compl.preimage
        ((continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst)
      filter_upwards [ho.mem_nhds hc] with q hq
      have ha : A q.1 q.2.2 q.2.1 = 0 := by
        apply hA.support
        change ¬ ((q.1 ∈ X ∧ q.2.2 ∈ Y) ∧ q.2.1 ∈ F) at hq
        tauto
      simp [integrand, ha]
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- Absolute frequency/source integrability from compact support; this is the
Fubini input for the actual forward kernel, not an assumed domination bound.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem integrable_integrand (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F)
    (hF0 : (0 : (Euclidean n)) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ x y η, η ∉ K → A x y η = 0) (x : (Euclidean n)) :
    Integrable (fun p ↦ integrand S A u (x, p)) (volume.prod volume) := by
  exact GraphDifferentiation.integrable_section (U := univ) (hK.prod hus)
    (smooth_integrand hA hX hY hF hF0 hcarrier hS hu).continuous.continuousOn
    (fun z _ p hp ↦ integrand_eq_zero_off_carrier hAK z p hp) (mem_univ x)

/-- The literal iterated graph integral equals the integral on the product
carrier, preserving the physical normalization.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphOperator_eq_product_integral (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F)
    (hF0 : (0 : (Euclidean n)) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ x y η, η ∉ K → A x y η = 0) (x : (Euclidean n)) :
    graphOperator S A u x = ((2 * Real.pi) ^ n : ℂ)⁻¹ •
      ∫ p, integrand S A u (x, p) ∂(volume.prod volume) := by
  exact congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·)
    (integral_prod _ (integrable_integrand hA hX hY hF hF0 hcarrier hS hu hus hK hAK x)).symm

/-- The actual regularized output is smooth, as required for output integration
by parts in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem smooth_graphOperator (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F)
    (hF0 : (0 : (Euclidean n)) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ x y η, η ∉ K → A x y η = 0) :
    ContDiff ℝ ∞ (graphOperator S A u) := by
  let μ : Measure ((Euclidean n) × (Euclidean n)) := volume.prod volume
  have hc : IsCompact (K ×ˢ tsupport u) := hK.prod hus
  let : IsFiniteMeasure (μ.restrict (K ×ˢ tsupport u)) :=
    isFiniteMeasure_restrict.mpr hc.measure_lt_top.ne
  have hs := contDiffOn_compactParameterIntegral (μ := μ) (U := (univ : Set (Euclidean n)))
    isOpen_univ isOpen_univ hc (subset_univ _)
    (smooth_integrand hA hX hY hF hF0 hcarrier hS hu).contDiffOn
  have he : graphOperator S A u = fun x ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ •
      ∫ p in K ×ˢ tsupport u, integrand S A u (x, p) ∂μ := by
    funext x
    rw [graphOperator_eq_product_integral hA hX hY hF hF0 hcarrier hS hu hus hK hAK x]
    exact congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·)
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun p hp ↦ integrand_eq_zero_off_carrier hAK x p hp)).symm
  rw [he]
  exact (contDiffOn_univ.mp hs).const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)

/-- Output differentiation passes through the literal normalized product
integral. Compactness supplies the derivative domination and integrability.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem partialDeriv_graphOperator_integral (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F)
    (hF0 : (0 : Euclidean n) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hAK : ∀ x y η, η ∉ K → A x y η = 0) (x : Euclidean n) (i : Fin n) :
    partialDeriv (graphOperator S A u) x i = ((2 * Real.pi) ^ n : ℂ)⁻¹ •
      ∫ η, ∫ y, partialDeriv (fun z ↦ integrand S A u (z, (η, y))) x i := by
  let μ : Measure (Euclidean n × Euclidean n) := volume.prod volume
  have hf := smooth_integrand hA hX hY hF hF0 hcarrier hS hu
  have hs : ∀ z ∈ (univ : Set (Euclidean n)), ∀ p ∉ K ×ˢ tsupport u,
      integrand S A u (z, p) = 0 :=
    fun z _ p hp ↦ integrand_eq_zero_off_carrier hAK z p hp
  have hd := GraphDifferentiation.hasFDerivAt_integral (μ := μ)
    isOpen_univ (hK.prod hus) hf.contDiffOn hs (mem_univ x)
  have hdi := GraphDifferentiation.integrable_section (μ := μ) (hK.prod hus)
    (contDiffOn_parameterFDeriv isOpen_univ isOpen_univ hf.contDiffOn).continuousOn
    (fun z hz p hp ↦ GraphDifferentiation.fderiv_section_eq_zero isOpen_univ hs hz hp)
    (mem_univ x)
  have he : graphOperator S A u = fun z ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ •
      ∫ p, integrand S A u (z, p) ∂μ :=
    funext (graphOperator_eq_product_integral hA hX hY hF hF0 hcarrier hS hu hus hK hAK)
  rw [he]
  have hscaled := hd.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)
  change (fderiv ℝ _ x) (EuclideanSpace.single i 1) = _
  have heval := congrArg (fun L : Euclidean n →L[ℝ] (Fin r → ℂ) ↦
    L (EuclideanSpace.single i 1)) hscaled.fderiv
  refine heval.trans ?_
  change ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    (∫ p, fderiv ℝ (fun z ↦ integrand S A u (z, p)) x ∂μ) (EuclideanSpace.single i 1) = _
  rw [ContinuousLinearMap.integral_apply hdi]
  exact congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·)
    (integral_prod _ ((ContinuousLinearMap.apply ℝ (Fin r → ℂ)
      (EuclideanSpace.single i 1)).integrable_comp hdi))

end JanetCartan.FourierIntegral.SupportedSobolev.ForwardRegularized
