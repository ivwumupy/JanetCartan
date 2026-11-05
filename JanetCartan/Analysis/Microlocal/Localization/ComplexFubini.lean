module

public import JanetCartan.Analysis.Microlocal.Localization.Source
public import Mathlib.MeasureTheory.VectorMeasure.Prod
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
/-!
# Complex-measure Fubini for the oscillatory source

This supplies the source/Fourier identification in `app:ch_osc:prop:osc-source-shell`.
The spatial measure is only required to give finite mass to the common compact support;
no global finiteness or Haar hypothesis is needed. Product integrability follows from
that support and the uniform amplitude bound. Restricting the spatial measure to the
support permits application of vector-measure Fubini to its associated signed measure.

Joint measurability of the real phase and joint strong measurability of the amplitude
are explicit. The `_of_measurable` identification and the measurable-source/kernel
corollaries use ordinary joint measurability for amplitudes in a second-countable
complex Banach space, in particular any finite-dimensional complex Hilbert space.
The frequency variable is the physical covector: the phase is exactly `ρ * φ u x - ξ x`.
The averaged kernel is continuous, so multiplication by a continuous mask is measurable.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace JanetCartan.Localization

variable {D X F : Type*} [MeasurableSpace D] [MeasurableSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- `app:ch_osc:prop:osc-source-shell`: Complex scalar multiplication commutes with the parameter
integral of an integrable field. -/
theorem complexMeasureIntegral_smul (ν : ComplexMeasure D) {f : D → F}
    (hf : Integrable f ν.variation) (c : ℂ) :
    complexMeasureIntegral ν (fun u ↦ c • f u) = c • complexMeasureIntegral ν f := by
  let S : F →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℂ) c
  let B : F →L[ℝ] ℂ →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℂ).flip
  change ν.integral (fun u ↦ S (f u)) B = S (ν.integral f B)
  rw [VectorMeasure.integral_continuousLinearMap_comp hf,
    VectorMeasure.continuousLinearMap_apply_integral hf]
  congr 1
  ext v z
  exact smul_comm z c v

/-- `app:ch_osc:prop:osc-source-shell`: Fubini for a finite positive spatial measure and a finite
complex parameter measure, derived from vector-measure Fubini and compatibility of real and
complex scalar multiplication. -/
theorem integral_complexMeasureIntegral_swap_finite (μ : Measure X) [IsFiniteMeasure μ]
    (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation] {f : X → D → F}
    (hf : Integrable (Function.uncurry f) (μ.prod ν.variation)) :
    (∫ x, complexMeasureIntegral ν (f x) ∂μ) =
      complexMeasureIntegral ν (fun u ↦ ∫ x, f x u ∂μ) := by
  let B : F →L[ℝ] ℂ →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℂ).flip
  let C : F →L[ℝ] ℝ →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have : IsFiniteMeasure μ.toSignedMeasure.variation := by
    simpa only [Measure.variation_toSignedMeasure] using (inferInstance : IsFiniteMeasure μ)
  have h := VectorMeasure.integral_integral_swap
    (μ := μ.toSignedMeasure) (ν := ν) (B := B) (C := C) (A := C) (D := B)
    (by simpa using hf) (fun v z r ↦ smul_comm r z v)
  simpa [complexMeasureIntegral, B, C] using h

/-- `app:ch_osc:prop:osc-source-shell`: Complex-measure Fubini for a uniformly bounded jointly
strongly measurable field with common finite-measure spatial support. Product integrability on
the restricted measure is derived, not assumed. -/
theorem integral_complexMeasureIntegral_swap_of_support (μ : Measure X)
    (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation] {f : X → D → F}
    {K : Set X} (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤)
    (hm : StronglyMeasurable (Function.uncurry f)) {B : ℝ}
    (hb : ∀ x u, ‖f x u‖ ≤ B) (hs : ∀ x ∉ K, ∀ u, f x u = 0) :
    (∫ x, complexMeasureIntegral ν (f x) ∂μ) =
      complexMeasureIntegral ν (fun u ↦ ∫ x, f x u ∂μ) := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hKfin.lt_top⟩
  have hi : Integrable (Function.uncurry f) ((μ.restrict K).prod ν.variation) :=
    Integrable.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall fun p ↦ hb p.1 p.2)
  have he (u : D) : (∫ x in K, f x u ∂μ) = ∫ x, f x u ∂μ := by
    rw [← integral_indicator hK]
    congr 1
    ext x
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, hs x hx u]
  have he' : (∫ x in K, complexMeasureIntegral ν (f x) ∂μ) =
      ∫ x, complexMeasureIntegral ν (f x) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [complexMeasureIntegral, funext (hs x hx), VectorMeasure.integral_zero]
  rw [← he', integral_complexMeasureIntegral_swap_finite (μ.restrict K) ν hi]
  simp_rw [he]

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [BorelSpace E] in
/-- `app:ch_osc:prop:osc-source-shell`: Joint measurability of the phase gives joint strong
measurability of its unit-modulus oscillation. -/
theorem stronglyMeasurable_phaseOscillation_joint {φ : D → E → ℝ}
    (hφ : Measurable (Function.uncurry φ)) (ρ : ℝ) :
    StronglyMeasurable (fun p : D × E ↦ phaseOscillation (fun y ↦ ρ * φ p.1 y) p.2) := by
  exact (Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp (measurable_const.mul hφ)).mul measurable_const)).stronglyMeasurable

omit [CompleteSpace F] [NormedAddCommGroup E] [BorelSpace E] in
/-- `app:ch_osc:prop:osc-source-shell`: The parameter-averaged source is strongly measurable from
joint phase and amplitude measurability. -/
theorem stronglyMeasurable_oscillatorySource (ν : ComplexMeasure D)
    [IsFiniteMeasure ν.variation] {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ))
    (ha : StronglyMeasurable (Function.uncurry a)) (ρ : ℝ) :
    StronglyMeasurable (oscillatorySource ν φ a ρ) :=
  ((stronglyMeasurable_phaseOscillation_joint hφ ρ).smul ha).integral_vectorMeasure_prod_left'

omit [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: The actual source is integrable from joint measurability,
the amplitude bound, and finite common compact support. -/
theorem integrable_oscillatorySource_joint (μ : Measure E) (ν : ComplexMeasure D)
    [IsFiniteMeasure ν.variation] {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ))
    (ham : StronglyMeasurable (Function.uncurry a)) (ρ : ℝ)
    {K : Set E} (hK : IsCompact K) (hKfin : μ K ≠ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ u x, ‖a u x‖ ≤ B) (hs : ∀ u, tsupport (a u) ⊆ K) :
    Integrable (oscillatorySource ν φ a ρ) μ :=
  integrable_oscillatorySource ν φ a ρ hK hKfin hB ha hs
    (stronglyMeasurable_oscillatorySource ν hφ ham ρ).aestronglyMeasurable

variable [NormedSpace ℝ E]

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: The full physical-frequency integrand is jointly strongly
measurable in parameter and position. -/
theorem stronglyMeasurable_fourierPhase_joint {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ))
    (ha : StronglyMeasurable (Function.uncurry a)) (ρ : ℝ) (ξ : E →L[ℝ] ℝ) :
    StronglyMeasurable (fun p : D × E ↦ phaseOscillation (fourierPhase (φ p.1) ρ ξ) p.2 • a p.1 p.2) := by
  have hp : Measurable (fun p : D × E ↦ ρ * φ p.1 p.2 - ξ p.2) :=
    (measurable_const.mul hφ).sub (ξ.continuous.measurable.comp measurable_snd)
  exact ((Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp hp).mul measurable_const)).stronglyMeasurable).smul ha

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: The uniform amplitude bound and common compact support imply
integrability on the product of the spatial measure and the total variation of the parameter
measure. -/
theorem integrable_fourierPhase_prod (μ : Measure E) (ν : ComplexMeasure D)
    [IsFiniteMeasure ν.variation] {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ))
    (ham : StronglyMeasurable (Function.uncurry a)) (ρ : ℝ) (ξ : E →L[ℝ] ℝ)
    {K : Set E} (hK : IsCompact K) (hKfin : μ K ≠ ⊤) {B : ℝ}
    (ha : ∀ u x, ‖a u x‖ ≤ B) (hs : ∀ u, tsupport (a u) ⊆ K) :
    Integrable (fun p : E × D ↦ phaseOscillation (fourierPhase (φ p.2) ρ ξ) p.1 • a p.2 p.1)
      (μ.prod ν.variation) := by
  apply integrable_of_bounded_support (hK.measurableSet.prod MeasurableSet.univ)
    (K := K ×ˢ Set.univ) (B := B)
  · rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hKfin (measure_ne_top _ _)
  · exact ((stronglyMeasurable_fourierPhase_joint hφ ham ρ ξ).comp_measurable
      measurable_swap).aestronglyMeasurable
  · intro p hp
    refine ⟨?_, Set.mem_univ _⟩
    by_contra hx
    have hz : a p.2 p.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs p.2 h))
    exact hp (by simp [hz])
  · intro p
    simpa only [norm_smul, norm_phaseOscillation, one_mul] using ha p.2 p.1

omit [MeasurableSpace E] [BorelSpace E] in
/-- `app:ch_osc:prop:osc-source-shell`: Factorization of the exact physical Fourier phase, with no
rescaling or change of sign. -/
theorem phaseOscillation_fourierPhase (φ : E → ℝ) (ρ : ℝ) (ξ : E →L[ℝ] ℝ) (x : E) :
    phaseOscillation (fourierPhase φ ρ ξ) x =
      phaseOscillation (fun y ↦ -ξ y) x * phaseOscillation (fun y ↦ ρ * φ y) x := by
  simp only [phaseOscillation, fourierPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `app:ch_osc:prop:osc-source-shell`: The physical Fourier integral of the actual source equals
the averaged Fourier kernel. Both section integrability and the product integrability needed by
Fubini are derived from the stated bounds and support. -/
theorem physicalFourierIntegral_oscillatorySource (μ : Measure E) (ν : ComplexMeasure D)
    [IsFiniteMeasure ν.variation] {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ))
    (ham : StronglyMeasurable (Function.uncurry a)) (ρ : ℝ) (ξ : E →L[ℝ] ℝ)
    {K : Set E} (hK : IsCompact K) (hKfin : μ K ≠ ⊤) {B : ℝ}
    (ha : ∀ u x, ‖a u x‖ ≤ B) (hs : ∀ u, tsupport (a u) ⊆ K) :
    physicalFourierIntegral μ (oscillatorySource ν φ a ρ) ξ =
      averagedFourierKernel μ ν φ a ρ ξ := by
  have hi (x : E) : Integrable
      (fun u ↦ phaseOscillation (fun y ↦ ρ * φ u y) x • a u x) ν.variation := by
    apply Integrable.of_bound (((stronglyMeasurable_phaseOscillation_joint hφ ρ).smul ham).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
    exact Filter.Eventually.of_forall fun u ↦ by
      change ‖phaseOscillation (fun y ↦ ρ * φ u y) x • a u x‖ ≤ B
      simpa only [norm_smul, norm_phaseOscillation, one_mul] using ha u x
  have he (x : E) : phaseOscillation (fun y ↦ -ξ y) x • oscillatorySource ν φ a ρ x =
      complexMeasureIntegral ν
        (fun u ↦ phaseOscillation (fourierPhase (φ u) ρ ξ) x • a u x) := by
    simp_rw [phaseOscillation_fourierPhase, mul_smul]
    exact (complexMeasureIntegral_smul ν (hi x) _).symm
  simp only [physicalFourierIntegral, he, averagedFourierKernel]
  apply integral_complexMeasureIntegral_swap_of_support μ ν
    (f := fun x u ↦ phaseOscillation (fourierPhase (φ u) ρ ξ) x • a u x)
    hK.measurableSet hKfin
    ((stronglyMeasurable_fourierPhase_joint hφ ham ρ ξ).comp_measurable measurable_swap)
  · intro x u
    simpa only [norm_smul, norm_phaseOscillation, one_mul] using ha u x
  · intro x hx u
    have hz : a u x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs u h))
    simp [hz]

omit [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: An integrable field has a continuous physical Fourier
integral, by dominated convergence with its norm as majorant. -/
theorem continuous_physicalFourierIntegral (μ : Measure E) {h : E → F}
    (hh : Integrable h μ) : Continuous (physicalFourierIntegral μ h) := by
  apply continuous_of_dominated (bound := fun x ↦ ‖h x‖)
  · intro ξ
    have hp : Continuous (fun x ↦ phaseOscillation (fun y ↦ -ξ y) x) := by
      unfold phaseOscillation
      fun_prop
    exact hp.stronglyMeasurable.aestronglyMeasurable.smul hh.aestronglyMeasurable
  · intro ξ
    exact Filter.Eventually.of_forall fun x ↦ by simp only [norm_smul, norm_phaseOscillation, one_mul, le_refl]
  · exact hh.norm
  · apply Filter.Eventually.of_forall
    intro x
    unfold phaseOscillation
    fun_prop

/-- `app:ch_osc:prop:osc-source-shell`: The averaged kernel is continuous in the physical covector,
using the proved source identification and integrability. -/
theorem continuous_averagedFourierKernel (μ : Measure E) (ν : ComplexMeasure D)
    [IsFiniteMeasure ν.variation] {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ))
    (ham : StronglyMeasurable (Function.uncurry a)) (ρ : ℝ)
    {K : Set E} (hK : IsCompact K) (hKfin : μ K ≠ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ u x, ‖a u x‖ ≤ B) (hs : ∀ u, tsupport (a u) ⊆ K) :
    Continuous (averagedFourierKernel μ ν φ a ρ) := by
  have he : averagedFourierKernel μ ν φ a ρ = physicalFourierIntegral μ
      (oscillatorySource ν φ a ρ) := by
    funext ξ
    exact (physicalFourierIntegral_oscillatorySource μ ν hφ ham ρ ξ hK hKfin ha hs).symm
  rw [he]
  exact continuous_physicalFourierIntegral μ
    (integrable_oscillatorySource_joint μ ν hφ ham ρ hK hKfin hB ha hs)

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [CompleteSpace F] [NormedAddCommGroup E] [BorelSpace E] [NormedSpace ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: Ordinary joint measurability suffices for measurability of
the source for second-countable amplitudes, including finite-dimensional complex Hilbert
amplitudes. -/
theorem measurable_oscillatorySource (ν : ComplexMeasure D)
    [IsFiniteMeasure ν.variation] {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ))
    (ha : Measurable (Function.uncurry a)) (ρ : ℝ) :
    Measurable (oscillatorySource ν φ a ρ) :=
  (stronglyMeasurable_oscillatorySource ν hφ ha.stronglyMeasurable ρ).measurable

/-- `app:ch_osc:prop:osc-source-shell`: The source/Fourier identification with ordinary joint
measurability of phase and amplitude. Finite-dimensional complex Hilbert amplitudes satisfy the
ambient completeness and second-countability assumptions. -/
theorem physicalFourierIntegral_oscillatorySource_of_measurable
    (μ : Measure E) (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ)) (ham : Measurable (Function.uncurry a))
    (ρ : ℝ) (ξ : E →L[ℝ] ℝ) {K : Set E} (hK : IsCompact K) (hKfin : μ K ≠ ⊤)
    {B : ℝ} (ha : ∀ u x, ‖a u x‖ ≤ B) (hs : ∀ u, tsupport (a u) ⊆ K) :
    physicalFourierIntegral μ (oscillatorySource ν φ a ρ) ξ =
      averagedFourierKernel μ ν φ a ρ ξ :=
  physicalFourierIntegral_oscillatorySource μ ν hφ ham.stronglyMeasurable ρ ξ hK hKfin ha hs

variable [MeasurableSpace (E →L[ℝ] ℝ)] [BorelSpace (E →L[ℝ] ℝ)]

/-- `app:ch_osc:prop:osc-source-shell`: The averaged kernel is Borel measurable in physical
frequency under ordinary joint measurability and finite common compact support. -/
theorem measurable_averagedFourierKernel (μ : Measure E) (ν : ComplexMeasure D)
    [IsFiniteMeasure ν.variation] {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ)) (ham : Measurable (Function.uncurry a))
    (ρ : ℝ) {K : Set E} (hK : IsCompact K) (hKfin : μ K ≠ ⊤)
    {B : ℝ} (hB : 0 ≤ B) (ha : ∀ u x, ‖a u x‖ ≤ B)
    (hs : ∀ u, tsupport (a u) ⊆ K) :
    Measurable (averagedFourierKernel μ ν φ a ρ) :=
  (continuous_averagedFourierKernel μ ν hφ ham.stronglyMeasurable ρ hK hKfin hB ha hs).measurable

/-- `app:ch_osc:prop:osc-source-shell`: Multiplication of the averaged kernel by a continuous
complex mask preserves strong measurability. Applying this to a complementary mask supplies the
measurability required by the tail integrals. -/
theorem stronglyMeasurable_mask_smul_averagedFourierKernel
    (μ : Measure E) (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    {φ : D → E → ℝ} {a : D → E → F}
    (hφ : Measurable (Function.uncurry φ)) (ham : Measurable (Function.uncurry a))
    (ρ : ℝ) {K : Set E} (hK : IsCompact K) (hKfin : μ K ≠ ⊤)
    {B : ℝ} (hB : 0 ≤ B) (ha : ∀ u x, ‖a u x‖ ≤ B)
    (hs : ∀ u, tsupport (a u) ⊆ K) {χ : (E →L[ℝ] ℝ) → ℂ} (hχ : Continuous χ) :
    StronglyMeasurable (fun ξ ↦ χ ξ • averagedFourierKernel μ ν φ a ρ ξ) :=
  (hχ.measurable.smul (measurable_averagedFourierKernel μ ν hφ ham ρ hK hKfin hB ha hs)).stronglyMeasurable

end JanetCartan.Localization
