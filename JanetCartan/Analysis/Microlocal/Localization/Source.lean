module

public import JanetCartan.Analysis.Microlocal.Localization.Parameter
public import JanetCartan.Analysis.Microlocal.Localization.Gap
public import JanetCartan.Analysis.Microlocal.Localization.RadialIntegral

/-!
# The compactly supported oscillatory source

Definitions and the physical-space L² estimate in
`app:ch_osc:prop:osc-source-shell`. Measurability is explicit in the integral
estimates; the support and pointwise estimates need no parameter regularity.
The averaged Fourier kernel is defined separately so that its identification
with the Fourier transform can be proved using Fubini.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.Localization

variable {D E F : Type*} [MeasurableSpace D]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

/-- `app:ch_osc:prop:osc-source-shell`: The actual parameter-averaged source. -/
def oscillatorySource (ν : ComplexMeasure D) (φ : D → E → ℝ)
    (a : D → E → F) (ρ : ℝ) (x : E) : F :=
  complexMeasureIntegral ν (fun u ↦ phaseOscillation (fun y ↦ ρ * φ u y) x • a u x)

/-- `app:ch_osc:prop:osc-source-shell`: The source vanishes wherever all amplitudes vanish. -/
theorem oscillatorySource_eq_zero (ν : ComplexMeasure D) (φ : D → E → ℝ)
    (a : D → E → F) (ρ : ℝ) {x : E} (ha : ∀ u, a u x = 0) :
    oscillatorySource ν φ a ρ x = 0 := by
  simp [oscillatorySource, ha, complexMeasureIntegral, VectorMeasure.integral_zero]

/-- `app:ch_osc:prop:osc-source-shell`: The total variation controls the source pointwise. -/
theorem norm_oscillatorySource_le (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    (φ : D → E → ℝ) (a : D → E → F) (ρ : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ u x, ‖a u x‖ ≤ B) (x : E) :
    ‖oscillatorySource ν φ a ρ x‖ ≤ B * ν.variation.real Set.univ := by
  apply norm_complexMeasureIntegral_le ν _ hB
  exact Filter.Eventually.of_forall (fun u ↦ by
    simpa only [norm_smul, norm_phaseOscillation, one_mul] using ha u x)

variable [NormedAddCommGroup E]

/-- `app:ch_osc:prop:osc-source-shell`: A common closed support is preserved by parameter averaging. -/
theorem tsupport_oscillatorySource_subset (ν : ComplexMeasure D) (φ : D → E → ℝ)
    (a : D → E → F) (ρ : ℝ) {K : Set E} (hK : IsClosed K)
    (ha : ∀ u, tsupport (a u) ⊆ K) :
    tsupport (oscillatorySource ν φ a ρ) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra h
  exact hx (oscillatorySource_eq_zero ν φ a ρ (fun u ↦
    image_eq_zero_of_notMem_tsupport (fun hx ↦ h (ha u hx))))

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

omit [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup E] [BorelSpace E] in
/-- `app:ch_osc:prop:osc-source-shell`: A bounded measurable field with finite-measure support
is Bochner integrable, as required for its ordinary Fourier integral. -/
theorem integrable_of_bounded_support {h : E → F} {K : Set E} {B : ℝ}
    (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤) (hh : AEStronglyMeasurable h μ)
    (hs : Function.support h ⊆ K) (hb : ∀ x, ‖h x‖ ≤ B) : Integrable h μ := by
  have hi : Integrable (K.indicator (fun _ : E ↦ B)) μ :=
    (integrableOn_const hKfin).integrable_indicator hK
  apply hi.mono' hh
  filter_upwards [] with x
  by_cases hx : x ∈ K
  · simpa only [Set.indicator_of_mem hx] using hb x
  · have hz : h x = 0 := Function.notMem_support.mp (fun h ↦ hx (hs h))
    simp [hz, hx]

/-- `app:ch_osc:prop:osc-source-shell`: Finite common support and the amplitude bound make
the measurable source Bochner integrable. -/
theorem integrable_oscillatorySource (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    (φ : D → E → ℝ) (a : D → E → F) (ρ : ℝ) {K : Set E} (hK : IsCompact K)
    (hKfin : μ K ≠ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ u x, ‖a u x‖ ≤ B) (hs : ∀ u, tsupport (a u) ⊆ K)
    (hm : AEStronglyMeasurable (oscillatorySource ν φ a ρ) μ) :
    Integrable (oscillatorySource ν φ a ρ) μ :=
  integrable_of_bounded_support hK.measurableSet hKfin hm
    ((subset_tsupport _).trans (tsupport_oscillatorySource_subset ν φ a ρ hK.isClosed hs))
    (norm_oscillatorySource_le ν φ a ρ hB ha)

omit [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup E] [BorelSpace E] in
/-- `app:ch_osc:prop:osc-source-shell`: A bounded measurable field with finite-measure support
has an integrable squared norm. -/
theorem integrable_norm_sq_of_bounded_support {h : E → F} {K : Set E} {B : ℝ}
    (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤) (hh : AEStronglyMeasurable h μ)
    (hs : Function.support h ⊆ K) (hb : ∀ x, ‖h x‖ ≤ B) :
    Integrable (fun x ↦ ‖h x‖ ^ 2) μ := by
  have hi : Integrable (K.indicator (fun _ : E ↦ B ^ 2)) μ :=
    (integrableOn_const hKfin).integrable_indicator hK
  apply hi.mono' (hh.norm.pow 2)
  filter_upwards [] with x
  by_cases hx : x ∈ K
  · change ‖‖h x‖ ^ 2‖ ≤ _
    rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
  · have hz : h x = 0 := Function.notMem_support.mp (fun h ↦ hx (hs h))
    simp [hz, hx]

omit [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup E] [BorelSpace E] in
/-- `app:ch_osc:prop:osc-source-shell`: The squared L² bound includes exactly the support volume. -/
theorem integral_norm_sq_le_of_bounded_support {h : E → F} {K : Set E} {B : ℝ}
    (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤) (hh : AEStronglyMeasurable h μ)
    (hs : Function.support h ⊆ K) (hb : ∀ x, ‖h x‖ ≤ B) :
    (∫ x, ‖h x‖ ^ 2 ∂μ) ≤ B ^ 2 * μ.real K := by
  have hi : Integrable (K.indicator (fun _ : E ↦ B ^ 2)) μ :=
    (integrableOn_const hKfin).integrable_indicator hK
  calc
    _ ≤ ∫ x, K.indicator (fun _ : E ↦ B ^ 2) x ∂μ := by
      apply integral_mono (integrable_norm_sq_of_bounded_support hK hKfin hh hs hb) hi
      intro x
      by_cases hx : x ∈ K
      · simpa only [Set.indicator_of_mem hx] using pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
      · have hz : h x = 0 := Function.notMem_support.mp (fun h ↦ hx (hs h))
        simp [hz, hx]
    _ = _ := by rw [integral_indicator_const _ hK, smul_eq_mul, mul_comm]

/-- `app:ch_osc:prop:osc-source-shell`: The source L² bound from the amplitude bound and common
compact support. Joint measurability can be used to discharge the explicit measurability premise. -/
theorem sourceL2Norm_le (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    (φ : D → E → ℝ) (a : D → E → F) (ρ : ℝ) {K : Set E} (hK : IsCompact K)
    (hKfin : μ K ≠ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ u x, ‖a u x‖ ≤ B) (hs : ∀ u, tsupport (a u) ⊆ K)
    (hm : AEStronglyMeasurable (oscillatorySource ν φ a ρ) μ) :
    Real.sqrt (∫ x, ‖oscillatorySource ν φ a ρ x‖ ^ 2 ∂μ) ≤
      B * ν.variation.real Set.univ * Real.sqrt (μ.real K) := by
  apply (Real.sqrt_le_sqrt (integral_norm_sq_le_of_bounded_support hK.measurableSet hKfin hm
    ((subset_tsupport _).trans (tsupport_oscillatorySource_subset ν φ a ρ hK.isClosed hs))
    (norm_oscillatorySource_le ν φ a ρ hB ha))).trans_eq
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

variable [NormedSpace ℝ E]

/-- `app:ch_osc:prop:osc-source-shell`: The unnormalized Fourier integral at a physical
frequency covector. The paper multiplies this by `(2π)^(-n)`; Mathlib uses the
unit-period covector `2π ξ`. -/
def physicalFourierIntegral (μ : Measure E) (h : E → F) (ξ : E →L[ℝ] ℝ) : F :=
  ∫ x, phaseOscillation (fun y ↦ -ξ y) x • h x ∂μ

/-- `app:ch_osc:prop:osc-source-shell`: The parameter average of the unnormalized physical
Fourier kernels, with exact signed covector `ρ dφ - ξ`. Fubini is needed to identify this with
the Fourier transform of `oscillatorySource`. -/
def averagedFourierKernel (μ : Measure E) (ν : ComplexMeasure D)
    (φ : D → E → ℝ) (a : D → E → F) (ρ : ℝ) (ξ : E →L[ℝ] ℝ) : F :=
  complexMeasureIntegral ν (fun u ↦ ∫ x, phaseOscillation (fourierPhase (φ u) ρ ξ) x • a u x ∂μ)

end JanetCartan.Localization
