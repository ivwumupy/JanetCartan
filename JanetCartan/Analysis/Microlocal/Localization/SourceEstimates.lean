module

public import JanetCartan.Analysis.Microlocal.Localization.AveragedKernel
public import JanetCartan.Analysis.Microlocal.Localization.ComplexFubini
public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel

/-!
# Radial shell estimates for the actual oscillatory source

Assembly of `app:ch_osc:prop:osc-source-shell`. The hypotheses below contain
only regularity, support, phase and amplitude bounds. Fubini, integrability,
Plancherel and the annular split are derived. The constants display the entire
high derivative profiles and are independent of `A`, `L`, `ρ` and the parameter
measure. The amplitude loss `L^b` is fixed before choosing any observation order.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.Localization

variable {D E F ι : Type*} [MeasurableSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The analytic hypotheses of `app:ch_osc:prop:osc-source-shell`, with joint
parameter measurability made explicit. No Fourier estimate is a field. -/
structure SourceShellBounds (φ : D → E → ℝ) (a : D → E → F)
    (U K : Set E) (c G A L b : ℝ) (P C : ℕ → ℝ) : Prop where
  open_domain : IsOpen U
  compact_support : IsCompact K
  support_subset : K ⊆ U
  phase_measurable : Measurable (Function.uncurry φ)
  amplitude_measurable : StronglyMeasurable (Function.uncurry a)
  phase_smooth : ∀ u, ContDiffOn ℝ ∞ (φ u) U
  amplitude_smooth : ∀ u, ContDiffOn ℝ ∞ (a u) U
  amplitude_support : ∀ u, tsupport (a u) ⊆ K
  lower_pos : 0 < c
  lower_lt_upper : c < G
  amplitude_nonneg : 0 ≤ A
  scale_one_le : 1 ≤ L
  loss_nonneg : 0 ≤ b
  phase_constants_nonneg : ∀ j, 0 ≤ P j
  amplitude_constants_nonneg : ∀ r, 0 ≤ C r
  gradient_lower : ∀ u x, x ∈ U → c ≤ ‖fderiv ℝ (φ u) x‖
  gradient_upper : ∀ u x, x ∈ U → ‖fderiv ℝ (φ u) x‖ ≤ G
  phase_derivatives : ∀ u x, x ∈ tsupport (a u) → ∀ j, 1 ≤ j →
    ‖iteratedFDeriv ℝ (j + 1) (φ u) x‖ ≤ P j * L ^ j
  amplitude_derivatives : ∀ u x, x ∈ tsupport (a u) → ∀ r : ℕ,
    ‖iteratedFDeriv ℝ r (a u) x‖ ≤ C r * (A * L ^ ((r : ℝ) + b))

/-- The fixed radial multiplier in `app:ch_osc:prop:osc-source-shell`. Its
complementary bound is displayed so the constants also cover nonpositive masks. -/
structure SourceShellMask (π : (E →L[ℝ] ℝ) → ℂ) (c G ρ W : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ π
  equals_one : ∀ ξ, c * ρ / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 * G * ρ → π ξ = 1
  support : tsupport π ⊆ {ξ | c * ρ / 4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4 * G * ρ}
  bound_nonneg : 0 ≤ W
  complement_bound : ∀ ξ, ‖1 - π ξ‖ ≤ W

variable {φ : D → E → ℝ} {a : D → E → F} {U K : Set E}
  {c G A L b : ℝ} {P C : ℕ → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: separate the fixed amplitude loss from
the per-derivative scale. -/
theorem SourceShellBounds.graded_amplitude (s : SourceShellBounds φ a U K c G A L b P C)
    (u : D) (x : E) (hx : x ∈ tsupport (a u)) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (a u) x‖ ≤ C r * ((A * L ^ b) * L ^ r) := by
  have h := s.amplitude_derivatives u x hx r
  rw [Real.rpow_add (by linarith [s.scale_one_le]), Real.rpow_natCast] at h
  convert h using 1
  ring

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: the zeroth derivative bound extends
across the complement of the amplitude support. -/
theorem SourceShellBounds.amplitude_bound (s : SourceShellBounds φ a U K c G A L b P C)
    (u : D) (x : E) : ‖a u x‖ ≤ C 0 * (A * L ^ b) := by
  by_cases hx : x ∈ tsupport (a u)
  · simpa using s.graded_amplitude u x hx 0
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact mul_nonneg (s.amplitude_constants_nonneg 0)
      (mul_nonneg s.amplitude_nonneg (Real.rpow_nonneg (by linarith [s.scale_one_le]) _))

variable [Fintype ι]

/-- Explicit constant in `app:ch_osc:eq:osc-source-tail`. It contains the
support volume and every high derivative constant, but no variable scale. -/
def sourceTailConstant (e : OrthonormalBasis ι ℝ E) (K : Set E)
    (c G W : ℝ) (P C : ℕ → ℝ) (m : ℝ) (q : ℕ) : ℝ :=
  W * transposeDerivativeConstant e
    (phaseCoefficientDerivativeBound e ((radialGapConstant c G) ^ 2) (max G 1) P) C q 0 *
    volume.real K * Real.sqrt (∫ ξ : E, (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * m)))

/-- `app:ch_osc:eq:osc-source-negative`: the constant after the annular split,
with the physical-frequency Plancherel factor made explicit. -/
def sourceNegativeConstant (e : OrthonormalBasis ι ℝ E) (K : Set E)
    (c G W : ℝ) (P C : ℕ → ℝ) (M : ℝ) (q : ℕ) : ℝ :=
  (c / 4) ^ (-M) * ((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) *
    C 0 * Real.sqrt (volume.real K)) + sourceTailConstant e K c G W P C 0 q

variable (s : SourceShellBounds φ a U K c G A L b P C)
  (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]

include s

omit [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: the actual source is in L¹ and L²;
neither integrability assertion is an additional hypothesis. -/
theorem SourceShellBounds.source_integrable (ρ : ℝ) :
    Integrable (oscillatorySource ν φ a ρ) ∧
      Integrable (fun x ↦ ‖oscillatorySource ν φ a ρ x‖ ^ 2) := by
  have hB : 0 ≤ C 0 * (A * L ^ b) := mul_nonneg (s.amplitude_constants_nonneg 0)
    (mul_nonneg s.amplitude_nonneg (Real.rpow_nonneg (by linarith [s.scale_one_le]) _))
  have hm := (stronglyMeasurable_oscillatorySource ν s.phase_measurable
    s.amplitude_measurable ρ).aestronglyMeasurable (μ := volume)
  exact ⟨integrable_oscillatorySource ν φ a ρ s.compact_support
    s.compact_support.measure_ne_top hB s.amplitude_bound s.amplitude_support hm,
    integrable_norm_sq_of_bounded_support s.compact_support.measurableSet
      s.compact_support.measure_ne_top hm
      ((subset_tsupport _).trans (tsupport_oscillatorySource_subset ν φ a ρ
        s.compact_support.isClosed s.amplitude_support))
      (norm_oscillatorySource_le ν φ a ρ hB s.amplitude_bound)⟩

/-- `app:ch_osc:prop:osc-source-shell`: Fourier identification under precisely
the source hypotheses. -/
theorem SourceShellBounds.fourier_eq (ρ : ℝ) (ξ : E →L[ℝ] ℝ) :
    physicalFourierIntegral volume (oscillatorySource ν φ a ρ) ξ =
      averagedFourierKernel volume ν φ a ρ ξ :=
  physicalFourierIntegral_oscillatorySource volume ν s.phase_measurable
    s.amplitude_measurable ρ ξ s.compact_support s.compact_support.measure_ne_top
    s.amplitude_bound s.amplitude_support

/-- `app:ch_osc:prop:osc-source-shell`: the source L² estimate transferred to
physical frequency by the proved Plancherel identity. -/
theorem SourceShellBounds.fourierL2_le (ρ : ℝ) :
    fourierWeightedL2Norm volume 0 (fun ξ : E ↦
      physicalFourierIntegral volume (oscillatorySource ν φ a ρ)
        (InnerProductSpace.toDual ℝ E ξ)) ≤
      ((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) * C 0 *
        Real.sqrt (volume.real K)) * A * ν.variation.real Set.univ * L ^ b := by
  rw [fourierWeightedL2Norm_zero_physicalFourierIntegral
    (s.source_integrable ν ρ).1 (s.source_integrable ν ρ).2]
  have hB : 0 ≤ C 0 * (A * L ^ b) := mul_nonneg (s.amplitude_constants_nonneg 0)
    (mul_nonneg s.amplitude_nonneg (Real.rpow_nonneg (by linarith [s.scale_one_le]) _))
  apply (mul_le_mul_of_nonneg_left (sourceL2Norm_le ν φ a ρ s.compact_support
    s.compact_support.measure_ne_top hB s.amplitude_bound s.amplitude_support
    (stronglyMeasurable_oscillatorySource ν s.phase_measurable
      s.amplitude_measurable ρ).aestronglyMeasurable) (by positivity)).trans_eq
  ring

/-- `app:ch_osc:eq:osc-source-negative`: the negative spectral energy is
integrable; this follows already from the proved source L² bound. -/
theorem SourceShellBounds.negative_energy_integrable (ρ : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-M) *
      ‖physicalFourierIntegral volume (oscillatorySource ν φ a ρ)
        (InnerProductSpace.toDual ℝ E ξ)‖ ^ 2) := by
  have hi := integrable_norm_sq_physicalFourierIntegral
    (s.source_integrable ν ρ).1 (s.source_integrable ν ρ).2
  have hw : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-M)) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun ξ ↦ Or.inl (show (1 + ‖ξ‖ ^ 2 : ℝ) ≠ 0 by positivity))
  apply hi.mono' (hw.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  filter_upwards [] with ξ
  change ‖(1 + ‖ξ‖ ^ 2) ^ (-M) *
    ‖physicalFourierIntegral volume (oscillatorySource ν φ a ρ)
      (InnerProductSpace.toDual ℝ E ξ)‖ ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_right
    (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖])
      (neg_nonpos.mpr hM)) (sq_nonneg _)).trans_eq (one_mul _)

variable (e : OrthonormalBasis ι ℝ E) {ρ W : ℝ} {π : (E →L[ℝ] ℝ) → ℂ}
  (hρ : 1 ≤ ρ) (hπ : SourceShellMask π c G ρ W)

include hρ hπ

/-- `app:ch_osc:eq:osc-source-tail`: weighted integrability and the radial tail
of the actual source. The Fourier integral here is unnormalized; the normalized
version below includes the paper's `(2π)^(-n)` factor. -/
theorem source_sobolev_tail {m : ℝ} (hm : 0 ≤ m) (q : ℕ)
    (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q) :
    let H := fun ξ : E ↦ (1 - π (InnerProductSpace.toDual ℝ E ξ)) •
      physicalFourierIntegral volume (oscillatorySource ν φ a ρ)
        (InnerProductSpace.toDual ℝ E ξ)
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ m * ‖H ξ‖ ^ 2) ∧
      fourierWeightedL2Norm volume m H ≤
        sourceTailConstant e K c G W P C m q * A * ν.variation.real Set.univ * L ^ b *
          (ρ ^ (m + (Module.finrank ℝ E : ℝ) / 2) * (L / ρ) ^ q) := by
  dsimp only
  simp_rw [s.fourier_eq ν]
  have ht := sobolev_tail_averagedFourierKernel_le (μ := volume)
    s.open_domain s.compact_support s.support_subset e ν φ a π q
    s.phase_smooth s.amplitude_smooth s.amplitude_support s.lower_pos
    (s.lower_pos.trans s.lower_lt_upper)
    (mul_nonneg s.amplitude_nonneg (Real.rpow_nonneg (by linarith [s.scale_one_le]) _))
    (by linarith [s.scale_one_le]) hρ hπ.bound_nonneg s.gradient_lower s.gradient_upper
    hπ.equals_one hπ.complement_bound s.phase_constants_nonneg s.amplitude_constants_nonneg
    s.phase_derivatives s.graded_amplitude hm hq
    (μξ := volume)
  have hcont : Continuous (fun ξ : E ↦ (1 - π (InnerProductSpace.toDual ℝ E ξ)) •
      averagedFourierKernel volume ν φ a ρ (InnerProductSpace.toDual ℝ E ξ)) := by
    rw [show averagedFourierKernel volume ν φ a ρ =
      physicalFourierIntegral volume (oscillatorySource ν φ a ρ) from
        funext (fun ξ ↦ (s.fourier_eq ν ρ ξ).symm)]
    exact (continuous_const.sub (hπ.smooth.continuous.comp
      (InnerProductSpace.toDual ℝ E).continuous)).smul
      ((continuous_physicalFourierIntegral volume (s.source_integrable ν ρ).1).comp
        (InnerProductSpace.toDual ℝ E).continuous)
  obtain ⟨hi, hb⟩ := ht hcont.aestronglyMeasurable
  refine ⟨hi, hb.trans_eq ?_⟩
  dsimp [sourceTailConstant]
  ring

/-- `app:ch_osc:eq:osc-source-negative`: the actual source's negative Sobolev
gain, with explicit integration order and constants, after discharging Fubini,
Plancherel, the annular split and the scale absorption. -/
theorem source_negative_sobolev {σ M : ℝ} (hM : 0 ≤ M)
    (hgap : L ≤ ρ ^ (1 - σ)) (q : ℕ)
    (hq : (Module.finrank ℝ E : ℝ) / 2 < q)
    (horder : M + (Module.finrank ℝ E : ℝ) / 2 ≤ σ * q) :
    fourierWeightedL2Norm volume (-M) (fun ξ : E ↦
      physicalFourierIntegral volume (oscillatorySource ν φ a ρ)
        (InnerProductSpace.toDual ℝ E ξ)) ≤
      sourceNegativeConstant e K c G W P C M q * A * ν.variation.real Set.univ *
        L ^ b * ρ ^ (-M) := by
  have hcoeff := transposeDerivativeConstant_nonneg e
    (phaseCoefficientDerivativeBound_nonneg e ((radialGapConstant c G) ^ 2) (max G 1) P)
    s.amplitude_constants_nonneg q 0
  have hA : 0 ≤ A * L ^ b := mul_nonneg s.amplitude_nonneg
    (Real.rpow_nonneg (by linarith [s.scale_one_le]) _)
  have hdecay (ξ : E) := norm_masked_averagedFourierKernel_le (μ := volume)
    s.open_domain s.compact_support s.support_subset e ν φ a π
    (InnerProductSpace.toDual ℝ E ξ) q s.phase_smooth s.amplitude_smooth s.amplitude_support
    s.lower_pos (s.lower_pos.trans s.lower_lt_upper) hA (by linarith [s.scale_one_le])
    (by linarith) hπ.bound_nonneg s.gradient_lower s.gradient_upper hπ.equals_one
    (hπ.complement_bound _) s.phase_constants_nonneg s.amplitude_constants_nonneg
    s.phase_derivatives s.graded_amplitude
  simp only [LinearIsometryEquiv.norm_map] at hdecay
  simp_rw [← s.fourier_eq ν] at hdecay
  have hcont := continuous_physicalFourierIntegral volume (s.source_integrable ν ρ).1
  have ht := fourierWeightedL2Norm_negative_le_of_scaleRatio hρ
    (by linarith [s.scale_one_le]) (div_pos s.lower_pos (by norm_num : (0 : ℝ) < 4))
    hM hgap hq horder
    (show 0 ≤ W * transposeDerivativeConstant e
      (phaseCoefficientDerivativeBound e ((radialGapConstant c G) ^ 2) (max G 1) P) C q 0 *
      (A * L ^ b) * volume.real K * ν.variation.real Set.univ from
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hπ.bound_nonneg hcoeff) hA)
        measureReal_nonneg) measureReal_nonneg)
    (fun ξ : E ↦ π (InnerProductSpace.toDual ℝ E ξ))
    (fun ξ : E ↦ physicalFourierIntegral volume (oscillatorySource ν φ a ρ)
      (InnerProductSpace.toDual ℝ E ξ))
    (fun ξ hx ↦ image_eq_zero_of_notMem_tsupport (fun hs ↦ by
      have hl := (hπ.support hs).1
      simp only [LinearIsometryEquiv.norm_map] at hl
      linarith))
    (integrable_norm_sq_physicalFourierIntegral (s.source_integrable ν ρ).1
      (s.source_integrable ν ρ).2)
    (((continuous_const.sub (hπ.smooth.continuous.comp
      (InnerProductSpace.toDual ℝ E).continuous)).smul
      (hcont.comp (InnerProductSpace.toDual ℝ E).continuous)).aestronglyMeasurable)
    (s.fourierL2_le ν ρ) hdecay
  apply ht.trans_eq
  simp only [sourceNegativeConstant, sourceTailConstant, mul_zero, sub_zero]
  ring

end JanetCartan.Localization
