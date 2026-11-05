module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Cutoffs
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Rescaling
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.SingleShell

/-!
# Exact physical and normalized graph kernels

These identities connect the two kernel APIs used in
`app:ch_regular:eq:joint-kernel-phase`. They retain both physical amplitude
positions, the input shoulder, the complementary output symbol, and all three
Fourier normalizations. No shell estimate or decomposition identity is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Pointwise Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
open FourierIntegral
variable {n r : ℕ}
attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The real and complex normalizations in the estimate and limit APIs agree
exactly (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem jointNormalization_coe (n : ℕ) :
    (KernelEstimates.jointNormalization n : ℂ) = KernelLimits.jointNormalization n := by
  rw [KernelLimits.jointNormalization_eq_cube]
  simp [KernelEstimates.jointNormalization]

/-- The estimate API's five product measures are the physical product volume
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem jointMeasure_eq_volume (n : ℕ) :
    KernelEstimates.jointMeasure n = (volume : Measure (JointVariables (Euclidean n))) := by
  simp only [KernelEstimates.jointMeasure, JointVariables, Measure.volume_eq_prod]

/-- Rescaling the input-frequency carrier does not rescale either base position
(`app:ch_regular:eq:joint-kernel-phase`). -/
def physicalInputCarriers {A : FullAmplitude n r} {mi : LocalizerSymbol n}
    {χA χo : Euclidean n → ℝ} (c : KernelLimits.RegularizedCarriers A mi χA χo)
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    KernelLimits.RegularizedCarriers A (fun q => mi (q.1, ρ⁻¹ • q.2)) χA χo where
  amplitudeBase := c.amplitudeBase
  inputBase := c.inputBase
  inputFrequency := ρ • c.inputFrequency
  compact_amplitudeBase := c.compact_amplitudeBase
  compact_inputBase := c.compact_inputBase
  compact_inputFrequency := c.compact_inputFrequency.smul ρ
  compact_graphCutoff := c.compact_graphCutoff
  compact_outputCutoff := c.compact_outputCutoff
  amplitude_zero := c.amplitude_zero
  input_zero := by
    intro y η hyη
    apply c.input_zero
    intro h
    apply hyη
    refine ⟨h.1, ?_⟩
    exact ⟨ρ⁻¹ • η, h.2, by simp [smul_smul, hρ]⟩

/-- Carriers for the normalized integrand retain the physical full amplitude
`A u z (ρ • ξ)` (`app:ch_regular:eq:joint-kernel-phase`). -/
def normalizedFrequencyCarriers {A : FullAmplitude n r} {mi : LocalizerSymbol n}
    {χA χo : Euclidean n → ℝ} (c : KernelLimits.RegularizedCarriers A mi χA χo)
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    KernelLimits.RegularizedCarriers (fun u z ξ => A u z (ρ • ξ)) mi
      (fun ξ => χA (ρ • ξ)) (fun ζ => χo (ρ • ζ)) where
  amplitudeBase := c.amplitudeBase
  inputBase := c.inputBase
  inputFrequency := c.inputFrequency
  compact_amplitudeBase := c.compact_amplitudeBase
  compact_inputBase := c.compact_inputBase
  compact_inputFrequency := c.compact_inputFrequency
  compact_graphCutoff := c.compact_graphCutoff.comp_smul hρ
  compact_outputCutoff := c.compact_outputCutoff.comp_smul hρ
  amplitude_zero := fun u z ξ hu => c.amplitude_zero u z (ρ • ξ) hu
  input_zero := c.input_zero

/-- Rescaling only the three covectors gives the exact normalized integrand,
including the physical amplitude argument (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem jointIntegrand_eq_physical_rescale (backward : Bool)
    (S φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hφ : ∀ u ξ, S u (ρ • ξ) = ρ * φ u ξ) (p : JointVariables (Euclidean n)) :
    KernelEstimates.jointIntegrand backward ρ φ A mi mo χA χo x y p =
      KernelLimits.regularizedJointIntegrand backward S A
        (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2))
        χA χo x y (p.1, ρ • p.2) := by
  rw [KernelLimits.regularizedJointIntegrand,
    KernelLimits.jointPhase_rescale backward S φ x y ρ p (hφ _ _),
    KernelLimits.regularizedJointAmplitude_rescale A mi mo χA χo x y hρ p]
  simp only [KernelEstimates.jointIntegrand, JanetCartan.Localization.phaseOscillation,
    Pi.smul_apply, smul_eq_mul, mul_comm Complex.I]

/-- Absolute integrability of the normalized joint integral follows from
primitive continuity and compact carriers. This is the Fubini input for the
exact bridge, not a kernel estimate (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem integrable_jointIntegrand (backward : Bool)
    (S φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hφ : ∀ u ξ, S u (ρ • ξ) = ρ * φ u ξ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : KernelLimits.RegularizedCarriers A mi χA χo) :
    Integrable (KernelEstimates.jointIntegrand backward ρ φ A mi mo χA χo x y)
      (KernelEstimates.jointMeasure n) := by
  rw [jointMeasure_eq_volume]
  have hscale : Continuous (fun q : Euclidean n × Euclidean n => (q.1, ρ⁻¹ • q.2)) :=
    by fun_prop
  have hcont : Continuous
      (KernelEstimates.jointIntegrand backward ρ φ A mi mo χA χo x y) := by
    have he := (KernelLimits.regularizedJointIntegrand_continuous backward S A
      (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2)) χA χo
      hS hA (hi.comp hscale) (ho.comp hscale) hg hc).comp
        (f := fun p : JointVariables (Euclidean n) => ((x,y), (p.1, ρ • p.2))) (by fun_prop)
    simpa only [Function.comp_def, ← jointIntegrand_eq_physical_rescale backward S φ A mi mo χA χo x y hρ hφ]
      using he
  apply hcont.integrable_of_hasCompactSupport
  let cn := normalizedFrequencyCarriers c hρ
  apply HasCompactSupport.intro cn.compact_jointCarrier
  intro p hp
  have hz := cn.integrand_zero backward (fun _ _ => 0) mo x y p (fun h => hp h.1)
  have ha : jointAmplitude ρ A mi mo χA χo x y p = 0 := by
    simpa only [KernelLimits.regularizedJointIntegrand, smul_eq_zero,
      Complex.exp_ne_zero, false_or, KernelLimits.regularizedJointAmplitude,
      jointAmplitude] using hz
  simp [KernelEstimates.jointIntegrand, ha]

/-- The exact physical cutoff-pair kernel is the normalized joint kernel used
by `BufferedDecay`. The equality keeps `(2π)^(-3n)`, `ρ^(3n)`, and the full
matrix amplitude; hence it also preserves the Frobenius norm
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem regularizedJointKernel_eq_normalized (backward : Bool)
    (S φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (hφ : ∀ u ξ, S u (ρ • ξ) = ρ * φ u ξ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : KernelLimits.RegularizedCarriers A mi χA χo) :
    KernelLimits.regularizedJointKernel backward S A
      (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2)) χA χo x y =
      KernelEstimates.regularizedJointKernel backward ρ φ A mi mo χA χo x y := by
  rw [KernelLimits.regularizedJointKernel_rescale backward S φ A mi mo χA χo x y
    hρ hφ hS hA hi ho hg hc (physicalInputCarriers c hρ.ne')]
  have hint := integrable_jointIntegrand backward S φ A mi mo χA χo x y hρ.ne'
    hφ hS hA hi ho hg hc c
  rw [jointMeasure_eq_volume, Measure.volume_eq_prod] at hint
  unfold KernelEstimates.regularizedJointKernel
  change _ = (KernelEstimates.jointNormalization n * ρ ^ (3 * n)) •
    ∫ p, KernelEstimates.jointIntegrand backward ρ φ A mi mo χA χo x y p
      ∂KernelEstimates.jointMeasure n
  conv_rhs =>
    arg 2
    rw [jointMeasure_eq_volume, Measure.volume_eq_prod, integral_prod _ hint]
  simp only [KernelEstimates.jointIntegrand,
    JanetCartan.Localization.phaseOscillation, Pi.smul_apply, smul_eq_mul,
    mul_comm Complex.I, ← jointNormalization_coe]
  rw [Complex.coe_smul, smul_smul]

/-- A compact rectangular restriction does not change the normalized kernel
when the primitive amplitude and cutoff supports lie there. This proves the
shell identity needed to apply `Noncomparable.norm_iteratedFDeriv_regularizedShellKernel_le`
to an actual physical cutoff pair (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem normalizedJointKernel_eq_restricted (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    {Kb : Set (Euclidean n × Euclidean n)} {Kξ Kη Kζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hKξ : IsCompact Kξ) (hKη : IsCompact Kη) (hKζ : IsCompact Kζ)
    (hA : ∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0)
    (hχA : tsupport (fun ξ => χA (ρ • ξ)) ⊆ Kξ)
    (hmi : tsupport (fun η => mi (y, η)) ⊆ Kη)
    (hχo : tsupport (fun ζ => χo (ρ • ζ)) ⊆ Kζ) :
    KernelEstimates.regularizedJointKernel backward ρ φ A mi mo χA χo x y =
      KernelEstimates.Noncomparable.regularizedShellKernel backward ρ φ A mi mo χA χo
        Kb Kξ Kη Kζ x y := by
  have hs := KernelEstimates.tsupport_jointAmplitude_subset ρ A mi mo χA χo x y
    hKb hKξ hKη hKζ hA hχA hmi hχo
  unfold KernelEstimates.regularizedJointKernel
    KernelEstimates.Noncomparable.regularizedShellKernel
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hz : jointAmplitude ρ A mi mo χA χo x y p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hp (hs hh))
  simp [KernelEstimates.jointIntegrand, hz]

/-- The restriction identity holds for every actual evaluated output
derivative, with no assumed derivative formula or kernel bound
(`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_normalizedJointKernel_eq_restricted (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    {Kb : Set (Euclidean n × Euclidean n)} {Kξ Kη Kζ : Set (Euclidean n)}
    (hKb : IsCompact Kb) (hKξ : IsCompact Kξ) (hKη : IsCompact Kη) (hKζ : IsCompact Kζ)
    (hA : ∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0)
    (hχA : tsupport (fun ξ => χA (ρ • ξ)) ⊆ Kξ)
    (hmi : tsupport (fun η => mi (y, η)) ⊆ Kη)
    (hχo : tsupport (fun ζ => χo (ρ • ζ)) ⊆ Kζ)
    (m : ℕ) (v : Fin m → Euclidean n) :
    iteratedFDeriv ℝ m
        (fun t => KernelEstimates.regularizedJointKernel backward ρ φ A mi mo χA χo t y) x v =
      iteratedFDeriv ℝ m
        (fun t => KernelEstimates.Noncomparable.regularizedShellKernel backward ρ φ A mi mo
          χA χo Kb Kξ Kη Kζ t y) x v := by
  congr 2
  funext t
  exact normalizedJointKernel_eq_restricted backward ρ φ A mi mo χA χo t y
    hKb hKξ hKη hKζ hA hχA hmi hχo

/-- Physical and normalized actual output derivatives agree as matrices, and
therefore in Frobenius norm. Consumer: transfer of the primitive estimates to
the independently indexed physical cutoff pairs (`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_physicalJointKernel_eq_normalized (backward : Bool)
    (S φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (hφ : ∀ u ξ, S u (ρ • ξ) = ρ * φ u ξ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : KernelLimits.RegularizedCarriers A mi χA χo)
    (m : ℕ) (v : Fin m → Euclidean n) :
    iteratedFDeriv ℝ m
        (fun t => KernelLimits.regularizedJointKernel backward S A
          (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2)) χA χo t y) x v =
      iteratedFDeriv ℝ m
        (fun t => KernelEstimates.regularizedJointKernel backward ρ φ A mi mo χA χo t y) x v := by
  congr 2
  funext t
  exact regularizedJointKernel_eq_normalized backward S φ A mi mo χA χo t y
    hρ hφ hS hA hi ho hg hc c

/-- A phase extension changes no normalized cutoff-pair kernel when it agrees
where the physical full amplitude and graph cutoff contribute. This is the
support-local equality required when applying a globally smooth estimate to a
phase defined on a conic chart (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem normalizedJointKernel_congr_phase (backward : Bool) (ρ : ℝ)
    (φ ψ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (hphase : ∀ u z ξ, A u z (ρ • ξ) ≠ 0 → χA (ρ • ξ) ≠ 0 → φ u ξ = ψ u ξ) :
    KernelEstimates.regularizedJointKernel backward ρ φ A mi mo χA χo x y =
      KernelEstimates.regularizedJointKernel backward ρ ψ A mi mo χA χo x y := by
  unfold KernelEstimates.regularizedJointKernel
  congr 1
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hA : A p.1.1 p.1.2 (ρ • p.2.1) = 0
  · simp [jointAmplitude, hA]
  by_cases hg : χA (ρ • p.2.1) = 0
  · simp [jointAmplitude, hg]
  have hp : jointPhase backward φ x y p = jointPhase backward ψ x y p := by
    cases backward <;> simp [jointPhase, forwardPhase, reversePhase,
      hphase p.1.1 p.1.2 p.2.1 hA hg]
  simp only [JanetCartan.Localization.phaseOscillation, Pi.smul_apply, hp]

end JanetCartan.FiniteChain.Graph.PhysicalShells
