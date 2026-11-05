module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Noncomparable.BaseIntegral
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives

/-!
# Integrating the two Fourier measures after common-base decay

For `app:ch_regular:lem:finite-chain`, Fubini separates the actual output jets
into a common-base integral and a frequency-only factor. This is the bridge
from `BaseIntegral.norm_halfSpaceIntegral_le` to unequal-shell estimates in
`app:ch_regular:eq:chain-tail`. No frequency derivative is used.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel HalfSpace BaseIntegral
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance noncomparableBaseVolumeHaar : (volume : Measure (ℝ × E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure E)
local instance noncomparableFrequencyVolumeHaar : (volume : Measure ((ℝ × E) × (ℝ × E))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × E)) (volume : Measure (ℝ × E))
local instance noncomparableTangentialVolumeHaar : (volume : Measure (TangentialVariables E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × E))
    (volume : Measure ((ℝ × E) × (ℝ × E)))

local instance noncomparableSpaceVolumeSFinite : SFinite (volume : Measure E) := inferInstance
local instance noncomparableBaseVolumeSFinite : SFinite (volume : Measure (ℝ × E)) := inferInstance
local instance noncomparableFrequencyVolumeSFinite : SFinite (volume : Measure ((ℝ × E) × (ℝ × E))) := inferInstance
local instance noncomparableTangentialVolumeSFinite : SFinite (volume : Measure (TangentialVariables E)) :=
  inferInstanceAs (SFinite ((volume : Measure (ℝ × E)).prod
    (volume : Measure ((ℝ × E) × (ℝ × E)))))

/-- Regroup the half-space integral with both Fourier covectors outermost.
Integrability, rather than formal interchange of oscillatory integrals, is the
premise; compact primitive carriers discharge it for the concrete kernels
(`app:ch_regular:lem:finite-chain`). -/
theorem halfSpaceIntegral_eq_frequency_first
    {f : ℝ × TangentialVariables E → ℂ}
    (hf : Integrable f (volume.prod volume)) :
    halfSpaceIntegral volume f =
      ∫ w : (ℝ × E) × (ℝ × E), halfSpaceIntegral volume
        (fun p : ℝ × (ℝ × E) => f (p.1, p.2, w)) := by
  let μ := (volume : Measure ℝ).restrict (Ici 0)
  have hf' : Integrable f (μ.prod (volume : Measure (TangentialVariables E))) := by
    rw [Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ)) (ν := (volume : Measure (TangentialVariables E)))]
    exact hf.restrict
  have hm := measurePreserving_prodAssoc μ (volume : Measure (ℝ × E))
    (volume : Measure ((ℝ × E) × (ℝ × E)))
  have hi := hm.integrable_comp_of_integrable hf'
  unfold halfSpaceIntegral
  rw [← Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ)) (ν := (volume : Measure (TangentialVariables E)))]
  simp_rw [← Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × E)))]
  exact (hm.integral_comp' f).symm.trans (integral_prod_symm _ hi)

/-- The frequency-only factor in the scalar output derivative. Its definition
retains both primitive symbols, the regularizer, and every output-symbol jet
(`app:ch_regular:eq:chain-tail`). -/
def outputFrequencyFactor (ρ : ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    (w : (ℝ × E) × (ℝ × E)) : ℂ :=
  r (ρ • w.1) * mi xi (ρ • w.2) * rescaledOutputSymbolJet ρ mo xo m v w.1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Exact separation of the primitive weights and the frequency factor, for
both literal orientations (`app:ch_regular:lem:finite-chain`). -/
theorem outputDifferentiatedAmplitude_eq_weight_mul_frequency
    (upper : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (x : ℝ × TangentialVariables E) :
    outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v x =
      ρ ^ m • (weightAmplitude upper α β (x.1, x.2.1) *
        outputFrequencyFactor ρ mi mo r xi xo m v x.2.2) := by
  rw [outputDifferentiatedAmplitude_eq_scaled_outputSymbolJet upper hρ α β mi mo r
    xi xo m v ho x]
  congr 1
  cases upper <;> simp only [outputIndependentAmplitude, normalizedAmplitude,
    lowerAmplitude, upperAmplitude, weightAmplitude, outputFrequencyFactor,
    rescaledOutputSymbolJet, Bool.false_eq_true, ↓reduceIte, sub_zero,
    mul_one, Prod.smul_fst, Prod.smul_snd] <;> ring

/-- Fubini for the actual regularized output derivatives, with both Fourier
measures, their Jacobian, and `ρ^m` explicit. All integrability hypotheses are
proved from primitive smoothness and compact carriers
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_fourierKernel_apply_eq_frequency_integral
    (upper : Bool) {ρ : ℝ} (hρ : 0 < ρ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r)
    {Kα Kβ Ko Ki : Set (ℝ × E)}
    (hKα : IsCompact Kα) (hKβ : IsCompact Kβ) (hKo : IsCompact Ko) (hKi : IsCompact Ki)
    (hsα : tsupport α ⊆ Kα) (hsβ : tsupport β ⊆ Kβ)
    (hsr : tsupport (fun ξ => r (ρ • ξ)) ⊆ Ko)
    (hsi : tsupport (fun ξ => mi xi (ρ • ξ)) ⊆ Ki) :
    iteratedFDeriv ℝ m (fun y => if upper then upperFourierKernel α β mi mo r xi y
      else lowerFourierKernel α β mi mo r xi y) xo v =
      ((normalization (E := E)) ^ 2 * ρ ^ (2 * (1 + Module.finrank ℝ E)) * ρ ^ m) •
        ∫ w : (ℝ × E) × (ℝ × E),
          halfSpaceOscillatoryIntegral volume ρ (basePhase upper xi xo w)
            (weightAmplitude upper α β) * outputFrequencyFactor ρ mi mo r xi xo m v w := by
  let a := outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v
  have ha := contDiff_outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v
    hα hβ hi ho hr
  have hc : HasCompactSupport a := (isCompact_amplitudeCarrier hKα hKβ hKo hKi).of_isClosed_subset (isClosed_tsupport _) (tsupport_outputDifferentiatedAmplitude_subset
      upper ρ α β mi mo r xi xo m v hKα hKβ hKo hKi hsα hsβ hsr hsi)
  rw [iteratedFDeriv_fourierKernel_apply_eq_halfSpace upper hρ α β mi mo r xi xo m v
    hα hβ hi ho hr hKα hKβ hKo hKi hsα hsβ hsr hsi]
  unfold halfSpaceOscillatoryIntegral
  rw [halfSpaceIntegral_eq_frequency_first
    (integrable_oscillatoryIntegrand (contDiff_literalPhase upper xi xo) ha hc ρ)]
  simp_rw [outputDifferentiatedAmplitude_eq_weight_mul_frequency upper hρ.ne' α β mi mo r
    xi xo m v ho, mul_smul_comm]
  simp only [halfSpaceIntegral, integral_smul, ← mul_assoc, integral_mul_const, smul_smul]
  rfl

end JanetCartan.FiniteChain.Retarded.KernelDecay
