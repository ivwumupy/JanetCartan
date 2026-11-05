module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Factorization

/-!
# Output differentiation of the actual normalized Fourier kernels

For `app:ch_regular:lem:finite-chain`, differentiation of every fixed order
passes through the normalized half-space integral, with the two Fourier
normalizations and the full Jacobian retained. The scalar amplitudes retain
output-symbol derivatives. Smoothness, domination and integrability follow
from the primitive smooth factors and common compact carrier.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel HalfSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance outputDerivativeBaseVolumeHaar :
    (volume : Measure (ℝ × E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure E)
local instance outputDerivativeFrequenciesVolumeHaar :
    (volume : Measure ((ℝ × E) × (ℝ × E))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × E)) (volume : Measure (ℝ × E))
local instance outputDerivativeTangentialVolumeHaar :
    (volume : Measure (TangentialVariables E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × E))
    (volume : Measure ((ℝ × E) × (ℝ × E)))

/-- Every fixed order of output differentiation of the actual lower or literal
upper Fourier kernel commutes with its normalized half-space integral. The
hypotheses are only primitive smoothness and compact frequency/weight supports;
domination is proved on a compact output neighborhood. This is the derivative
identity needed for `app:ch_regular:eq:chain-tail`. -/
theorem iteratedFDeriv_fourierKernel_eq_integral
    (upper : Bool) {ρ : ℝ} (hρ : 0 < ρ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (m : ℕ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r)
    {Kα Kβ Ko Ki : Set (ℝ × E)}
    (hKα : IsCompact Kα) (hKβ : IsCompact Kβ) (hKo : IsCompact Ko) (hKi : IsCompact Ki)
    (hsα : tsupport α ⊆ Kα) (hsβ : tsupport β ⊆ Kβ)
    (hsr : tsupport (fun ξ => r (ρ • ξ)) ⊆ Ko)
    (hsi : tsupport (fun ξ => mi xi (ρ • ξ)) ⊆ Ki) :
    iteratedFDeriv ℝ m (fun y => if upper then upperFourierKernel α β mi mo r xi y
      else lowerFourierKernel α β mi mo r xi y) xo =
      ((normalization (E := E)) ^ 2 * ρ ^ (2 * (1 + Module.finrank ℝ E))) •
        ∫ x in Ici (0 : ℝ) ×ˢ (univ : Set (TangentialVariables E)),
          iteratedFDeriv ℝ m
            (fun y => normalizedIntegrand upper ρ α β mi mo r xi y x) xo
          ∂(volume.prod volume) := by
  let μ : Measure (ℝ × TangentialVariables E) :=
    (volume.prod volume).restrict (Ici (0 : ℝ) ×ˢ (univ : Set (TangentialVariables E)))
  have hf := contDiff_normalizedIntegrand_joint upper ρ α β mi mo r xi hα hβ hi ho hr
  have hK := isCompact_amplitudeCarrier hKα hKβ hKo hKi
  have hs := normalizedIntegrand_eq_zero_off_carrier upper ρ α β mi mo r xi
    hKα hKβ hKo hKi hsα hsβ hsr hsi
  have he : (fun y => if upper then upperFourierKernel α β mi mo r xi y
      else lowerFourierKernel α β mi mo r xi y) =
      ((normalization (E := E)) ^ 2 * ρ ^ (2 * (1 + Module.finrank ℝ E))) •
        (fun y => ∫ x, normalizedIntegrand upper ρ α β mi mo r xi y x ∂μ) := by
    funext y
    apply fourierKernel_eq_halfSpace upper hρ α β mi mo r xi y
      (contDiff_normalizedAmplitude upper ρ α β mi mo r hα hβ hi ho hr xi y)
    exact hK.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_normalizedAmplitude_subset upper ρ α β mi mo r xi y
        hKα hKβ hKo hKi hsα hsβ hsr hsi)
  rw [he, iteratedFDeriv_const_smul_apply
    ((contDiff_integral_commonCarrier (μ := μ) hf hK hs).contDiffAt.of_le (by simp)),
    iteratedFDeriv_integral_commonCarrier hf hK hs]

/-- The actual scalar output jet is an oscillatory half-space integral with the
same literal phase and the constructed differentiated amplitude. All directions
are retained, so mixed derivatives are covered as well
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_fourierKernel_apply_eq_halfSpace
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
      ((normalization (E := E)) ^ 2 * ρ ^ (2 * (1 + Module.finrank ℝ E))) •
        halfSpaceOscillatoryIntegral volume ρ (literalPhase upper xi xo)
          (outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v) := by
  rw [iteratedFDeriv_fourierKernel_eq_integral upper hρ α β mi mo r xi xo m
    hα hβ hi ho hr hKα hKβ hKo hKi hsα hsβ hsr hsi,
    smul_apply]
  have hj := (integrable_outputJet_commonCarrier
    (μ := volume.prod (volume : Measure (TangentialVariables E)))
    (contDiff_normalizedIntegrand_joint upper ρ α β mi mo r xi hα hβ hi ho hr)
    (isCompact_amplitudeCarrier hKα hKβ hKo hKi)
    (normalizedIntegrand_eq_zero_off_carrier upper ρ α β mi mo r xi
      hKα hKβ hKo hKi hsα hsβ hsr hsi) m xo).restrict
      (s := Ici (0 : ℝ) ×ˢ (univ : Set (TangentialVariables E)))
  rw [ContinuousMultilinearMap.integral_apply hj]
  simp only [halfSpaceOscillatoryIntegral, halfSpaceIntegral,
    oscillation_mul_outputDifferentiatedAmplitude]

end JanetCartan.FiniteChain.Retarded.KernelDecay
