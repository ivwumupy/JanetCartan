module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.AmplitudeGrades
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# Scalar amplitudes for output derivatives

The scalar output jets in `app:ch_regular:lem:finite-chain` are constructed
from the actual normalized integrand, including the output symbol's dependence
on the output base. Demodulation preserves each literal phase and weight order.
Quantitative grades are separate from these exact identities.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
attribute [local fun_prop] ContDiff.inner
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual joint normalized integrand, for the lower or literal upper
orientation (`app:ch_regular:lem:finite-chain`). -/
def normalizedIntegrand (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) : ℂ :=
  Localization.phaseOscillation (ρ • literalPhase upper xi xo) x *
    normalizedAmplitude upper ρ α β mi mo r xi xo x

/-- Scalar amplitude of the actual output jet in directions `v`. Both the
oscillation and the output symbol are differentiated, before removing the
original oscillation (`app:ch_regular:lem:finite-chain`). -/
def outputDifferentiatedAmplitude (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    (x : ℝ × TangentialVariables E) : ℂ :=
  Localization.phaseOscillation (-(ρ • literalPhase upper xi xo)) x *
    iteratedFDeriv ℝ m (fun y => normalizedIntegrand upper ρ α β mi mo r xi y x) xo v

/-- Joint smoothness in the output and integration variables, needed for
all-order dominated differentiation (`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_normalizedIntegrand_joint (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi : ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × TangentialVariables E) =>
      normalizedIntegrand upper ρ α β mi mo r xi p.1 p.2) := by
  have hi' : ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × TangentialVariables E) =>
      mi xi (ρ • p.2.2.2.2)) := hi.comp
      (show ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × TangentialVariables E) =>
        (xi, ρ • p.2.2.2.2)) from by fun_prop)
  have ho' : ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × TangentialVariables E) =>
      mo p.1 (ρ • p.2.2.2.1)) := ho.comp
      (show ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × TangentialVariables E) =>
        (p.1, ρ • p.2.2.2.1)) from by fun_prop)
  have hcoe : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  cases upper <;>
    simp only [normalizedIntegrand, normalizedAmplitude, literalPhase, lowerAmplitude,
      upperAmplitude, Localization.phaseOscillation, packedPhase, packedUpperPhase,
      phase, adjointPhase, Bool.false_eq_true, ↓reduceIte, Pi.smul_apply,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> fun_prop

/-- Output differentiation gives a smooth scalar amplitude in all integration
variables (`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_outputDifferentiatedAmplitude (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v) := by
  have hj := (contDiff_outputJet
    (contDiff_normalizedIntegrand_joint upper ρ α β mi mo r xi hα hβ hi ho hr) m).comp
      ((contDiff_const (c := xo)).prodMk contDiff_id)
  have hv := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℝ × E) ℂ v).contDiff.comp hj
  have hp := contDiff_literalPhase upper xi xo
  exact (Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp ((hp.const_smul ρ).neg)).mul contDiff_const)).mul hv

/-- Exact reconstruction of the differentiated integrand. This identity retains
the original literal phase, not a phase for a signed partner
(`app:ch_regular:lem:finite-chain`). -/
theorem oscillation_mul_outputDifferentiatedAmplitude (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    (x : ℝ × TangentialVariables E) :
    Localization.phaseOscillation (ρ • literalPhase upper xi xo) x *
        outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v x =
      iteratedFDeriv ℝ m (fun y => normalizedIntegrand upper ρ α β mi mo r xi y x) xo v := by
  simp only [outputDifferentiatedAmplitude, Localization.phaseOscillation, Pi.neg_apply,
    Complex.ofReal_neg, neg_mul, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, one_mul]

/-- The undifferentiated member is exactly the concrete normalized amplitude
(`app:ch_regular:lem:finite-chain`). -/
theorem outputDifferentiatedAmplitude_zero (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (v : Fin 0 → ℝ × E) :
    outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo 0 v =
      normalizedAmplitude upper ρ α β mi mo r xi xo := by
  funext x
  simp only [outputDifferentiatedAmplitude, iteratedFDeriv_zero_apply,
    normalizedIntegrand, Localization.phaseOscillation, Pi.neg_apply,
    Complex.ofReal_neg, neg_mul, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, one_mul]

/-- The primitive compact carrier works for the entire family of output
sections. No support is required of the complementary output symbol
(`app:ch_regular:lem:finite-chain`). -/
theorem normalizedIntegrand_eq_zero_off_carrier (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi : ℝ × E) {Kα Kβ Ko Ki : Set (ℝ × E)}
    (hKα : IsCompact Kα) (hKβ : IsCompact Kβ) (hKo : IsCompact Ko) (hKi : IsCompact Ki)
    (hα : tsupport α ⊆ Kα) (hβ : tsupport β ⊆ Kβ)
    (hr : tsupport (fun ξ => r (ρ • ξ)) ⊆ Ko)
    (hi : tsupport (fun ξ => mi xi (ρ • ξ)) ⊆ Ki)
    (y : ℝ × E) (x : ℝ × TangentialVariables E)
    (hx : x ∉ amplitudeCarrier Kα Kβ Ko Ki) :
    normalizedIntegrand upper ρ α β mi mo r xi y x = 0 := by
  have hs := tsupport_normalizedAmplitude_subset upper ρ α β mi mo r xi y
    hKα hKβ hKo hKi hα hβ hr hi
  have ha := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  exact mul_eq_zero_of_right _ ha

/-- All scalar output derivatives share the same compact carrier, independently
of output order (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem tsupport_outputDifferentiatedAmplitude_subset (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    {Kα Kβ Ko Ki : Set (ℝ × E)}
    (hKα : IsCompact Kα) (hKβ : IsCompact Kβ) (hKo : IsCompact Ko) (hKi : IsCompact Ki)
    (hα : tsupport α ⊆ Kα) (hβ : tsupport β ⊆ Kβ)
    (hr : tsupport (fun ξ => r (ρ • ξ)) ⊆ Ko)
    (hi : tsupport (fun ξ => mi xi (ρ • ξ)) ⊆ Ki) :
    tsupport (outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v) ⊆
      amplitudeCarrier Kα Kβ Ko Ki := by
  apply closure_minimal _ (isCompact_amplitudeCarrier hKα hKβ hKo hKi).isClosed
  intro x hx
  by_contra h
  have hz := outputJet_eq_zero_off_carrier
    (f := fun p => normalizedIntegrand upper ρ α β mi mo r xi p.1 p.2)
    (normalizedIntegrand_eq_zero_off_carrier upper ρ α β mi mo r xi
      hKα hKβ hKo hKi hα hβ hr hi) m xo h
  apply hx
  simp [outputDifferentiatedAmplitude, hz]

end JanetCartan.FiniteChain.Retarded.KernelDecay
