module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Amplitudes

/-!
# Separating the output-symbol jet

The differentiated amplitude in `app:ch_regular:lem:finite-chain` factors
into the two weights, regularizer and input symbol, times the output jet of
one Fourier character and the complementary output symbol. This supplies the
quantitative derivative-grade step of `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open scoped ContDiff
attribute [local fun_prop] ContDiff.inner
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Output-independent factors of the literal normalized amplitude, preserving
its scalar and weight positions (`app:ch_regular:lem:finite-chain`). -/
def outputIndependentAmplitude (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ) (xi : ℝ × E) :
    (ℝ × TangentialVariables E) → ℂ :=
  normalizedAmplitude upper ρ α β mi (fun _ _ => 0) r xi 0

/-- The complementary output symbol is the sole output-dependent amplitude
factor (`app:ch_regular:lem:finite-chain`). -/
theorem normalizedAmplitude_eq_outputIndependent_mul (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) :
    normalizedAmplitude upper ρ α β mi mo r xi xo x =
      outputIndependentAmplitude upper ρ α β mi r xi x * (1 - mo xo (ρ • x.2.2.1)) := by
  cases upper <;> simp [outputIndependentAmplitude, normalizedAmplitude,
    lowerAmplitude, upperAmplitude] <;> ring

/-- Translation in the output adds precisely the output covector pairing,
for both literal orientations (`app:ch_regular:lem:finite-chain`). -/
theorem literalPhase_add_output (upper : Bool) (xi xo y : ℝ × E)
    (x : ℝ × TangentialVariables E) :
    literalPhase upper xi (xo + y) x = literalPhase upper xi xo x + pairing x.2.2.1 y := by
  cases upper <;> simp only [literalPhase, packedPhase, packedUpperPhase,
    phase, adjointPhase, Bool.false_eq_true, ↓reduceIte, Prod.fst_add, Prod.snd_add,
    pairing, inner_sub_left, inner_add_left, real_inner_comm x.2.2.1.2 y.2] <;> ring

/-- Exact factorization after output translation. The phase at the fixed
output is constant with respect to the new output increment
(`app:ch_regular:lem:finite-chain`). -/
theorem normalizedIntegrand_add_output (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo y : ℝ × E) (x : ℝ × TangentialVariables E) :
    normalizedIntegrand upper ρ α β mi mo r xi (xo + y) x =
      (Localization.phaseOscillation (ρ • literalPhase upper xi xo) x *
        outputIndependentAmplitude upper ρ α β mi r xi x) *
      (wave (ρ • x.2.2.1) y * (1 - mo (xo + y) (ρ • x.2.2.1))) := by
  have hp : pairing (ρ • x.2.2.1) y = ρ * pairing x.2.2.1 y := by
    simp only [pairing, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_left]
    ring
  simp only [normalizedIntegrand, normalizedAmplitude_eq_outputIndependent_mul,
    Localization.phaseOscillation, Pi.smul_apply, smul_eq_mul,
    literalPhase_add_output, wave, hp, mul_add, Complex.ofReal_add,
    add_mul, Complex.exp_add]
  ring

/-- Explicit all-order scalar output amplitude. The differentiated function
contains both the Fourier character and the output symbol. In particular no
output-symbol derivative has been discarded. This formula is the input to the
`ρ^m` grade calculation (`app:ch_regular:eq:chain-tail`). -/
theorem outputDifferentiatedAmplitude_eq_outputSymbolJet (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (x : ℝ × TangentialVariables E) :
    outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v x =
      outputIndependentAmplitude upper ρ α β mi r xi x *
        iteratedFDeriv ℝ m (fun y => wave (ρ • x.2.2.1) y *
          (1 - mo (xo + y) (ρ • x.2.2.1))) 0 v := by
  let g : (ℝ × E) → ℂ := fun y => wave (ρ • x.2.2.1) y *
    (1 - mo (xo + y) (ρ • x.2.2.1))
  have hmo : ContDiff ℝ ∞ (fun y => mo (xo + y) (ρ • x.2.2.1)) :=
    ho.comp (show ContDiff ℝ ∞ (fun y : ℝ × E => (xo + y, ρ • x.2.2.1)) from by fun_prop)
  have hcoe : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hg : ContDiff ℝ ∞ g := by unfold g wave pairing; fun_prop
  have he : (fun y => normalizedIntegrand upper ρ α β mi mo r xi (xo + y) x) =
      (Localization.phaseOscillation (ρ • literalPhase upper xi xo) x *
        outputIndependentAmplitude upper ρ α β mi r xi x) • g := by
    funext y
    exact normalizedIntegrand_add_output upper ρ α β mi mo r xi xo y x
  have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun y => normalizedIntegrand upper ρ α β mi mo r xi y x) m xo 0
  rw [add_zero, he, iteratedFDeriv_const_smul_apply (hg.contDiffAt.of_le (by simp))] at ht
  unfold outputDifferentiatedAmplitude
  rw [← ht, smul_apply, smul_eq_mul]
  simp only [Localization.phaseOscillation, Pi.neg_apply, Complex.ofReal_neg,
    neg_mul, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  rfl

/-- Extract the exact output-frequency factor `ρ^m` by rescaling the output
increment. The residual jet contains `mo (xo + ρ⁻¹ • y) (ρ • ξ)`, so output
symbol derivatives remain present with their correct inverse-frequency factors.
This is the algebraic frequency count in `app:ch_regular:eq:chain-tail`. -/
theorem outputDifferentiatedAmplitude_eq_scaled_outputSymbolJet (upper : Bool)
    {ρ : ℝ} (hρ : ρ ≠ 0) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (x : ℝ × TangentialVariables E) :
    outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v x =
      ρ ^ m • (outputIndependentAmplitude upper ρ α β mi r xi x *
        iteratedFDeriv ℝ m (fun y => wave x.2.2.1 y *
          (1 - mo (xo + ρ⁻¹ • y) (ρ • x.2.2.1))) 0 v) := by
  let g : (ℝ × E) → ℂ := fun y => wave x.2.2.1 y *
    (1 - mo (xo + ρ⁻¹ • y) (ρ • x.2.2.1))
  have hmo : ContDiff ℝ ∞ (fun y => mo (xo + ρ⁻¹ • y) (ρ • x.2.2.1)) :=
    ho.comp (show ContDiff ℝ ∞
      (fun y : ℝ × E => (xo + ρ⁻¹ • y, ρ • x.2.2.1)) from by fun_prop)
  have hcoe : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hg : ContDiff ℝ ∞ g := by unfold g wave pairing; fun_prop
  have he : (fun y => wave (ρ • x.2.2.1) y * (1 - mo (xo + y) (ρ • x.2.2.1))) =
      fun y => g (ρ • y) := by
    funext y
    have hp : pairing (ρ • x.2.2.1) y = pairing x.2.2.1 (ρ • y) := by
      simp only [pairing, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        real_inner_smul_left, inner_smul_right]
      ring
    simp only [g, wave, hp, inv_smul_smul₀ hρ]
  rw [outputDifferentiatedAmplitude_eq_outputSymbolJet upper ρ α β mi mo r xi xo m v ho x,
    he, iteratedFDeriv_comp_const_smul ρ (hg.of_le (by simp))]
  simp only [smul_zero, smul_apply]
  exact mul_smul_comm _ _ _

end JanetCartan.FiniteChain.Retarded.KernelDecay
