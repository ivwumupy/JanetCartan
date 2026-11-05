module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Basic

/-!
# Smoothness of the concrete retarded amplitudes

The jump is kept in the half-space measure, so all differentiations of the
amplitudes in `app:ch_regular:lem:finite-chain` concern smooth functions.
Both covectors and the common base remain genuine integration variables.
-/

@[expose] public noncomputable section
open scoped ContDiff
attribute [local fun_prop] ContDiff.inner
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Smoothness of the literal upper phase (`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_packedUpperPhase (xi xo : ℝ × E) :
    ContDiff ℝ ∞ (packedUpperPhase xi xo) := by
  unfold packedUpperPhase adjointPhase
  fun_prop

/-- The concrete lower amplitude is smooth before half-space restriction
(`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_lowerAmplitude (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ r) (xi xo : ℝ × E) :
    ContDiff ℝ ∞ (lowerAmplitude α β mi mo r xi xo) := by
  have hi' : ContDiff ℝ ∞ (mi xi) := hi.comp (contDiff_const.prodMk contDiff_id)
  have ho' : ContDiff ℝ ∞ (mo xo) := ho.comp (contDiff_const.prodMk contDiff_id)
  have ha : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E =>
      (α (x.2.1.1 + x.1, x.2.1.2) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hα).comp (by fun_prop)
  have hb : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E => (β x.2.1 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hβ).comp (by fun_prop)
  have hout : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E =>
      r x.2.2.1 * (1 - mo xo x.2.2.1)) := by fun_prop
  exact (((contDiff_const.mul ha).mul hb).mul hout).mul
    (hi'.comp (by fun_prop))

/-- The same smoothness statement for the exchanged adjoint weights and
the literal scalar `-i` (`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_upperAmplitude (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ r) (xi xo : ℝ × E) :
    ContDiff ℝ ∞ (upperAmplitude α β mi mo r xi xo) := by
  have hi' : ContDiff ℝ ∞ (mi xi) := hi.comp (contDiff_const.prodMk contDiff_id)
  have ho' : ContDiff ℝ ∞ (mo xo) := ho.comp (contDiff_const.prodMk contDiff_id)
  have ha : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E =>
      (α (x.2.1.1 + x.1, x.2.1.2) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hα).comp (by fun_prop)
  have hb : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E => (β x.2.1 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hβ).comp (by fun_prop)
  have hout : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E =>
      r x.2.2.1 * (1 - mo xo x.2.2.1)) := by fun_prop
  exact (((contDiff_const.mul hb).mul ha).mul hout).mul
    (hi'.comp (by fun_prop))

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
