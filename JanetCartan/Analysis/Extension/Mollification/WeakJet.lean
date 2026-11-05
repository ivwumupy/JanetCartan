module

public import JanetCartan.Analysis.Extension.Mollification.WeakDeriv

/-!
# Finite weak derivative jets

A concrete integration-by-parts description of the finite weak jets used in
Appendix B, `app:ch_regular_base:lem:ball-extension` of `paper.tex`. No
approximation or extension property is included in this definition.
-/

@[expose] public noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Appendix B, ball-extension density: `J` is the weak derivative jet of `f`
through order `m` on `U`. Order zero records the value; each subsequent order
is characterized by the usual weak first-derivative identity after currying. -/
def HasWeakJetOn (f : E → F) (J : (j : ℕ) → E → E [×j]→L[ℝ] F)
    (U : Set E) (m : ℕ) : Prop :=
  J 0 = iteratedFDeriv ℝ 0 f ∧ ∀ j < m,
    HasWeakFDerivOn μ (J j)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F) ∘ J (j + 1)) U

/-- Appendix B, ball-extension density: the classical derivatives of a Cᵐ
function form its weak jet on any domain. -/
theorem hasWeakJetOn_of_contDiff {f : E → F} {m : ℕ} (hf : ContDiff ℝ m f) (U : Set E) :
    HasWeakJetOn μ f (fun j ↦ iteratedFDeriv ℝ j f) U m := by
  refine ⟨rfl, fun j hj ↦ ?_⟩
  change HasWeakFDerivOn μ (iteratedFDeriv ℝ j f) (fderiv ℝ (iteratedFDeriv ℝ j f)) U
  exact hasWeakFDerivOn_of_contDiff μ (hf.iteratedFDeriv_right (by
    exact_mod_cast (show 1 + j ≤ m by omega))) U

end JanetCartan.Mollification
