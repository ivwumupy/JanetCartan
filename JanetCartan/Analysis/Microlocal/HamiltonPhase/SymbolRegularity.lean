module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.LocalFlow
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Regularity of the Hamilton vector field

The vector field regularity required by the local flow is derived from the
scalar symbol via its actual differential and the Riesz isomorphism.
-/

open scoped ContDiff InnerProductSpace
@[expose] public noncomputable section

namespace JanetCartan.HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Differentiating a smooth symbol gives the smooth Hamilton field, with
exactly one derivative of loss (`app:lem:common-hamilton-phase`). -/
theorem HomogeneousSymbol.contDiffOn_vectorField (H : HomogeneousSymbol E) {n : WithTop ℕ∞}
    (hH : ContDiffOn ℝ (n + 1) H.h H.domain) :
    ContDiffOn ℝ n H.vectorField H.domain := by
  have hd : ContDiffOn ℝ n (fderiv ℝ H.h) H.domain :=
    hH.fderiv_of_isOpen H.isOpen_domain le_rfl
  have hx := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hd.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inl ℝ E E)))
  have hp := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hd.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inr ℝ E E)))
  apply (hp.prodMk hx.neg).congr
  intro z hz
  have hh := (H.hasFDerivAt_h z hz).fderiv
  have hx' : (fderiv ℝ H.h z).comp (ContinuousLinearMap.inl ℝ E E) =
      InnerProductSpace.toDual ℝ E (H.hx z) := by
    rw [hh]
    apply ContinuousLinearMap.ext
    intro v
    simp
  have hp' : (fderiv ℝ H.h z).comp (ContinuousLinearMap.inr ℝ E E) =
      InnerProductSpace.toDual ℝ E (H.hp z) := by
    rw [hh]
    apply ContinuousLinearMap.ext
    intro v
    simp
  simp [hx', hp', HomogeneousSymbol.vectorField]

end JanetCartan.HamiltonPhase
