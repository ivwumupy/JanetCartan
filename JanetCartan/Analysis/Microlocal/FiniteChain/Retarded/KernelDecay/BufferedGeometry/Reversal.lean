module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Basic
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.GradientGaps

/-!
# Literal upper phase and the reversed buffered image

The coordinate reversal needed by `exists_buffered_upper_geometry` retains the
upper input mask and backward complete image of `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exchange the two covectors, keeping the common base fixed
(`app:ch_regular:lem:finite-chain`). -/
def swapTangentialCovectors : TangentialVariables E ≃L[ℝ] TangentialVariables E :=
  (ContinuousLinearEquiv.refl ℝ (ℝ × E)).prodCongr
    (ContinuousLinearEquiv.prodComm ℝ (ℝ × E) (ℝ × E))

/-- The same exchange with the normal variable fixed
(`app:ch_regular:lem:finite-chain`). -/
def swapPackedCovectors : (ℝ × TangentialVariables E) ≃L[ℝ] (ℝ × TangentialVariables E) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr swapTangentialCovectors

/-- Phase reversal transports the tangential squared gradient without dropping
any input-base equation (`app:ch_regular:lem:finite-chain`). -/
theorem upper_tangential_gradientSquare_eq {ι : Type*} [Fintype ι]
    (e : ι → TangentialVariables E) (xi xo : ℝ × E)
    (d : ℝ) (z : TangentialVariables E) :
    Localization.phaseGradientSquare e (fun w => packedUpperPhase xi xo (d, w)) z =
      Localization.phaseGradientSquare (fun i => swapTangentialCovectors (e i))
        (fun w => packedPhase xo xi (d, w)) (swapTangentialCovectors z) := by
  have he : (fun w => packedUpperPhase xi xo (d, w)) =
      -(fun w => packedPhase xo xi (d, w)) ∘ swapTangentialCovectors := by
    funext w
    exact packedUpperPhase_eq_neg_swap xi xo w.1 w.2.1 w.2.2 d
  have hf : Differentiable ℝ (fun w => packedPhase xo xi (d, w)) :=
    ((contDiff_packedPhase xo xi).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  rw [he]
  simp only [Localization.phaseGradientSquare,
    fderiv_comp _ (hf _) swapTangentialCovectors.differentiableAt,
    fderiv_neg, ContinuousLinearEquiv.fderiv,
    ContinuousLinearMap.comp_apply, neg_apply, neg_sq]
  rfl

/-- The full squared gradient transforms by the same literal phase reversal
(`app:ch_regular:lem:finite-chain`). -/
theorem upper_gradientSquare_eq {ι : Type*} [Fintype ι]
    (e : ι → ℝ × TangentialVariables E) (xi xo : ℝ × E)
    (x : ℝ × TangentialVariables E) :
    Localization.phaseGradientSquare e (packedUpperPhase xi xo) x =
      Localization.phaseGradientSquare (fun i => swapPackedCovectors (e i))
        (packedPhase xo xi) (swapPackedCovectors x) := by
  have he : packedUpperPhase xi xo = -(packedPhase xo xi) ∘ swapPackedCovectors := by
    funext w
    exact packedUpperPhase_eq_neg_swap xi xo w.2.1 w.2.2.1 w.2.2.2 w.1
  have hf := (contDiff_packedPhase xo xi).differentiable (by simp)
  rw [he]
  simp only [Localization.phaseGradientSquare,
    fderiv_comp _ (hf _) swapPackedCovectors.differentiableAt,
    fderiv_neg, ContinuousLinearEquiv.fderiv,
    ContinuousLinearMap.comp_apply, neg_apply, neg_sq]
  rfl

/-- Backward buffered canonical images yield uniform squared-gradient gaps for
the literal upper phase (`app:ch_regular:lem:finite-chain`). The input support
and output rectangle are kept in their original upper orientation. -/
theorem exists_buffered_upper_gradient_gaps {X ι κ : Type*}
    [TopologicalSpace X] [Fintype ι] [Fintype κ] {K : Set X} (hK : IsCompact K)
    (eT : Module.Basis ι ℝ (TangentialVariables E))
    (eI : Module.Basis κ ℝ (ℝ × TangentialVariables E))
    {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage true R (tsupport mi) ⊆ interior {q | mo q = 1})
    (xi xo : X → ℝ × E) (x : X → ℝ × TangentialVariables E)
    (hi : Continuous xi) (ho : Continuous xo) (hx : Continuous x)
    (hd : ∀ p ∈ K, 0 ≤ (x p).1)
    (hin : ∀ p ∈ K, (xi p, (x p).2.2.2) ∈ tsupport mi)
    (hoR : ∀ p ∈ K, xo p ∈ R)
    (hout : ∀ p ∈ K, (xo p, (x p).2.2.1) ∈ tsupport (fun q => 1 - mo q)) :
    ∃ ε > 0, ∃ δT > 0, ∃ δI > 0, ∀ p ∈ K,
      (∀ d : ℝ, |d| ≤ ε → δT ≤ Localization.phaseGradientSquare eT
        (fun w => packedUpperPhase (xi p) (xo p) (d, w)) (x p).2) ∧
      δI ≤ Localization.phaseGradientSquare eI (packedUpperPhase (xi p) (xo p)) (x p) := by
  obtain ⟨δb, hb, hbgap⟩ := exists_adjoint_complementary_boundary_gap hK hmo hbuffer xi xo
    (fun p => (x p).2.1.1) (fun p => (x p).2.2.1.1) (fun p => (x p).2.2.2.1)
    (fun p => (x p).2.1.2) (fun p => (x p).2.2.1.2) (fun p => (x p).2.2.2.2)
    hi ho (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) hin hoR hout
  obtain ⟨δi, hiδ, higap⟩ := exists_adjoint_complementary_interior_gap hK hmo hbuffer xi xo
    (fun p => (x p).1) (fun p => (x p).2.1.1) (fun p => (x p).2.2.1.1)
    (fun p => (x p).2.2.2.1) (fun p => (x p).2.1.2)
    (fun p => (x p).2.2.1.2) (fun p => (x p).2.2.2.2)
    hi ho (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) hd hin hoR hout
  obtain ⟨δI, hδI, hI⟩ := exists_packedPhase_interior_gradient_gap hK
    (eI.map swapPackedCovectors.toLinearEquiv) xo xi (swapPackedCovectors ∘ x)
    ho hi (swapPackedCovectors.continuous.comp hx)
    (fun p hp => hiδ.trans_le (higap p hp))
  obtain ⟨δT, hδT, hT⟩ := exists_packedPhase_tangential_gradient_gap
    (hK.prod (isCompact_Icc (a := -δb / 2) (b := δb / 2)))
    (eT.map swapTangentialCovectors.toLinearEquiv)
    (fun p : X × ℝ => xo p.1) (fun p : X × ℝ => xi p.1)
    (fun p : X × ℝ => (p.2, swapTangentialCovectors (x p.1).2))
    (by fun_prop) (by fun_prop) (by fun_prop)
    (by
      intro p hp
      apply (half_pos hb).trans_le
      apply (hbgap p.1 hp.1).2 p.2
      exact abs_le.mpr ⟨by linarith [hp.2.1], hp.2.2⟩)
  refine ⟨δb / 2, half_pos hb, δT, hδT, δI, hδI, fun p hp => ⟨?_, ?_⟩⟩
  · intro d hd'
    rw [upper_tangential_gradientSquare_eq]
    exact hT (p, d) ⟨hp, by have hh := abs_le.mp hd'; constructor <;> linarith [hh.1, hh.2]⟩
  · rw [upper_gradientSquare_eq]
    exact hI p hp

end JanetCartan.FiniteChain.Retarded.KernelDecay
