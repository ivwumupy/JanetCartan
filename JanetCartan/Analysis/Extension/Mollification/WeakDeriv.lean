module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Weak derivatives and convolution

The integration-by-parts formulation of weak derivatives used in the density
paragraph of Appendix B, `app:ch_regular_base:lem:ball-extension` of `paper.tex`.
The derivative is a locally integrable field of continuous linear maps. Tests
are smooth scalar functions with compact support inside the specified domain.
-/

@[expose] public noncomputable section

open MeasureTheory Set Function ContinuousLinearMap
open scoped Topology ContDiff Convolution

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Appendix B, ball-extension density: `f'` is the weak Fréchet derivative of
`f` on `U`. The defining identity is tested against all smooth compactly
supported scalar functions and all constant directions. -/
def HasWeakFDerivOn (f : E → F) (f' : E → E →L[ℝ] F) (U : Set E) : Prop :=
  LocallyIntegrableOn f U μ ∧ LocallyIntegrableOn f' U μ ∧
    ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : E, (∫ x, ψ x • f' x v ∂μ) = - ∫ x, fderiv ℝ ψ x v • f x ∂μ

/-- Appendix B, ball-extension density: classical C¹ derivatives satisfy the
weak integration-by-parts identity on every domain. -/
theorem hasWeakFDerivOn_of_contDiff {f : E → F} (hf : ContDiff ℝ 1 f) (U : Set E) :
    HasWeakFDerivOn μ f (fderiv ℝ f) U := by
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn U,
    (hf.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn U, ?_⟩
  intro ψ hψ hc _ v
  have hψd : Continuous (fun x ↦ fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x ↦ fderiv ℝ ψ x v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ ↦ L v) rfl
  have hfd : LocallyIntegrable (fun x ↦ fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).locallyIntegrable
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (hf.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψd hψdc)
    (hfd.integrable_smul_left_of_hasCompactSupport hψ.continuous hc)
    (hf.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hc)
    (fun x _ ↦ hψ.differentiable (by simp) x)
    (fun x _ ↦ hf.differentiable one_ne_zero x)

/-- Appendix B, ball-extension density: convolution converts a weak derivative
into a classical derivative wherever the translated kernel is supported inside
the domain. Global local integrability is only used to define both convolutions. -/
theorem HasWeakFDerivOn.fderiv_convolution {f : E → F} {f' : E → E →L[ℝ] F}
    {U : Set E} (hw : HasWeakFDerivOn μ f f' U)
    (hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ)
    {κ : E → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (x : E) (hx : tsupport (fun y ↦ κ (x - y)) ⊆ U) :
    fderiv ℝ (κ ⋆[lsmul ℝ ℝ, μ] f) x = (κ ⋆[lsmul ℝ ℝ, μ] f') x := by
  let ψ : E → ℝ := fun y ↦ κ (x - y)
  have hψ : ContDiff ℝ ∞ ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hψd : ∀ y v, fderiv ℝ ψ y v = -(fderiv ℝ κ (x - y) v) := by
    intro y v
    have hd := ((hκ.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)).fderiv
    simpa [ψ, Function.comp_def] using congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hd
  rw [(hc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) (hκ.of_le (by simp)) hf x).fderiv]
  ext v
  have hi := (hc.fderiv ℝ).convolutionExists_left
    (L := (lsmul ℝ ℝ (E := F)).precompL E)
    (hκ.continuous_fderiv (by simp)) hf x
  have hi' := hc.convolutionExists_left (L := lsmul ℝ ℝ (E := E →L[ℝ] F))
    hκ.continuous hf' x
  rw [convolution_def, integral_apply hi, convolution_def, integral_apply hi']
  simp only [precompL_apply, lsmul_apply, smul_apply]
  rw [← integral_sub_left_eq_self (fun y ↦ fderiv ℝ κ y v • f (x - y)) μ x,
    ← integral_sub_left_eq_self (fun y ↦ κ y • f' (x - y) v) μ x]
  simp only [sub_sub_cancel]
  have hwψ := hw.2.2 ψ hψ hψc hx v
  simp only [hψd, neg_smul, integral_neg, neg_neg] at hwψ
  exact hwψ.symm

end JanetCartan.Mollification
