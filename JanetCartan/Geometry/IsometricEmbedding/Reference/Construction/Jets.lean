module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Bending
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Center second derivatives in Proposition `app:ch_seed:prop:seed-analytic`. -/

@[expose] public noncomputable section

namespace JanetCartan.ReferenceConstruction

variable {D E G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The second-order chain rule used in Proposition `app:ch_seed:prop:seed-analytic`. -/
theorem secondFDeriv_comp_apply {f : D → E} {g : E → G}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x u w : D) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x u w =
      fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x u w) +
      fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x u) (fderiv ℝ f x w) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have he : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd₂ : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have he₂ : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable (by norm_num)
  have hEq : fderiv ℝ (g ∘ f) = fun y ↦ (fderiv ℝ g (f y)).comp (fderiv ℝ f y) :=
    funext (fun y ↦ fderiv_comp y (he _) (hd _))
  have hc : DifferentiableAt ℝ (fun y ↦ fderiv ℝ g (f y)) x := (he₂ _).comp x (hd x)
  rw [hEq, fderiv_clm_comp hc (hd₂ x)]
  rw [show (fun y ↦ fderiv ℝ g (f y)) = (fderiv ℝ g) ∘ f from rfl,
    fderiv_comp x (he₂ _) (hd x)]
  rfl

/-- Proposition `app:ch_seed:prop:seed-analytic`: a bending preserves the old center
second derivatives and adds a rank-one form in the new normal direction. -/
theorem secondFDeriv_circularBending_comp_zero {f : D → E}
    (hf : ContDiff ℝ 2 f) (hzero : f 0 = 0) (v : E) {n : ℝ} (hn : n ≠ 0)
    (u w : D) :
    fderiv ℝ (fderiv ℝ (circularBending v n ∘ f)) 0 u w =
      bendingInclusion (fderiv ℝ (fderiv ℝ f) 0 u w) +
        (n * inner ℝ v (fderiv ℝ f 0 u) * inner ℝ v (fderiv ℝ f 0 w)) •
          bendingNormal := by
  rw [secondFDeriv_comp_apply hf (circularBending_contDiff v n 2), hzero,
    circularBending_fderiv_zero v hn, circularBending_secondFDeriv_zero_apply v hn]

/-- Proposition `app:ch_seed:prop:seed-analytic`: a linear change of ambient
coordinates transports the second derivative. -/
theorem secondFDeriv_linear_comp_apply {f : D → E}
    (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] G) (x u w : D) :
    fderiv ℝ (fderiv ℝ (L ∘ f)) x u w = L (fderiv ℝ (fderiv ℝ f) x u w) := by
  rw [secondFDeriv_comp_apply hf L.contDiff]
  have hL : fderiv ℝ (⇑L : E → G) = fun _ ↦ L := funext (fun _ ↦ L.fderiv)
  rw [hL]
  simp

end JanetCartan.ReferenceConstruction
