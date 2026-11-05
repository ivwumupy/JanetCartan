module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.Graph
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Phase
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Eikonal graphs are tangent to the Hamilton field

The differential step of `app:ch_regular:thm:no-return`, followed by uniqueness
on the entire physical segment in either orientation. The eikonal identity is
supplied by the constructed Hamilton phase; tangency is derived here using
symmetry of its actual Hessian. The producer of the local phases is
`HamiltonPhase.ProjectionChart.eikonal`.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology NNReal
open InnerProductSpace Filter Set

namespace JanetCartan.ProtectedFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Hessian symmetry in the gradient representation used in the proof of
`app:ch_regular:thm:no-return`. -/
theorem gradient_derivative_symmetric {ψ : E → ℝ} {x : E} {dg : E →L[ℝ] E}
    (hψ : ContDiffAt ℝ 2 ψ x) (hg : HasFDerivAt (gradient ψ) dg x) (v w : E) :
    ⟪dg v, w⟫_ℝ = ⟪dg w, v⟫_ℝ := by
  have hd := ((toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).comp x hg
  have hd' : HasFDerivAt (fderiv ℝ ψ)
      ((toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.comp dg) x := by
    change HasFDerivAt ((toDual ℝ E) ∘ gradient ψ) _ x at hd
    simpa only [toDual_comp_gradient] using hd
  have hs := (hψ.isSymmSndFDerivAt (by simp)).eq v w
  rw [hd'.fderiv] at hs
  exact hs

/-- Differentiating the eikonal identity gives Hamiltonian tangency, as in
`app:ch_regular:thm:no-return`. Neither tangency nor graph invariance is an input. -/
theorem hamilton_tangent_of_eikonal (H : JanetCartan.HamiltonPhase.HomogeneousSymbol E)
    {ψ : E → ℝ} {x : E} {dg : E →L[ℝ] E} {e : ℝ}
    (hψ : ContDiffAt ℝ 2 ψ x) (hg : HasFDerivAt (gradient ψ) dg x)
    (hmem : (x, gradient ψ x) ∈ H.domain)
    (he : (fun y ↦ H.h (y, gradient ψ y)) =ᶠ[𝓝 x] (fun _ ↦ e)) :
    -H.hx (x, gradient ψ x) = dg (H.hp (x, gradient ψ x)) := by
  have hd := (H.hasFDerivAt_h _ hmem).comp x ((hasFDerivAt_id x).prodMk hg)
  have hz := (hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_const e x)
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hz
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, JanetCartan.HamiltonPhase.hamiltonDifferential_apply,
    zero_apply] at hv
  have hs := gradient_derivative_symmetric hψ hg (H.hp (x, gradient ψ x)) v
  rw [inner_neg_left, hs, real_inner_comm (H.hp (x, gradient ψ x)) (dg v)]
  linarith

/-- A smooth eikonal graph contains the entire Hamilton segment starting on
it, including segments traversed backwards (`app:ch_regular:thm:no-return`).
The domain condition concerns every intermediate time. The remaining
Lipschitz input is a bound on the actual vector field, not graph invariance. -/
theorem characteristic_stays_on_eikonal_graph
    (H : HamiltonPhase.HomogeneousSymbol E)
    {W D : Set E} {ψ : E → ℝ} {dg : E → E →L[ℝ] E} {L : ℝ≥0}
    {x p : ℝ → E} {a b t₀ e : ℝ}
    (hW : IsOpen W) (ht₀ : t₀ ∈ Icc a b)
    (hψ : ∀ y ∈ W, ContDiffAt ℝ 2 ψ y)
    (hgraph : ∀ y ∈ W, HasFDerivAt (gradient ψ) (dg y) y)
    (hmem : ∀ y ∈ W, (y, gradient ψ y) ∈ H.domain)
    (he : ∀ y ∈ W, H.h (y, gradient ψ y) = e)
    (hlip : ∀ y ∈ W, LipschitzOnWith L
      (fun z ↦ -H.hx (y, z) - dg y (H.hp (y, z))) D)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (H.hp (x t, p t)) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (-H.hx (x t, p t)) t)
    (hxW : ∀ t ∈ Icc a b, x t ∈ W)
    (hpD : ∀ t ∈ Icc a b, p t ∈ D)
    (hgD : ∀ y ∈ W, gradient ψ y ∈ D)
    (hinit : p t₀ = gradient ψ (x t₀)) :
    ∀ t ∈ Icc a b, p t = gradient ψ (x t) := by
  apply characteristic_stays_on_graph ht₀ hgraph _ hlip hx hp hxW hpD hgD hinit
  intro y hy
  exact hamilton_tangent_of_eikonal H (hψ y hy) (hgraph y hy) (hmem y hy)
    (eventuallyEq_of_mem (hW.mem_nhds hy) (fun z hz ↦ he z hz))

end JanetCartan.ProtectedFlow
