module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Interchanging parameter and spatial derivatives

Mixed derivatives used in `app:ch_osc:setup:osc-normal` and
`app:ch_osc:prop:osc-normal`. The family is smooth on an open product;
therefore the ordinary parameter derivative also applies at the manuscript's
parameter endpoints. The spatial order is arbitrary.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.NormalComparison

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- First spatial and parameter derivatives commute on an open product.
This is the second-derivative symmetry step for `app:ch_osc:setup:osc-normal`. -/
theorem fderiv_deriv_parameter {f : ℝ × E → V} {I : Set ℝ} {U : Set E}
    (hI : IsOpen I) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (I ×ˢ U))
    {t : ℝ} (ht : t ∈ I) {x : E} (hx : x ∈ U) :
    fderiv ℝ (fun y ↦ deriv (fun s ↦ f (s, y)) t) x =
      deriv (fun s ↦ fderiv ℝ (fun y ↦ f (s, y)) x) t := by
  have h (s) (hs : s ∈ I) (y) (hy : y ∈ U) : ContDiffAt ℝ ∞ f (s, y) :=
    hf.contDiffAt ((hI.prod hU).mem_nhds ⟨hs, hy⟩)
  have heq₁ : (fun y ↦ deriv (fun s ↦ f (s, y)) t) =ᶠ[𝓝 x]
      (fun y ↦ fderiv ℝ f (t, y) (1, 0)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (((h t ht y hy).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))).deriv
  have heq₂ : (fun s ↦ fderiv ℝ (fun y ↦ f (s, y)) x) =ᶠ[𝓝 t]
      (fun s ↦ (fderiv ℝ f (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (((h s hs x hx).differentiableAt (by simp)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right s x)).fderiv
  have hd := ((h t ht x hx).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [heq₁.fderiv_eq, heq₂.deriv_eq]
  have hleft := ((ContinuousLinearMap.apply ℝ V (1, (0 : E))).hasFDerivAt.comp x
    (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x))).fderiv
  have hright := (((ContinuousLinearMap.compL ℝ E (ℝ × E) V).flip
      (ContinuousLinearMap.inr ℝ ℝ E)).hasFDerivAt.comp_hasDerivAt t
      (hd.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)))).deriv
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, id_eq] at hleft hright
  rw [hleft, hright]
  ext v
  exact (h t ht x hx).isSymmSndFDerivAt (by simp) (0, v) (1, 0)

/-- All finite spatial jets remain jointly smooth in the parameter and position
(`app:ch_osc:setup:osc-normal`). -/
theorem contDiffAt_spatial_iteratedFDeriv {f : ℝ × E → V} {q : ℝ × E}
    (hf : ContDiffAt ℝ ∞ f q) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E ↦ iteratedFDeriv ℝ k (fun y ↦ f (p.1, y)) p.2) q := by
  induction k with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Prod.mk.eta] using
      (continuousMultilinearCurryFin0 ℝ E V).symm.contDiff.contDiffAt.comp q hf
  | succ k ih =>
    have hh : ContDiffAt ℝ ∞
        (fun w : (ℝ × E) × E ↦ iteratedFDeriv ℝ k (fun y ↦ f (w.1.1, y)) w.2)
        (q, q.2) := ih.comp (q, q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd := hh.fderiv
      (f := fun p y ↦ iteratedFDeriv ℝ k (fun z ↦ f (p.1, z)) y)
      (x₀ := q) contDiffAt_snd (m := ∞) (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) V).symm.contDiff.contDiffAt.comp
        q hd

/-- The actual parameter derivative is jointly smooth on the open extension
(`app:ch_osc:setup:osc-normal`). -/
theorem contDiffAt_parameter_deriv {f : ℝ × E → V} {q : ℝ × E}
    (hf : ContDiffAt ℝ ∞ f q) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E ↦ deriv (fun s ↦ f (s, p.2)) p.1) q := by
  have hh : ContDiffAt ℝ ∞ (fun w : (ℝ × E) × ℝ ↦ f (w.2, w.1.2)) (q, q.1) :=
    hf.comp (q, q.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact (hh.fderiv contDiffAt_fst (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem deriv_comp_equiv {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V ≃L[ℝ] W) (g : ℝ → V) (t : ℝ) :
    deriv (fun s ↦ L (g s)) t = L (deriv g t) := by
  have h := congrArg (fun A : ℝ →L[ℝ] W ↦ A 1) (L.comp_fderiv (f := g) (x := t))
  simpa only [deriv, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe] using h

/-- Spatial jets of the actual parameter derivative equal parameter derivatives
of the original spatial jets, at every finite order
(`app:ch_osc:setup:osc-normal`). -/
theorem iteratedFDeriv_deriv_parameter {f : ℝ × E → V} {I : Set ℝ} {U : Set E}
    (hI : IsOpen I) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (I ×ˢ U))
    {t : ℝ} (ht : t ∈ I) {x : E} (hx : x ∈ U) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y ↦ deriv (fun s ↦ f (s, y)) t) x =
      deriv (fun s ↦ iteratedFDeriv ℝ k (fun y ↦ f (s, y)) x) t := by
  induction k generalizing x with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
    exact (deriv_comp_equiv (continuousMultilinearCurryFin0 ℝ E V).symm.toContinuousLinearEquiv
      (fun s ↦ f (s, x)) t).symm
  | succ k ih =>
    have heq : (iteratedFDeriv ℝ k (fun y ↦ deriv (fun s ↦ f (s, y)) t)) =ᶠ[𝓝 x]
        (fun y ↦ deriv (fun s ↦ iteratedFDeriv ℝ k (fun z ↦ f (s, z)) y) t) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hy
    have hj : ContDiffOn ℝ ∞
        (fun p : ℝ × E ↦ iteratedFDeriv ℝ k (fun y ↦ f (p.1, y)) p.2) (I ×ˢ U) := by
      intro q hq
      exact (contDiffAt_spatial_iteratedFDeriv
        (hf.contDiffAt ((hI.prod hU).mem_nhds hq)) k).contDiffWithinAt
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def]
    rw [heq.fderiv_eq, fderiv_deriv_parameter hI hU hj ht hx]
    exact (deriv_comp_equiv
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) V).symm.toContinuousLinearEquiv
      (fun s ↦ fderiv ℝ (iteratedFDeriv ℝ k (fun y ↦ f (s, y))) x) t).symm

end JanetCartan.NormalComparison
