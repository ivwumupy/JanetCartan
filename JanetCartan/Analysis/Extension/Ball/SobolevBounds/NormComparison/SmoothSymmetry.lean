module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Data.List.FinRange

/-!
# Permutation symmetry of smooth Fréchet jets

The multiindex derivative norm in `app:ch_regular_base:lem:ball-extension` and
`app:ch_regular_base:eq:ball-extension-sobolev` uses the independence of repeated
partial derivatives from their order. We prove the corresponding symmetry of
all iterated Fréchet derivatives on open real domains. The argument uses
Schwarz's theorem for adjacent directional derivatives, then list permutations.

The result holds for arbitrary real normed spaces, so in particular includes
Euclidean domains of dimensions zero and one. Only smoothness is required.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.BallExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Repeated directional derivatives, with the head acting last, used to prove
jet symmetry for `app:ch_regular_base:lem:ball-extension`. -/
private def smoothDirectionalDerivList : List E → (E → F) → E → F
  | [], f => f
  | v :: vs, f => fun x ↦ fderiv ℝ (smoothDirectionalDerivList vs f) x v

/-- The intermediate directional derivatives in the proof of
`app:ch_regular_base:eq:ball-extension-sobolev` remain smooth on the open set. -/
private theorem contDiffOn_smoothDirectionalDerivList
    {s : Set E} (hs : IsOpen s) {f : E → F} (hf : ContDiffOn ℝ ∞ f s)
    (vs : List E) : ContDiffOn ℝ ∞ (smoothDirectionalDerivList vs f) s := by
  induction vs with
  | nil => exact hf
  | cons v vs ih =>
    exact (ih.fderiv_of_isOpen hs (m := ∞) (by simp)).clm_apply contDiffOn_const

/-- Schwarz's theorem and adjacent swaps give order independence of the
repeated derivatives used in `app:ch_regular_base:lem:ball-extension`. -/
private theorem smoothDirectionalDerivList_perm
    {s : Set E} (hs : IsOpen s) {f : E → F} (hf : ContDiffOn ℝ ∞ f s)
    {vs ws : List E} (h : vs.Perm ws) :
    EqOn (smoothDirectionalDerivList vs f) (smoothDirectionalDerivList ws f) s := by
  induction h with
  | nil => intro _ _; rfl
  | cons v h ih =>
    intro x hx
    simp only [smoothDirectionalDerivList]
    rw [← fderivWithin_of_isOpen hs hx, ← fderivWithin_of_isOpen hs hx,
      fderivWithin_congr' ih hx]
  | swap v w vs =>
    intro x hx
    have hg := (contDiffOn_smoothDirectionalDerivList hs hf vs).contDiffAt (hs.mem_nhds hx)
    have hd := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    simp only [smoothDirectionalDerivList]
    rw [fderiv_clm_apply hd (differentiableAt_const _),
      fderiv_clm_apply hd (differentiableAt_const _)]
    simpa using (hg.isSymmSndFDerivAt (by simp)) w v
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Identify successive directional derivatives with evaluation of the Fréchet
jet in the derivative norm of `app:ch_regular_base:lem:ball-extension`. -/
private theorem smoothDirectionalDerivList_ofFn
    {s : Set E} (hs : IsOpen s) {f : E → F} (hf : ContDiffOn ℝ ∞ f s)
    (j : ℕ) (v : Fin j → E) :
    EqOn (smoothDirectionalDerivList (List.ofFn v) f)
      (fun x ↦ iteratedFDerivWithin ℝ j f s x v) s := by
  induction j with
  | zero =>
    intro x _
    simp [smoothDirectionalDerivList, iteratedFDerivWithin_zero_apply]
  | succ j ih =>
    intro x hx
    rw [List.ofFn_succ]
    change fderiv ℝ (smoothDirectionalDerivList (List.ofFn (Fin.tail v)) f) x (v 0) = _
    rw [← fderivWithin_of_isOpen hs hx, fderivWithin_congr' (ih (Fin.tail v)) hx,
      fderivWithin_continuousMultilinear_apply_const_apply (hs.uniqueDiffOn x hx)
        (hf.differentiableOn_iteratedFDerivWithin (m := j)
          (by exact_mod_cast ENat.natCast_lt_top j) hs.uniqueDiffOn x hx)]
    rfl

/-- Every Fréchet jet of a smooth function on an open real domain is symmetric.
This supplies the order independence of derivatives in the Sobolev norm of
`app:ch_regular_base:lem:ball-extension` and its estimate
`app:ch_regular_base:eq:ball-extension-sobolev`. In particular it applies to
real-valued functions on `EuclideanSpace ℝ (Fin n)` for every `n`, including
zero and one, without any analyticity assumption. -/
theorem iteratedFDerivWithin_comp_perm_of_contDiffOn
    {s : Set E} (hs : IsOpen s) {f : E → F} (hf : ContDiffOn ℝ ∞ f s)
    {x : E} (hx : x ∈ s) (j : ℕ) (v : Fin j → E) (σ : Equiv.Perm (Fin j)) :
    iteratedFDerivWithin ℝ j f s x (v ∘ σ) = iteratedFDerivWithin ℝ j f s x v := by
  exact (smoothDirectionalDerivList_ofFn hs hf j (v ∘ σ) hx).symm.trans
    ((smoothDirectionalDerivList_perm hs hf (σ.ofFn_comp_perm v) hx).trans
      (smoothDirectionalDerivList_ofFn hs hf j v hx))

end JanetCartan.BallExtension
