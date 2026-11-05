module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Adjugate
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of the selected nullvectors

The fixed-minor construction in `app:ch_waves:thm:leading` is polynomial in the
matrix entries. In particular it preserves joint regularity in spatial and
carrier parameters without choosing a new nullvector at each point.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.NullTransport

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι] {s : Set E} {m : ℕ∞ω}

/-- Each fixed adjugate entry is smooth in the matrix entries, as used in
`app:ch_waves:thm:leading`. -/
theorem contDiffOn_adjugate_entry {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiffOn ℝ m (fun x ↦ A x i j) s) (r c : ι) :
    ContDiffOn ℝ m (fun x ↦ (A x).adjugate r c) s := by
  have hu (i j : ι) :
      ContDiffOn ℝ m (fun x ↦ (A x).updateRow c (Pi.single r 1) i j) s := by
    by_cases hi : i = c
    · subst i
      simp only [Matrix.updateRow_self]
      exact contDiffOn_const
    · simpa only [Matrix.updateRow_ne hi] using hA i j
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i _
  exact hu (σ i) i

/-- The fixed right nullvector varies smoothly in all parameters
(`app:ch_waves:thm:leading`). -/
theorem contDiffOn_rightNullvector {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiffOn ℝ m (fun x ↦ A x i j) s) (c : ι) :
    ContDiffOn ℝ m (fun x ↦ rightNullvector (A x) c) s := by
  apply contDiffOn_pi.mpr
  intro i
  exact contDiffOn_adjugate_entry hA i c

/-- The fixed left nullvector varies smoothly in all parameters
(`app:ch_waves:thm:leading`). -/
theorem contDiffOn_leftNullvector {A : E → Matrix ι ι ℝ}
    (hA : ∀ i j, ContDiffOn ℝ m (fun x ↦ A x i j) s) (r : ι) :
    ContDiffOn ℝ m (fun x ↦ leftNullvector (A x) r) s := by
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_adjugate_entry hA r j

end JanetCartan.NullTransport
