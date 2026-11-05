module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Compatible graded scales

The abstract scale used in the bootstrap in
`app:ch_regular:thm:exact-correction`. Each level is an actual subspace of one
base space. Its seminorm dominates the base norm, hence is a norm. Completeness
of the higher levels is unnecessary for the finite regularity bootstrap.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nested normed subspaces for `app:ch_regular:eq:one-gain-tame`.
The normalization assumes monotone scale norms, as used in the manuscript. -/
structure GradedScale where
  level : ℕ → Submodule ℝ E
  level_zero : level 0 = ⊤
  antitone_level : Antitone level
  seminorm : (s : ℕ) → Seminorm ℝ (level s)
  seminorm_zero : ∀ x : level 0, seminorm 0 x = ‖(x : E)‖
  monotone_seminorm : ∀ {s t : ℕ} (h : s ≤ t) (x : level t),
    seminorm s ⟨x, antitone_level h x.property⟩ ≤ seminorm t x

namespace GradedScale

variable {E} (G : GradedScale E)

/-- The norm at order `s`, extended by zero off its domain solely for notation.
Every analytic assertion below supplies membership in the relevant level. -/
def gradeNorm (s : ℕ) (x : E) : ℝ := by
  classical
  exact if h : x ∈ G.level s then G.seminorm s ⟨x, h⟩ else 0

theorem gradeNorm_eq {s : ℕ} {x : E} (hx : x ∈ G.level s) :
    G.gradeNorm s x = G.seminorm s ⟨x, hx⟩ := by
  simp [gradeNorm, hx]

theorem mem_zero (x : E) : x ∈ G.level 0 := by
  rw [G.level_zero]
  trivial

@[simp] theorem gradeNorm_zero (x : E) : G.gradeNorm 0 x = ‖x‖ := by
  rw [G.gradeNorm_eq (G.mem_zero x), G.seminorm_zero]

theorem gradeNorm_nonneg (s : ℕ) (x : E) : 0 ≤ G.gradeNorm s x := by
  unfold gradeNorm
  split
  · exact apply_nonneg _ _
  · exact le_rfl

theorem gradeNorm_mono {s t : ℕ} (hst : s ≤ t) {x : E} (hx : x ∈ G.level t) :
    G.gradeNorm s x ≤ G.gradeNorm t x := by
  rw [G.gradeNorm_eq hx, G.gradeNorm_eq (G.antitone_level hst hx)]
  exact G.monotone_seminorm hst ⟨x, hx⟩

theorem norm_le_gradeNorm {s : ℕ} {x : E} (hx : x ∈ G.level s) :
    ‖x‖ ≤ G.gradeNorm s x := by
  simpa using G.gradeNorm_mono (Nat.zero_le s) hx

theorem gradeNorm_sub_le {s : ℕ} {x y : E}
    (hx : x ∈ G.level s) (hy : y ∈ G.level s) :
    G.gradeNorm s (x - y) ≤ G.gradeNorm s x + G.gradeNorm s y := by
  rw [G.gradeNorm_eq ((G.level s).sub_mem hx hy), G.gradeNorm_eq hx, G.gradeNorm_eq hy]
  exact map_sub_le_add (G.seminorm s) ⟨x, hx⟩ ⟨y, hy⟩

/-- Smoothness in the abstract scale means membership at every order
(`app:ch_regular:thm:exact-correction`). Identifying this with classical smoothness
in a concrete Sobolev scale is a separate input. -/
def IsSmooth (x : E) : Prop := ∀ s, x ∈ G.level s

end GradedScale
end JanetCartan
