module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Phase
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

/-!
# Compact off-relation gaps for the retarded phase

The compactness step of `app:ch_regular:lem:finite-chain`. The defects below are
sums of the norms of the actual partial derivatives proved in `Phase`. The
hypotheses exclude the full relation, including the base variables. The boundary gap persists in a quantitative collar. Construction of smooth
proof masks is separate.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Sum of the tangential derivative norms in
`app:ch_regular:lem:finite-chain`. This remains defined at the boundary. -/
def tangentialDefect (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) : ℝ :=
  |τ-κ| + ‖η-ζ‖ + |xo.1-(s+d)| + ‖xo.2-y‖ + |s-xi.1| + ‖y-xi.2‖

/-- Sum of all derivative norms, used only in the interior in
`app:ch_regular:lem:finite-chain`. -/
def fullDefect (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) : ℝ :=
  tangentialDefect xi xo d s y κ ζ τ η + |κ|

omit [InnerProductSpace ℝ E] in
/-- Nonnegativity of the boundary derivative defect
(`app:ch_regular:lem:finite-chain`). -/
theorem tangentialDefect_nonneg (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    0 ≤ tangentialDefect xi xo d s y κ ζ τ η := by
  unfold tangentialDefect
  positivity

omit [InnerProductSpace ℝ E] in
/-- Nonnegativity of the full derivative defect
(`app:ch_regular:lem:finite-chain`). -/
theorem fullDefect_nonneg (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    0 ≤ fullDefect xi xo d s y κ ζ τ η :=
  add_nonneg (tangentialDefect_nonneg ..) (abs_nonneg _)

/-- The defect vanishes exactly at actual tangential stationary points
(`app:ch_regular:lem:finite-chain`). -/
theorem tangentialDefect_eq_zero_iff (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    tangentialDefect xi xo d s y κ ζ τ η = 0 ↔
      TangentialStationary xi xo d s y κ ζ τ η := by
  rw [tangentialStationary_iff]
  simp (disch := positivity) only [tangentialDefect,
    add_eq_zero_iff_of_nonneg,
    abs_eq_zero, norm_eq_zero, sub_eq_zero]
  tauto

/-- The full defect vanishes exactly at actual interior stationary points
(`app:ch_regular:lem:finite-chain`). -/
theorem fullDefect_eq_zero_iff (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    fullDefect xi xo d s y κ ζ τ η = 0 ↔
      InteriorStationary xi xo d s y κ ζ τ η := by
  simp only [fullDefect, add_eq_zero_iff_of_nonneg (tangentialDefect_nonneg ..)
    (abs_nonneg κ), tangentialDefect_eq_zero_iff, abs_eq_zero,
    InteriorStationary, deriv_phase_normal, neg_eq_zero]


omit [InnerProductSpace ℝ E] in
/-- Changing the normal coordinate changes the tangential defect by at most
`|d|` (`app:ch_regular:lem:finite-chain`). This gives a quantitative collar
without differentiating the half-space jump. -/
theorem tangentialDefect_boundary_le (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    tangentialDefect xi xo 0 s y κ ζ τ η ≤
      tangentialDefect xi xo d s y κ ζ τ η + |d| := by
  have h := norm_add_le (xo.1-(s+d)) d
  simp only [Real.norm_eq_abs] at h
  have he : xo.1-(s+d)+d = xo.1-s := by ring
  rw [he] at h
  dsimp [tangentialDefect]
  simp only [add_zero]
  linarith

omit [InnerProductSpace ℝ E] in
/-- A boundary tangential gap persists in a collar of half its width
(`app:ch_regular:lem:finite-chain`). No normal derivative of the jump is used. -/
theorem tangentialDefect_collar {xi xo : ℝ × E} {d s κ τ δ : ℝ} {y ζ η : E}
    (hgap : δ ≤ tangentialDefect xi xo 0 s y κ ζ τ η) (hd : |d| ≤ δ/2) :
    δ/2 ≤ tangentialDefect xi xo d s y κ ζ τ η := by
  have h := tangentialDefect_boundary_le xi xo d s y κ ζ τ η
  linarith

private theorem compact_positive_lower_bound {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (f : X → ℝ) (hf : ContinuousOn f K)
    (hp : ∀ x ∈ K, 0 < f x) : ∃ δ > 0, ∀ x ∈ K, δ ≤ f x := by
  rcases K.eq_empty_or_nonempty with he | hn
  · exact ⟨1, zero_lt_one, by simp [he]⟩
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hn hf
    exact ⟨f x, hp x hx, hmin⟩

/-- Compactness gives a positive boundary tangential gap off the full diagonal
(`app:ch_regular:lem:finite-chain`). No analytic tail estimate is assumed. -/
theorem exists_boundary_gap {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (xi xo : X → ℝ × E) (s κ τ : X → ℝ) (y ζ η : X → E)
    (hxi : Continuous xi) (hxo : Continuous xo) (hs : Continuous s)
    (hκ : Continuous κ) (hτ : Continuous τ) (hy : Continuous y)
    (hζ : Continuous ζ) (hη : Continuous η)
    (hoff : ∀ p ∈ K, ¬ (xo p = xi p ∧ κ p = τ p ∧ ζ p = η p)) :
    ∃ δ > 0, ∀ p ∈ K,
      δ ≤ tangentialDefect (xi p) (xo p) 0 (s p) (y p) (κ p) (ζ p) (τ p) (η p) := by
  apply compact_positive_lower_bound hK
  · exact (show Continuous (fun p => tangentialDefect (xi p) (xo p) 0 (s p)
        (y p) (κ p) (ζ p) (τ p) (η p)) by unfold tangentialDefect; fun_prop).continuousOn
  · intro p hp
    apply lt_of_le_of_ne (tangentialDefect_nonneg ..)
    intro he
    have h := (boundary_stationary_iff (xi p) (xo p) (s p) (y p)
      (κ p) (ζ p) (τ p) (η p)).mp ((tangentialDefect_eq_zero_iff ..).mp he.symm)
    exact hoff p hp ⟨h.1, h.2.1, h.2.2.1⟩

/-- Compactness gives a positive full-gradient defect off the oriented
characteristic image (`app:ch_regular:lem:finite-chain`). -/
theorem exists_interior_gap {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (xi xo : X → ℝ × E) (d s κ τ : X → ℝ) (y ζ η : X → E)
    (hxi : Continuous xi) (hxo : Continuous xo) (hd : Continuous d) (hs : Continuous s)
    (hκ : Continuous κ) (hτ : Continuous τ) (hy : Continuous y)
    (hζ : Continuous ζ) (hη : Continuous η) (hdpos : ∀ p ∈ K, 0 ≤ d p)
    (hoff : ∀ p ∈ K, ¬ ForwardRelation (xi p) (xo p) (τ p) (η p) (κ p) (ζ p)) :
    ∃ δ > 0, ∀ p ∈ K,
      δ ≤ fullDefect (xi p) (xo p) (d p) (s p) (y p) (κ p) (ζ p) (τ p) (η p) := by
  apply compact_positive_lower_bound hK
  · exact (show Continuous (fun p => fullDefect (xi p) (xo p) (d p) (s p)
        (y p) (κ p) (ζ p) (τ p) (η p)) by
      unfold fullDefect tangentialDefect; fun_prop).continuousOn
  · intro p hp
    apply lt_of_le_of_ne (fullDefect_nonneg ..)
    intro he
    apply hoff p hp
    apply (exists_interior_stationary_iff (xi p) (xo p) (κ p) (ζ p) (τ p) (η p)).mp
    exact ⟨d p, s p, y p, hdpos p hp, (fullDefect_eq_zero_iff ..).mp he.symm⟩

end JanetCartan.FiniteChain.Retarded
