module

public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# The literal localized graph phases

The five equations in `app:ch_regular:eq:joint-stationary` are obtained from
actual partial Fréchet derivatives. Covectors are physical covectors throughout.
The reverse phase exchanges the two physical positions as well as the sign of
the graph phase; it is not obtained by reversing the sign alone.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `app:ch_regular:eq:joint-kernel-phase`, after frequency normalization. -/
def forwardPhase (φ : E → E → ℝ) (x y u z ξ η ζ : E) : ℝ :=
  φ u ξ - inner ℝ z ξ + inner ℝ (z-y) η + inner ℝ (x-u) ζ

/-- The literal inverse-graph phase in `app:ch_regular:lem:finite-chain`. -/
def reversePhase (φ : E → E → ℝ) (x y u z ξ η ζ : E) : ℝ :=
  inner ℝ z ξ - φ u ξ + inner ℝ (u-y) η + inner ℝ (x-z) ζ

/-- The inverse phase is the negative forward phase with input and output
exchanged (`app:ch_regular:lem:finite-chain`). -/
theorem reversePhase_eq_neg_swap (φ : E → E → ℝ) (x y u z ξ η ζ : E) :
    reversePhase φ x y u z ξ η ζ = -forwardPhase φ y x u z ξ ζ η := by
  simp only [reversePhase, forwardPhase, inner_sub_left]
  ring

/-- Homogeneity gives the exact normalized forward phase, with all three
physical covectors scaled by the same frequency
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem forwardPhase_rescale (Φ φ : E → E → ℝ) (ρ : ℝ) (x y u z ξ η ζ : E)
    (hφ : Φ u (ρ • ξ) = ρ * φ u ξ) :
    forwardPhase Φ x y u z (ρ • ξ) (ρ • η) (ρ • ζ) =
      ρ * forwardPhase φ x y u z ξ η ζ := by
  simp only [forwardPhase, hφ, inner_smul_right]
  ring

/-- The same three-frequency normalization for the literal inverse phase
(`app:ch_regular:lem:finite-chain`). -/
theorem reversePhase_rescale (Φ φ : E → E → ℝ) (ρ : ℝ) (x y u z ξ η ζ : E)
    (hφ : Φ u (ρ • ξ) = ρ * φ u ξ) :
    reversePhase Φ x y u z (ρ • ξ) (ρ • η) (ρ • ζ) =
      ρ * reversePhase φ x y u z ξ η ζ := by
  rw [reversePhase_eq_neg_swap, forwardPhase_rescale Φ φ ρ y x u z ξ ζ η hφ,
    reversePhase_eq_neg_swap]
  ring

/-- Actual derivative in the output base of the graph factor
(`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_forwardPhase_u (φ : E → E → ℝ) (x y u z ξ η ζ : E)
    (hφ : DifferentiableAt ℝ (fun v => φ v ξ) u) :
    fderiv ℝ (fun v => forwardPhase φ x y v z ξ η ζ) u =
      fderiv ℝ (fun v => φ v ξ) u - innerSL ℝ ζ := by
  have he : (fun v => forwardPhase φ x y v z ξ η ζ) = fun v =>
      φ v ξ - innerSL ℝ ζ v +
        (-inner ℝ z ξ + inner ℝ (z-y) η + inner ℝ x ζ) := by
    funext v
    simp only [forwardPhase, inner_sub_left, innerSL_apply_apply]
    rw [real_inner_comm ζ v]
    ring
  rw [he]
  exact ((hφ.hasFDerivAt.sub (innerSL ℝ ζ).hasFDerivAt).add_const _).fderiv

/-- The input base derivative supplies the larger-frequency difference
(`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_forwardPhase_z (φ : E → E → ℝ) (x y u z ξ η ζ : E) :
    fderiv ℝ (fun v => forwardPhase φ x y u v ξ η ζ) z = innerSL ℝ (η-ξ) := by
  have he : (fun v => forwardPhase φ x y u v ξ η ζ) = fun v =>
      innerSL ℝ (η-ξ) v + (φ u ξ - inner ℝ y η + inner ℝ (x-u) ζ) := by
    funext v
    simp only [forwardPhase, inner_sub_left, innerSL_apply_apply]
    rw [real_inner_comm η v, real_inner_comm ξ v]
    ring
  rw [he]
  exact ((innerSL ℝ (η-ξ)).hasFDerivAt.add_const _).fderiv

/-- The graph covector derivative (`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_forwardPhase_xi (φ : E → E → ℝ) (x y u z ξ η ζ : E)
    (hφ : DifferentiableAt ℝ (φ u) ξ) :
    fderiv ℝ (fun v => forwardPhase φ x y u z v η ζ) ξ =
      fderiv ℝ (φ u) ξ - innerSL ℝ z := by
  exact (((hφ.hasFDerivAt.sub (innerSL ℝ z).hasFDerivAt).add_const _).add_const _).fderiv

/-- The right input symbol retains the equation `z = y`
(`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_forwardPhase_eta (φ : E → E → ℝ) (x y u z ξ η ζ : E) :
    fderiv ℝ (fun v => forwardPhase φ x y u z ξ v ζ) η = innerSL ℝ (z-y) := by
  exact (((innerSL ℝ (z-y)).hasFDerivAt.const_add _).add_const _).fderiv

/-- The left output symbol retains the equation `x = u`
(`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_forwardPhase_zeta (φ : E → E → ℝ) (x y u z ξ η ζ : E) :
    fderiv ℝ (fun v => forwardPhase φ x y u z ξ η v) ζ = innerSL ℝ (x-u) := by
  exact ((innerSL ℝ (x-u)).hasFDerivAt.const_add _).fderiv

/-- Stationarity means vanishing of all five actual partial derivatives,
including both localizer covectors (`app:ch_regular:eq:joint-stationary`). -/
def ForwardStationary (φ : E → E → ℝ) (x y u z ξ η ζ : E) : Prop :=
  fderiv ℝ (fun v => forwardPhase φ x y v z ξ η ζ) u = 0 ∧
  fderiv ℝ (fun v => forwardPhase φ x y u v ξ η ζ) z = 0 ∧
  fderiv ℝ (fun v => forwardPhase φ x y u z v η ζ) ξ = 0 ∧
  fderiv ℝ (fun v => forwardPhase φ x y u z ξ v ζ) η = 0 ∧
  fderiv ℝ (fun v => forwardPhase φ x y u z ξ η v) ζ = 0

/-- Vanishing of the five derivatives of the literal reverse phase
(`app:ch_regular:lem:finite-chain`). -/
def ReverseStationary (φ : E → E → ℝ) (x y u z ξ η ζ : E) : Prop :=
  fderiv ℝ (fun v => reversePhase φ x y v z ξ η ζ) u = 0 ∧
  fderiv ℝ (fun v => reversePhase φ x y u v ξ η ζ) z = 0 ∧
  fderiv ℝ (fun v => reversePhase φ x y u z v η ζ) ξ = 0 ∧
  fderiv ℝ (fun v => reversePhase φ x y u z ξ v ζ) η = 0 ∧
  fderiv ℝ (fun v => reversePhase φ x y u z ξ η v) ζ = 0

/-- All five forward equations, with the derivatives represented as covectors
using the real inner product (`app:ch_regular:eq:joint-stationary`). -/
theorem forwardStationary_iff (φ : E → E → ℝ) (x y u z ξ η ζ : E)
    (hu : DifferentiableAt ℝ (fun v => φ v ξ) u)
    (hξ : DifferentiableAt ℝ (φ u) ξ) :
    ForwardStationary φ x y u z ξ η ζ ↔
      fderiv ℝ (fun v => φ v ξ) u = innerSL ℝ ζ ∧ η = ξ ∧
      fderiv ℝ (φ u) ξ = innerSL ℝ z ∧ z = y ∧ x = u := by
  have hz (v : E) : innerSL ℝ v = 0 ↔ v = 0 := by
    rw [← norm_eq_zero, innerSL_apply_norm, norm_eq_zero]
  simp only [ForwardStationary, fderiv_forwardPhase_u φ x y u z ξ η ζ hu,
    fderiv_forwardPhase_z, fderiv_forwardPhase_xi φ x y u z ξ η ζ hξ,
    fderiv_forwardPhase_eta, fderiv_forwardPhase_zeta, hz, sub_eq_zero]

/-- Literal reversal exchanges the input and output equations
(`app:ch_regular:lem:finite-chain`). -/
theorem reverseStationary_iff_swap (φ : E → E → ℝ) (x y u z ξ η ζ : E) :
    ReverseStationary φ x y u z ξ η ζ ↔ ForwardStationary φ y x u z ξ ζ η := by
  simp only [ReverseStationary, ForwardStationary, reversePhase_eq_neg_swap,
    fderiv_fun_neg, neg_eq_zero]
  tauto

/-- The five literal reverse equations, including `u = y` and `x = z`
(`app:ch_regular:lem:finite-chain`). -/
theorem reverseStationary_iff (φ : E → E → ℝ) (x y u z ξ η ζ : E)
    (hu : DifferentiableAt ℝ (fun v => φ v ξ) u)
    (hξ : DifferentiableAt ℝ (φ u) ξ) :
    ReverseStationary φ x y u z ξ η ζ ↔
      fderiv ℝ (fun v => φ v ξ) u = innerSL ℝ η ∧ ζ = ξ ∧
      fderiv ℝ (φ u) ξ = innerSL ℝ z ∧ u = y ∧ x = z := by
  rw [reverseStationary_iff_swap, forwardStationary_iff φ y x u z ξ ζ η hu hξ]
  tauto

/-- The full forward canonical relation, with physical base points
(`app:ch_regular:eq:joint-stationary`). -/
def ForwardRelation (φ : E → E → ℝ) (y η x ζ : E) : Prop :=
  fderiv ℝ (fun u => φ u η) x = innerSL ℝ ζ ∧
    fderiv ℝ (φ x) η = innerSL ℝ y

/-- Projecting the critical set gives exactly the full graph, not merely its
covector projection (`app:ch_regular:eq:joint-stationary`). -/
theorem exists_forwardStationary_iff (φ : E → E → ℝ) (x y η ζ : E)
    (hu : ∀ u ξ, DifferentiableAt ℝ (fun v => φ v ξ) u)
    (hξ : ∀ u ξ, DifferentiableAt ℝ (φ u) ξ) :
    (∃ u z ξ, ForwardStationary φ x y u z ξ η ζ) ↔ ForwardRelation φ y η x ζ := by
  simp only [forwardStationary_iff φ _ _ _ _ _ _ _ (hu _ _) (hξ _ _)]
  constructor
  · rintro ⟨u, z, ξ, h1, h2, h3, h4, h5⟩
    subst u; subst z; subst ξ
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x, y, η, h1, rfl, h2, rfl, rfl⟩

/-- The inverse critical set projects to the inverse full graph
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_reverseStationary_iff (φ : E → E → ℝ) (x y η ζ : E)
    (hu : ∀ u ξ, DifferentiableAt ℝ (fun v => φ v ξ) u)
    (hξ : ∀ u ξ, DifferentiableAt ℝ (φ u) ξ) :
    (∃ u z ξ, ReverseStationary φ x y u z ξ η ζ) ↔ ForwardRelation φ x ζ y η := by
  simp only [reverseStationary_iff_swap, exists_forwardStationary_iff φ y x ζ η hu hξ]

/-- Diagonal factors have the full diagonal relation
(`app:ch_regular:lem:finite-chain`). -/
theorem diagonal_forwardRelation_iff (x y η ζ : E) :
    ForwardRelation (fun u ξ => inner ℝ u ξ) y η x ζ ↔ x = y ∧ ζ = η := by
  have he : (fun u => inner ℝ u η) = innerSL ℝ η := by
    funext u; exact (real_inner_comm u η).symm
  have hinj (a b : E) : innerSL ℝ a = innerSL ℝ b ↔ a = b := by
    rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, innerSL_apply_norm,
      norm_eq_zero, sub_eq_zero]
  have hf : fderiv ℝ (fun ξ => inner ℝ x ξ) η = innerSL ℝ x :=
    (innerSL ℝ x).fderiv
  simp only [ForwardRelation, he, hf, ContinuousLinearMap.fderiv, hinj]
  tauto

end JanetCartan.FiniteChain.Graph
