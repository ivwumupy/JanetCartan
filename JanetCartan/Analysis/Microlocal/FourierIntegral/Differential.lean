module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Module

/-!
# The physical differential operator and its cutoff commutator

The differential nature of `L_a = P_a / i` makes the physical transition vanish
exactly on an inner plateau. This file proves that fact for the actual derivative
operator, rather than assuming a vanishing operator commutator.
-/

@[expose] public noncomputable section

open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral

/-- The first-order matrix operator `L = -i(∑ Aⱼ ∂ⱼ + B)` used in
`app:ch_regular_base:eq:actual-global-cutoff`. -/
def physicalOperator {n r : ℕ}
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (f : Euclidean n → Fin r → ℂ) (x : Euclidean n) : Fin r → ℂ :=
  -Complex.I • ((∑ j, (A x j).mulVec (partialDeriv f x j)) + (B x).mulVec (f x))

/-- Coordinate product rule for a scalar cutoff, used in
`app:ch_regular_base:eq:actual-global-cutoff`. -/
theorem partialDeriv_cutoff_mul {n r : ℕ} (χ : Euclidean n → ℂ)
    (f : Euclidean n → Fin r → ℂ) (x : Euclidean n) (j : Fin n)
    (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x) :
    partialDeriv (fun y ↦ χ y • f y) x j =
      χ x • partialDeriv f x j + partialDeriv χ x j • f x := by
  simp only [partialDeriv, fderiv_fun_smul hχ hf, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply]

/-- The exact multiplication commutator `-i ∑ Aⱼ ∂ⱼχ`, with no derivative of
`f` left over (`app:ch_regular_base:eq:actual-global-cutoff`). -/
theorem physicalOperator_cutoff_commutator {n r : ℕ}
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χ : Euclidean n → ℂ) (f : Euclidean n → Fin r → ℂ) (x : Euclidean n)
    (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x) :
    physicalOperator A B (fun y ↦ χ y • f y) x - χ x • physicalOperator A B f x =
      -Complex.I • (∑ j, partialDeriv χ x j • (A x j).mulVec (f x)) := by
  simp only [physicalOperator, partialDeriv_cutoff_mul χ f x _ hχ hf,
    Matrix.mulVec_add, Matrix.mulVec_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  module

/-- Locality of the actual first-order operator; used for the physical plateau
in `app:ch_regular_base:thm:actual-calculus`, Step 5. -/
theorem physicalOperator_congr_of_eventuallyEq {n r : ℕ}
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (f g : Euclidean n → Fin r → ℂ) (x : Euclidean n)
    (h : f =ᶠ[𝓝 x] g) : physicalOperator A B f x = physicalOperator A B g x := by
  simp only [physicalOperator, partialDeriv, h.fderiv_eq, h.eq_of_nhds]

/-- The physical transition vanishes on every fixed inner plateau. The only
cutoff assumption is that `χt = 1` near each point where `χe` is nonzero.
Source: `app:ch_regular_base:eq:actual-inner-conjugation`. -/
theorem physical_transition_zero_on_plateau {n r : ℕ}
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χt χe : Euclidean n → ℂ) (f : Euclidean n → Fin r → ℂ)
    (hplateau : ∀ x, χe x ≠ 0 → χt =ᶠ[𝓝 x] fun _ ↦ 1) (x : Euclidean n) :
    χe x • (physicalOperator A B (fun y ↦ χt y • f y) x -
      χt x • physicalOperator A B f x) = 0 := by
  by_cases hx : χe x = 0
  · simp [hx]
  have ht := hplateau x hx
  have htf : (fun y ↦ χt y • f y) =ᶠ[𝓝 x] f := by
    filter_upwards [ht] with y hy
    simp only [hy, one_smul]
  rw [physicalOperator_congr_of_eventuallyEq A B _ f x htf, ht.eq_of_nhds]
  simp

end JanetCartan.FourierIntegral
