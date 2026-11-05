module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.ProductSum.Estimates

import Mathlib.Tactic.NormNum

/-!
# Weighted assembly of complete signed-product corrections

The finite assembly step of `app:ch_pairs:prop:pairs-lag-sum` in `paper.tex`.
`offSelfSource` is the literal quadratic derivative tensor minus its full
Hermitian self tensor. Its expansion is proved using `SignedExpansion`; no
amplitude or modulation term is deleted. The plus family includes doubled
carriers, and the minus family excludes exactly the equal-index diagonal.

These are **conditional analytic estimates**. `S` is one fixed real linear
solver, including the source cutoff, inverse, frame and ambient reconstruction.
`D` observes the linearized metric on `D`, `R` restricts the source to `D`, and
`O` observes the ambient field in the desired norm. Their ranges may be Sobolev
spaces with the stipulated Frobenius tensor norm. With an observation including
the fixed physical output cutoff, the size theorem also gives the torus bound.
The exact individual full-source error and size estimates are explicit inputs.
This file does not prove those analytic estimates or construct the solver.

`complete_signed_product_bounds` keeps the same literal `S` for all observation
orders and accuracies. Errors decay at the true beat lower bound `c lambda h`;
sizes grow at the carrier scale `lambda`. The conclusion includes both exact
weighted bounds and bounds with one sample-count factor and amplitude `b²`.
-/

@[expose] public noncomputable section

namespace JanetCartan.ProductSum

variable {ι X m n V E : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
variable [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equation `app:ch_pairs:eq:pairs-lag-sum-error`, conditional on the individual
complete-source estimate `app:ch_pairs:eq:pairs-lag-one-error`. The source is
derived from the complete derivative factorization. -/
theorem offSelf_error_bound (S : (X → Matrix n n ℝ) →ₗ[ℝ] V)
    (D : V →ₗ[ℝ] E) (R : (X → Matrix n n ℝ) →ₗ[ℝ] E)
    (b : ℝ) (μ : ι → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (θ : ι → X → ℝ) (dW A : ι → X → Matrix m n ℂ)
    (hdW : ∀ j x, dW j x = wavePhase (θ j x) • A j x)
    (ρplus ρminus : ι → ι → ℝ) {lambda h c C : ℝ}
    (hlambda : 0 < lambda) (hh : 0 < h) (hc : 0 < c) (hC : 0 ≤ C) (Q : ℕ)
    (hρp : ∀ j k, c * (lambda * h) ≤ ρplus j k)
    (hρm : ∀ j k, k ≠ j → c * (lambda * h) ≤ ρminus j k)
    (hp : ∀ j k, ‖D (S (plusSource θ A j k)) + R (plusSource θ A j k)‖ ≤
      C * ((ρplus j k) ^ Q)⁻¹)
    (hm : ∀ j k, k ≠ j →
      ‖D (S (minusSource θ A j k)) + R (minusSource θ A j k)‖ ≤
        C * ((ρminus j k) ^ Q)⁻¹) :
    ‖D (S (offSelfSource b μ dW A)) + R (offSelfSource b μ dW A)‖ ≤
      (2 * C * (c ^ Q)⁻¹) * b ^ 2 * coefficientMass μ * ((lambda * h) ^ Q)⁻¹ := by
  change ‖(D.comp S + R) (offSelfSource b μ dW A)‖ ≤ _
  rw [offSelfSource_eq_weightedSignedSum b μ hμ θ dW A hdW]
  exact error_bound_of_individual (D.comp S + R) b μ hμ
    (plusSource θ A) (minusSource θ A) ρplus ρminus hlambda hh hc hC Q hρp hρm hp hm

/-- Equation `app:ch_pairs:eq:pairs-lag-sum-size`, conditional on individual
full-source size estimates. Taking `O` to include the fixed physical cutoff
gives the same assembly on the torus. -/
theorem offSelf_size_bound (S : (X → Matrix n n ℝ) →ₗ[ℝ] V)
    (O : V →ₗ[ℝ] E) (b : ℝ) (μ : ι → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (θ : ι → X → ℝ) (dW A : ι → X → Matrix m n ℂ)
    (hdW : ∀ j x, dW j x = wavePhase (θ j x) • A j x)
    {lambda C : ℝ} (hlambda : 0 ≤ lambda) (hC : 0 ≤ C) (s : ℕ)
    (hp : ∀ j k, ‖O (S (plusSource θ A j k))‖ ≤ C * lambda ^ (s + 1))
    (hm : ∀ j k, k ≠ j → ‖O (S (minusSource θ A j k))‖ ≤ C * lambda ^ (s + 1)) :
    ‖O (S (offSelfSource b μ dW A))‖ ≤
      (2 * C) * b ^ 2 * coefficientMass μ * lambda ^ (s + 1) := by
  change ‖(O.comp S) (offSelfSource b μ dW A)‖ ≤ _
  rw [offSelfSource_eq_weightedSignedSum b μ hμ θ dW A hdW]
  exact size_bound_of_individual (O.comp S) b μ hμ
    (plusSource θ A) (minusSource θ A) hlambda hC s hp hm

variable {Error Size : ℕ → Type*}
variable [∀ s, NormedAddCommGroup (Error s)] [∀ s, NormedSpace ℝ (Error s)]
variable [∀ s, NormedAddCommGroup (Size s)] [∀ s, NormedSpace ℝ (Size s)]

/-- The finite weighted conclusion of `app:ch_pairs:prop:pairs-lag-sum` for all
natural observation orders and accuracies with one literal solver. The analytic
hypotheses are individual estimates for both complete signed sources, including
every doubled carrier. The size observation may include an output cutoff.
The sample-count bounds are derived here from these individual inputs. -/
theorem complete_signed_product_bounds
    (S : (X → Matrix n n ℝ) →ₗ[ℝ] V)
    (D : ∀ s, V →ₗ[ℝ] Error s) (R : ∀ s, (X → Matrix n n ℝ) →ₗ[ℝ] Error s)
    (O : ∀ s, V →ₗ[ℝ] Size s)
    (b : ℝ) (μ : ι → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (Cμ : ℝ) (hmass : ∑ j, μ j ≤ Cμ)
    (θ : ι → X → ℝ) (dW A : ι → X → Matrix m n ℂ)
    (hdW : ∀ j x, dW j x = wavePhase (θ j x) • A j x)
    (ρplus ρminus : ι → ι → ℝ) {lambda h c : ℝ}
    (hlambda : 0 < lambda) (hh : 0 < h) (hc : 0 < c)
    (Cerror : ℕ → ℕ → ℝ) (Csize : ℕ → ℝ)
    (hCe : ∀ s Q, 0 ≤ Cerror s Q) (hCs : ∀ s, 0 ≤ Csize s)
    (hρp : ∀ j k, c * (lambda * h) ≤ ρplus j k)
    (hρm : ∀ j k, k ≠ j → c * (lambda * h) ≤ ρminus j k)
    (hep : ∀ s Q j k,
      ‖D s (S (plusSource θ A j k)) + R s (plusSource θ A j k)‖ ≤
        Cerror s Q * ((ρplus j k) ^ Q)⁻¹)
    (hem : ∀ s Q j k, k ≠ j →
      ‖D s (S (minusSource θ A j k)) + R s (minusSource θ A j k)‖ ≤
        Cerror s Q * ((ρminus j k) ^ Q)⁻¹)
    (hsp : ∀ s j k, ‖O s (S (plusSource θ A j k))‖ ≤ Csize s * lambda ^ (s + 1))
    (hsm : ∀ s j k, k ≠ j →
      ‖O s (S (minusSource θ A j k))‖ ≤ Csize s * lambda ^ (s + 1)) :
    (∀ s Q, ‖D s (S (offSelfSource b μ dW A)) + R s (offSelfSource b μ dW A)‖ ≤
      (2 * Cerror s Q * (c ^ Q)⁻¹) * b ^ 2 * coefficientMass μ * ((lambda * h) ^ Q)⁻¹) ∧
    (∀ s, ‖O s (S (offSelfSource b μ dW A))‖ ≤
      (2 * Csize s) * b ^ 2 * coefficientMass μ * lambda ^ (s + 1)) ∧
    (∀ s Q, ‖D s (S (offSelfSource b μ dW A)) + R s (offSelfSource b μ dW A)‖ ≤
      (2 * Cerror s Q * (c ^ Q)⁻¹) * b ^ 2 *
        (Fintype.card ι * Cμ) * ((lambda * h) ^ Q)⁻¹) ∧
    (∀ s, ‖O s (S (offSelfSource b μ dW A))‖ ≤
      (2 * Csize s) * b ^ 2 * (Fintype.card ι * Cμ) * lambda ^ (s + 1)) := by
  have he := fun s Q ↦ offSelf_error_bound S (D s) (R s) b μ hμ θ dW A hdW ρplus ρminus
      hlambda hh hc (hCe s Q) Q hρp hρm (hep s Q) (hem s Q)
  have hs := fun s ↦ offSelf_size_bound S (O s) b μ hμ θ dW A hdW
      hlambda.le (hCs s) s (hsp s) (hsm s)
  refine ⟨he, hs, ?_, ?_⟩
  · intro s Q
    exact bound_by_sample_count μ hμ hmass
      (mul_nonneg (mul_nonneg (by norm_num) (hCe s Q))
        (inv_nonneg.mpr (pow_nonneg hc.le Q)))
      (inv_nonneg.mpr (pow_nonneg (mul_pos hlambda hh).le Q)) (he s Q)
  · intro s
    exact bound_by_sample_count μ hμ hmass (mul_nonneg (by norm_num) (hCs s))
      (pow_nonneg hlambda.le _) (hs s)

end JanetCartan.ProductSum
