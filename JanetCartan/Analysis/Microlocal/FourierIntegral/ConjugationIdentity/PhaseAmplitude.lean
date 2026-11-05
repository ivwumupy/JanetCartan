module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.SymbolDerivatives
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Actual derivatives of the leading graph amplitude

Chain rules for `b₀ = c(x,S_x) U` in
`app:ch_regular_base:eq:direct-graph-amplitudes`. The covector is Mathlib's
gradient of the supplied real phase; no independent Hessian array is supplied.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral

variable {n r : ℕ}

/-- Components of the actual eikonal covector in
`app:ch_regular_base:eq:direct-graph-amplitudes`. -/
theorem phase_gradient_apply (S : Euclidean n → ℝ) (x : Euclidean n) (j : Fin n) :
    gradient S x j = partialDeriv S x j := by
  simpa only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul,
    partialDeriv] using (inner_gradient_left (f := S) (x := x)
      (y := EuclideanSpace.single j 1))

/-- The actual phase covector is differentiable for a `C²` phase, as required
by the chain rule in `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem differentiableAt_phase_gradient (S : Euclidean n → ℝ) {x : Euclidean n}
    (hS : ContDiffAt ℝ 2 S x) : DifferentiableAt ℝ (gradient S) x := by
  exact (InnerProductSpace.toDual ℝ (Euclidean n)).symm.toContinuousLinearEquiv.differentiableAt.comp x
    ((hS.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

/-- Differentiating the actual eikonal covector gives the actual phase Hessian
(`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem partialDeriv_phase_gradient_apply (S : Euclidean n → ℝ) {x : Euclidean n}
    (hS : ContDiffAt ℝ 2 S x) (j l : Fin n) :
    partialDeriv (gradient S) x j l = partialDeriv (fun z ↦ partialDeriv S z l) x j := by
  have hd := ((EuclideanSpace.proj l).hasFDerivAt.comp x
    (differentiableAt_phase_gradient S hS).hasFDerivAt).fderiv
  have heq : (fun z ↦ gradient S z l) = fun z ↦ partialDeriv S z l :=
    funext fun z ↦ phase_gradient_apply S z l
  have hv := congrArg (fun L ↦ L (EuclideanSpace.single j 1)) hd
  change partialDeriv (fun z ↦ gradient S z l) x j = partialDeriv (gradient S) x j l at hv
  rw [heq] at hv
  exact hv.symm

/-- The chain rule for the leading amplitude realizes exactly the array
`leadingAmplitudeDerivative` consumed by `two_term_transport_identity`.
Source: `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem partialDeriv_leadingAmplitude_phase
    (c : Euclidean n × Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → ℝ) (U : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    {x : Euclidean n} (hc : DifferentiableAt ℝ c (x, gradient S x))
    (hS : ContDiffAt ℝ 2 S x) (hU : DifferentiableAt ℝ U x) (j : Fin n) :
    partialDeriv (fun z ↦ leadingAmplitude (c (z, gradient S z)) (U z)) x j =
      leadingAmplitudeDerivative (c (x, gradient S x)) (U x)
        (fun k ↦ partialDeriv (fun z ↦ c (z, gradient S x)) x k)
        (fun k ↦ partialDeriv (fun ξ ↦ c (x, ξ)) (gradient S x) k)
        (partialDeriv U x)
        (fun k l ↦ ((partialDeriv (fun z ↦ partialDeriv S z l) x k : ℝ) : ℂ)) j := by
  have hgrad := differentiableAt_phase_gradient S hS
  have hcomp := hc.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hgrad.hasFDerivAt)
  have hx := hc.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (gradient S x))
  have hξ := hc.hasFDerivAt.comp (gradient S x) (hasFDerivAt_prodMk_right (𝕜 := ℝ) x (gradient S x))
  have hchain : partialDeriv (fun z ↦ c (z, gradient S z)) x j =
      partialDeriv (fun z ↦ c (z, gradient S x)) x j +
        ∑ l, ((partialDeriv (fun z ↦ partialDeriv S z l) x j : ℝ) : ℂ) •
          partialDeriv (fun ξ ↦ c (x, ξ)) (gradient S x) l := by
    unfold partialDeriv
    erw [hcomp.fderiv]
    change fderiv ℝ c (x, gradient S x)
      (EuclideanSpace.single j 1, partialDeriv (gradient S) x j) = _
    have hv := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (partialDeriv (gradient S) x j)
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
      partialDeriv_phase_gradient_apply S hS] at hv
    have hsplit : (EuclideanSpace.single j 1, partialDeriv (gradient S) x j) =
        (EuclideanSpace.single j 1, 0) +
          ∑ l, partialDeriv (fun z ↦ partialDeriv S z l) x j •
            ((0 : Euclidean n), EuclideanSpace.single l 1) := by
      apply Prod.ext <;> simp [← hv, Prod.fst_sum, Prod.snd_sum]
    rw [hsplit, map_add, map_sum]
    simp only [map_smul, partialDeriv, Complex.coe_smul]
    erw [hx.fderiv, hξ.fderiv]
    rfl
  have hp := (hcomp.differentiableAt.hasFDerivAt.mul' hU.hasFDerivAt).fderiv
  change partialDeriv (fun z ↦ c (z, gradient S z) * U z) x j = _
  unfold partialDeriv
  erw [hp]
  change c (x, gradient S x) * partialDeriv U x j +
    partialDeriv (fun z ↦ c (z, gradient S z)) x j * U x = _
  rw [hchain]
  exact add_comm _ _

end JanetCartan.FourierIntegral
