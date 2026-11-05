module

public import JanetCartan.Analysis.Microlocal.NormalComparison.ChangeOfVariables
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Mask and Jacobian derivative terms

Calculus identities used in `app:ch_osc:prop:osc-normal`. These identities retain
the first derivative of the mask and the Jacobian derivative. They do not by
themselves prove the uniform spatial derivative bounds needed for the L² estimate.
-/

@[expose] public noncomputable section

namespace JanetCartan.NormalComparison

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivative of the transformed amplitude in
`app:ch_osc:eq:osc-exact-normal-kernel`. Here `A` denotes the amplitude evaluated
along the inverse chart and `J` its absolute Jacobian. Both the Jacobian derivative
and `Dm(U) U'` appear; no higher mask derivatives enter this identity. -/
theorem hasDerivAt_inverseJacobian_mask
    {A : ℝ → F} {A' : F} {U : ℝ → Euclidean n} {U' : Euclidean n}
    {J : ℝ → ℝ} {J' ε : ℝ} {m : Euclidean n → ℝ}
    {m' : Euclidean n →L[ℝ] ℝ}
    (hA : HasDerivAt A A' ε) (hU : HasDerivAt U U' ε)
    (hJ : HasDerivAt J J' ε) (hJ₀ : J ε ≠ 0)
    (hm : HasFDerivAt m m' (U ε)) :
    HasDerivAt (fun t ↦ (J t)⁻¹ • (m (U t) • A t))
      ((-J' / (J ε) ^ 2) • (m (U ε) • A ε) +
        (J ε)⁻¹ • (m' U' • A ε + m (U ε) • A')) ε := by
  simpa only [Pi.smul_def', Function.comp_def, Pi.inv_def, add_comm] using
    (hJ.inv hJ₀).smul ((hm.comp_hasDerivAt ε hU).smul hA)

/-- The inverse-chart velocity identity used in the second step of
`app:ch_osc:prop:osc-normal`: differentiating `Ψ(ε,U(ε,v)) = v` gives
`U' = -(DᵤΨ)⁻¹ ∂εΨ`. -/
theorem inverse_velocity_eq_neg
    (J : Euclidean n ≃L[ℝ] Euclidean n) (p q : Euclidean n)
    (h : p + J q = 0) : q = -J.symm p := by
  apply J.injective
  simpa using (eq_neg_of_add_eq_zero_right h)

/-- The mask Leibniz rule in the original input variable, used before integration
by parts in `app:ch_osc:prop:osc-normal`. -/
theorem partialDeriv_mask_smul
    (m : Euclidean n → ℝ) (B : Euclidean n → F) (u : Euclidean n) (j : Fin n)
    (hm : DifferentiableAt ℝ m u) (hB : DifferentiableAt ℝ B u) :
    partialDeriv (fun v ↦ m v • B v) u j =
      partialDeriv m u j • B u + m u • partialDeriv B u j := by
  change (fderiv ℝ (m • B) u) (EuclideanSpace.single j 1) = _
  simp [fderiv_smul hm hB, partialDeriv, add_comm]

/-- The divergence coefficient `c₀ = ∂ε A - divᵤ(w A)` of
`app:ch_osc:prop:osc-normal`. Both physical positions are parameters of `A,w`. -/
def transportCoefficient (Aε : Euclidean n → F)
    (B : Fin n → Euclidean n → F) (u : Euclidean n) : F :=
  Aε u - ∑ j, partialDeriv (B j) u j

/-- The exact first-mask-derivative decomposition after integration by parts in
`app:ch_osc:prop:osc-normal`, written with `Bⱼ = wⱼ A`. The identity is pointwise;
integrating it and justifying parameter differentiation are separate steps. -/
theorem mask_transport_expansion
    (m : Euclidean n → ℝ) (Aε : Euclidean n → F)
    (B : Fin n → Euclidean n → F) (u : Euclidean n)
    (hm : DifferentiableAt ℝ m u) (hB : ∀ j, DifferentiableAt ℝ (B j) u) :
    m u • Aε u - ∑ j, partialDeriv (fun v ↦ m v • B j v) u j =
      m u • transportCoefficient Aε B u + ∑ j, partialDeriv m u j • (-B j u) := by
  simp only [partialDeriv_mask_smul m _ u _ hm (hB _), Finset.sum_add_distrib,
    transportCoefficient, smul_sub, Finset.smul_sum, smul_neg, Finset.sum_neg_distrib]
  abel

end JanetCartan.NormalComparison
