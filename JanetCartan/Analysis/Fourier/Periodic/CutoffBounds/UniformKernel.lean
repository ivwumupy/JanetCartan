module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass

/-!
# Uniform derivative bounds for the fixed periodic cutoff

For `main:lem:smoothing` and `main:eq:smoothing-low`, the derivative kernel
representation and its uniform L¹ mass estimate give the pointwise bound
`C * R ^ j * M`. The constant depends only on the dimension and derivative
order, and works for every complete real normed codomain. In particular, the
codomain may itself be a space of continuous multilinear maps.

The imported mass estimate is proved by periodizing derivatives of the fixed
Euclidean inverse Fourier profile. It preserves the `2π` convention and the
exact symbol defining `periodicCutoff`.
-/

@[expose] public noncomputable section

open MeasureTheory

universe u

namespace JanetCartan

/-- `main:lem:smoothing`, `main:eq:smoothing-low`: the derivative kernel has
uniform L¹ mass at every Euclidean evaluation point. -/
theorem exists_periodicCutoffDerivKernel_uniform_mass_bound (n j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ x : EuclideanSpace ℝ (Fin n),
        (∫ y : Torus n, ‖periodicCutoffDerivKernel j R x y‖) ≤ C * R ^ j := by
  obtain ⟨C, hC, hmass⟩ := exists_periodicCutoffDerivKernel_mass_bound n j
  refine ⟨C, hC, ?_⟩
  intro R hR x
  rw [integral_norm_periodicCutoffDerivKernel_eq]
  exact hmass R hR

/-- `main:lem:smoothing`, `main:eq:smoothing-low`: the fixed cutoff maps a
continuous function bounded by `M` to a function whose order-`j` derivative is
bounded by `C * R ^ j * M`. The same nonnegative constant works for all complete
real normed codomains, scales `R ≥ 1`, inputs, bounds, and evaluation points. -/
theorem exists_periodicCutoff_derivative_bound (n j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        {R : ℝ}, 1 ≤ R → ∀ {f : Torus n → F}, Continuous f →
        ∀ {M : ℝ}, 0 ≤ M → (∀ y, ‖f y‖ ≤ M) →
        ∀ x : EuclideanSpace ℝ (Fin n),
          ‖iteratedFDeriv ℝ j (periodicLift (periodicCutoff R f)) x‖ ≤
            C * R ^ j * M := by
  obtain ⟨C, hC, hmass⟩ := exists_periodicCutoffDerivKernel_uniform_mass_bound n j
  refine ⟨C, hC, ?_⟩
  intro F _ _ _ R hR f hf M hM hbound x
  exact (norm_iteratedFDeriv_periodicCutoff_le_kernel_mass hf hbound j R x).trans
    (mul_le_mul_of_nonneg_right (hmass R hR x) hM)

end JanetCartan
