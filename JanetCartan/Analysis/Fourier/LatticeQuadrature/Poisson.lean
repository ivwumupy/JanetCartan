module

public import JanetCartan.Analysis.Fourier.LatticeQuadrature.Product
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.PSeries

/-!
# Poisson summation on product lattices

Tensorizing the one-dimensional formula gives a sum over `Fin n → ℤ`,
including the three-dimensional lattice in `app:ch_waves:thm:sampling`.
Mathlib's Fourier transform uses the unit-period `2π` convention.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace JanetCartan.LatticeQuadrature

/-- Translates of a Schwartz function are summable on the integer lattice;
this supplies the convergence needed in `app:ch_waves:thm:sampling`. -/
theorem summable_schwartz_translate (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    Summable (fun m : ℤ ↦ f (u + m)) := by
  have h := summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    (((f.compSubConstCLM ℂ (-u)).isBigO_cocompact_rpow (-2)).comp_tendsto
      Int.tendsto_coe_cofinite)
  simpa [Function.comp_def, sub_eq_add_neg, add_comm] using h

/-- Poisson summation for tensor products over the actual product integer
lattice (`app:ch_waves:thm:sampling`). Both lattice sums converge. -/
theorem poisson_fin_prod (n : ℕ) (f : Fin n → 𝓢(ℝ, ℂ)) (u : Fin n → ℝ) :
    (∑' m : Fin n → ℤ, ∏ i, f i (u i + m i)) =
      ∑' k : Fin n → ℤ,
        (∏ i, 𝓕 (f i) (k i : ℝ)) *
          ∏ i, fourier (k i) (u i : UnitAddCircle) := by
  have hs := hasSum_fin_prod (fun i ↦ (summable_schwartz_translate (f i) (u i)).hasSum)
  have ht : ∀ i, Summable (fun k : ℤ ↦
      𝓕 (f i) (k : ℝ) * fourier k (u i : UnitAddCircle)) := by
    intro i
    apply Summable.of_norm
    simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one, zero_add] using
      (summable_schwartz_translate (𝓕 (f i)) 0).norm
  rw [hs.tsum_eq]
  simp_rw [SchwartzMap.tsum_eq_tsum_fourier]
  convert (hasSum_fin_prod (fun i ↦ (ht i).hasSum)).tsum_eq.symm using 1
  simp only [Finset.prod_mul_distrib]

/-- Compactly supported smooth factors satisfy product-lattice Poisson
summation (`app:ch_waves:thm:sampling`), without extra convergence premises. -/
theorem poisson_fin_prod_of_contDiff_hasCompactSupport {n : ℕ}
    (f : Fin n → ℝ → ℂ) (hc : ∀ i, HasCompactSupport (f i))
    (hs : ∀ i, ContDiff ℝ ∞ (f i)) (u : Fin n → ℝ) :
    (∑' m : Fin n → ℤ, ∏ i, f i (u i + m i)) =
      ∑' k : Fin n → ℤ,
        (∏ i, 𝓕 (f i) (k i : ℝ)) *
          ∏ i, fourier (k i) (u i : UnitAddCircle) := by
  exact poisson_fin_prod n (fun i ↦ (hc i).toSchwartzMap (hs i)) u

/-- The Poisson exactness criterion for a tensor product
(`app:ch_waves:thm:sampling`). This is conditional on the stated Fourier
vanishing; it does not establish those zeros for polynomial-weighted windows. -/
theorem quadrature_fin_prod_of_fourier_zero {n : ℕ}
    (f : Fin n → ℝ → ℂ) (hc : ∀ i, HasCompactSupport (f i))
    (hs : ∀ i, ContDiff ℝ ∞ (f i))
    (hz : ∀ i (k : ℤ), k ≠ 0 → 𝓕 (f i) (k : ℝ) = 0) (u : Fin n → ℝ) :
    (∑' m : Fin n → ℤ, ∏ i, f i (u i + m i)) =
      ∫ x : Fin n → ℝ, ∏ i, f i (x i) := by
  classical
  rw [poisson_fin_prod_of_contDiff_hasCompactSupport f hc hs u]
  rw [tsum_eq_single (0 : Fin n → ℤ)]
  · simp [integral_fintype_prod_volume_eq_prod, Real.fourier_real_eq_integral_exp_smul]
  · intro k hk
    have hex : ∃ i, k i ≠ 0 := by
      by_contra! h
      exact hk (funext h)
    obtain ⟨i, hi⟩ := hex
    have hp : (∏ j, 𝓕 (f j) (k j : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hz i (k i) hi)
    rw [hp, zero_mul]

end JanetCartan.LatticeQuadrature
