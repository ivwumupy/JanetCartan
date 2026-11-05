module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MaskDerivative
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoundedSymbols

/-!
# The mask and its first derivatives as bounded multipliers

The only mask bounds used in `app:ch_osc:prop:osc-normal` produce the actual
L∞ symbols on the input domain. Smoothness is needed only on that domain;
neither a global extension nor higher derivative bounds are assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace JanetCartan.NormalComparison

open AmplitudeBound

/-- The coordinate derivatives of the mask are bounded by its differential's
operator norm, as used in `app:ch_osc:prop:osc-normal`. -/
theorem norm_partialDeriv_mask_le {n : ℕ} (m : Euclidean n → ℝ)
    (u : Euclidean n) (j : Fin n) :
    ‖partialDeriv m u j‖ ≤ ‖fderiv ℝ m u‖ := by
  simpa only [partialDeriv, EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] using
    (fderiv ℝ m u).le_opNorm (EuclideanSpace.single j 1)

/-- The exact mask assumptions in `app:ch_osc:prop:osc-normal` yield L∞
representatives of `m` and each `∂ⱼm`, with bounds `1` and `L/h`. Only C¹
regularity on the open input domain is required for this step. -/
theorem exists_mask_derivative_symbols {n : ℕ} {D : Set (Euclidean n)}
    (hD : IsOpen D) (m : Euclidean n → ℝ) (hm : ContDiffOn ℝ 1 m D)
    {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (hmask : ∀ u ∈ D, 0 ≤ m u ∧ m u ≤ 1)
    (hderiv : ∀ u ∈ D, ‖fderiv ℝ m u‖ ≤ L / h) :
    ∃ (g₀ : Lp ℂ ∞ (volume.restrict D))
      (g : Fin n → Lp ℂ ∞ (volume.restrict D)),
      g₀ =ᵐ[volume.restrict D] (fun u ↦ (m u : ℂ)) ∧ ‖g₀‖ ≤ 1 ∧
      (∀ j, g j =ᵐ[volume.restrict D] (fun u ↦ ((partialDeriv m u j : ℝ) : ℂ))) ∧
      ∀ j, ‖g j‖ ≤ L / h := by
  have hm₀ : AEStronglyMeasurable (fun u ↦ (m u : ℂ)) (volume.restrict D) :=
    (Complex.continuous_ofReal.comp_continuousOn hm.continuousOn).aestronglyMeasurable
      hD.measurableSet
  have hmb : ∀ᵐ u ∂volume.restrict D, ‖(m u : ℂ)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with u hu
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hmask u hu).1] using
      (hmask u hu).2
  have hjm (j : Fin n) : AEStronglyMeasurable
      (fun u ↦ ((partialDeriv m u j : ℝ) : ℂ)) (volume.restrict D) := by
    apply ContinuousOn.aestronglyMeasurable _ hD.measurableSet
    apply Complex.continuous_ofReal.comp_continuousOn
    exact (hm.continuousOn_fderiv_of_isOpen hD le_rfl).clm_apply continuousOn_const
  have hjb (j : Fin n) : ∀ᵐ u ∂volume.restrict D,
      ‖((partialDeriv m u j : ℝ) : ℂ)‖ ≤ L / h := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with u hu
    simpa only [Complex.norm_real] using
      (norm_partialDeriv_mask_le m u j).trans (hderiv u hu)
  refine ⟨boundedSymbol _ hm₀ 1 hmb,
    fun j ↦ boundedSymbol _ (hjm j) (L / h) (hjb j),
    boundedSymbol_coeFn _ hm₀ 1 hmb, norm_boundedSymbol_le _ hm₀ 1 hmb zero_le_one,
    fun j ↦ boundedSymbol_coeFn _ (hjm j) (L / h) (hjb j), ?_⟩
  exact fun j ↦ norm_boundedSymbol_le _ (hjm j) (L / h) (hjb j) (div_nonneg hL hh.le)

end JanetCartan.NormalComparison
