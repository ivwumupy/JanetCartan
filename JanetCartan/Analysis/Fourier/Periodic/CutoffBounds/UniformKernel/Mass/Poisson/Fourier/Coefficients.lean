module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson.Fourier.Descent
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Periodization
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.Realization.Character
public import JanetCartan.Analysis.Fourier.Periodic.Calculus

/-!
# Fourier coefficients of Schwartz periodizations

For `main:lem:smoothing` and `main:eq:smoothing-low`, unfolding the unit cube
identifies torus Fourier coefficients with Euclidean Fourier samples. The
character convention and the measures are the existing normalized ones.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace JanetCartan

variable {n : ℕ}

/-- `main:lem:smoothing`: the negative unit-torus mode is exactly the phase
in the Euclidean Fourier transform at the integer lattice vector. -/
theorem mFourier_neg_torusQuotient_eq_fourierChar (k : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier (-k) (torusQuotient x) =
      (Real.fourierChar (-inner ℝ x (WithLp.toLp 2 (fun i ↦ (k i : ℝ)) :
        EuclideanSpace ℝ (Fin n))) : ℂ) := by
  rw [mFourier_torusQuotient_eq_fourierChar]
  have he : (WithLp.toLp 2 (fun i ↦ ((-k) i : ℝ)) : EuclideanSpace ℝ (Fin n)) =
      -WithLp.toLp 2 (fun i ↦ (k i : ℝ)) := by ext i; simp
  rw [he, inner_neg_right]

/-- `main:lem:smoothing`: the Fourier coefficients of the continuous Schwartz
periodization are its Euclidean Fourier transform sampled on the unit lattice. -/
theorem mFourierCoeff_schwartzTorusPeriodization
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization f) k =
      𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ)
        (WithLp.toLp 2 (fun i ↦ (k i : ℝ))) := by
  let g : EuclideanSpace ℝ (Fin n) → ℂ := fun x ↦
    UnitAddTorus.mFourier (-k) (torusQuotient x) * f x
  have hg : Integrable g := by
    simp only [g, mFourier_neg_torusQuotient_eq_fourierChar,
      ← smul_eq_mul, ← Circle.smul_def]
    exact (Real.fourierIntegral_convergent_iff _).mpr f.integrable
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (0 : Fin n → ℝ)]
  simp only [Pi.zero_apply, zero_add]
  change (∫ x in unitLatticeIocCube n,
    UnitAddTorus.mFourier (-k) (torusQuotient (WithLp.toLp 2 x)) *
      schwartzTorusPeriodization f (torusQuotient (WithLp.toLp 2 x))) = _
  calc
    _ = ∫ x in unitLatticeIocCube n, ∑' m : Fin n → ℤ,
        g (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [schwartzTorusPeriodization_torusQuotient, schwartzLatticePeriodization]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      dsimp only [g]
      rw [show torusQuotient (WithLp.toLp 2 x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) =
        torusQuotient (WithLp.toLp 2 x) from torusQuotient_add_integerTranslation _ m]
    _ = ∫ x, g x := integral_unitLatticeIocCube_tsum g hg
    _ = _ := by
      simp only [g, mFourier_neg_torusQuotient_eq_fourierChar, Real.fourier_eq,
        Circle.smul_def, smul_eq_mul]

end JanetCartan
