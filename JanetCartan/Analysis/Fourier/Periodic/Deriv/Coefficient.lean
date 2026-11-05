module
public import JanetCartan.Analysis.Fourier.Periodic.Deriv.Coordinate
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
/-!
# Translation and differentiation of torus Fourier coefficients

The normalized unit-torus identities underlying paper.tex, `app:not:fourier`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace JanetCartan
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {n : ℕ}
/-- The Fourier characters have unit modulus (`app:not:fourier`). -/
lemma periodicFourierCharacter_norm (k : Fin n → ℤ) (x : Torus n) : ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp [UnitAddTorus.mFourier, fourier_apply, norm_prod]
/-- The Fourier characters intertwine addition and multiplication (`app:not:fourier`). -/
lemma periodicFourierCharacter_add (k : Fin n → ℤ) (x y : Torus n) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp [UnitAddTorus.mFourier, fourier_apply, smul_add, AddCircle.toCircle_add,
    Finset.prod_mul_distrib]
private lemma mFourier_single_coordinate (k : Fin n → ℤ) (i : Fin n) (t : ℝ) :
    UnitAddTorus.mFourier k (Pi.single i (t : AddCircle (1 : ℝ))) =
      fourier (k i) (t : AddCircle (1 : ℝ)) := by
  classical
  change (∏ j, fourier (k j) (((Pi.single i (t : AddCircle (1 : ℝ))) : Torus n) j)) = _
  rw [Finset.prod_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro j _ hj
    simp only [Pi.single_eq_of_ne hj, fourier_eval_zero]
  · simp
/-- Translation multiplies a Fourier coefficient by its character (`app:not:fourier`). -/
theorem mFourierCoeff_translate (f : Torus n → ℂ) (k : Fin n → ℤ) (y : Torus n) :
    UnitAddTorus.mFourierCoeff (fun x ↦ f (x + y)) k =
      UnitAddTorus.mFourier k y * UnitAddTorus.mFourierCoeff f k := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  rw [← integral_add_right_eq_self (fun x ↦ UnitAddTorus.mFourier (-k) x * f x) y,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [periodicFourierCharacter_add, UnitAddTorus.mFourier_neg (x := y)]
  have h : UnitAddTorus.mFourier k y * starRingEnd ℂ (UnitAddTorus.mFourier k y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, periodicFourierCharacter_norm]
    norm_num
  calc
    _ = (UnitAddTorus.mFourier k y * starRingEnd ℂ (UnitAddTorus.mFourier k y)) *
        (UnitAddTorus.mFourier (-k) x * f (x + y)) := by rw [h, one_mul]
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- Differentiation multiplies the coefficient by `2π i kᵢ` (`app:not:fourier`).
The derivative assumption is the ordinary pointwise derivative along coordinate translations. -/
theorem mFourierCoeff_of_hasDerivAt_coordinate {f g : Torus n → ℂ} (hf : Continuous f) (hg : Continuous g)
    (i : Fin n)
    (hd : ∀ (x : Torus n) (t : ℝ), HasDerivAt (fun s : ℝ ↦ f (x + Pi.single i (s : AddCircle (1 : ℝ))))
      (g (x + Pi.single i (t : AddCircle (1 : ℝ)))) t)
    (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff g k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) * UnitAddTorus.mFourierCoeff f k := by
  classical
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hcont (t : ℝ) : Continuous (fun x : Torus n ↦
      UnitAddTorus.mFourier (-k) x * f (x + Pi.single i (t : AddCircle (1 : ℝ)))) := by
    exact (UnitAddTorus.mFourier (-k)).continuous.mul (hf.comp (continuous_id.add continuous_const))
  have hgcont (t : ℝ) : Continuous (fun x : Torus n ↦
      UnitAddTorus.mFourier (-k) x * g (x + Pi.single i (t : AddCircle (1 : ℝ)))) := by
    exact (UnitAddTorus.mFourier (-k)).continuous.mul (hg.comp (continuous_id.add continuous_const))
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Torus n))) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun (t : ℝ) (x : Torus n) ↦ UnitAddTorus.mFourier (-k) x * f (x + Pi.single i (t : AddCircle (1 : ℝ))))
    (F' := fun (t : ℝ) (x : Torus n) ↦ UnitAddTorus.mFourier (-k) x * g (x + Pi.single i (t : AddCircle (1 : ℝ))))
    (bound := fun _ ↦ C) (by simp)
    (Eventually.of_forall fun t ↦ (hcont t).aestronglyMeasurable)
    ((hcont 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hgcont 0).aestronglyMeasurable)
    (Eventually.of_forall fun x t _ ↦ by
      rw [norm_mul, periodicFourierCharacter_norm, one_mul]
      exact hC _ (Set.mem_univ _))
    (integrable_const C)
    (Eventually.of_forall fun x t _ ↦ (hd x t).const_mul _)
  have heq (t : ℝ) :
      (∫ x : Torus n, UnitAddTorus.mFourier (-k) x *
        f (x + Pi.single i (t : AddCircle (1 : ℝ)))) =
      fourier (k i) (t : AddCircle (1 : ℝ)) * UnitAddTorus.mFourierCoeff f k := by
    simpa only [UnitAddTorus.mFourierCoeff, smul_eq_mul, mFourier_single_coordinate] using
      mFourierCoeff_translate f k (Pi.single i (t : AddCircle (1 : ℝ)))
  have hleft : HasDerivAt (fun t : ℝ ↦
      fourier (k i) (t : AddCircle (1 : ℝ)) * UnitAddTorus.mFourierCoeff f k)
      (UnitAddTorus.mFourierCoeff g k) 0 := by
    simpa only [heq, AddCircle.coe_zero, Pi.single_zero, add_zero,
      UnitAddTorus.mFourierCoeff, smul_eq_mul] using hint.2
  have hright := (hasDerivAt_fourier 1 (k i) 0).mul_const (UnitAddTorus.mFourierCoeff f k)
  simpa using hleft.unique hright
end JanetCartan

