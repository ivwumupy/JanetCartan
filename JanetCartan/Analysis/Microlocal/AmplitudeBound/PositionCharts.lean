module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Modulations
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.SmoothCoefficients

/-!
# The two physical positions on the auxiliary torus

Separate the two physical positions into the first and last `d` coordinates of
the unit torus in `app:ch_osc:lem:osc-amplitude`. The resulting characters factor
as the left and right modulations in the operator series.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.AmplitudeBound

variable {d : ℕ}

/-- First physical position in the larger torus of `app:ch_osc:lem:osc-amplitude`. -/
def leftPositionChart (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : Torus (2 * d) :=
  fun i ↦ if hi : i.val < d then scaledTorusChart ℓ x ⟨i.val, hi⟩ else 0

/-- Second physical position in the larger torus of `app:ch_osc:lem:osc-amplitude`. -/
def rightPositionChart (ℓ : ℝ) (y : EuclideanSpace ℝ (Fin d)) : Torus (2 * d) :=
  fun i ↦ if hi : i.val < d then 0 else scaledTorusChart ℓ y ⟨i.val - d, by omega⟩

/-- Measurability of the first physical chart (`app:ch_osc:lem:osc-amplitude`). -/
theorem measurable_leftPositionChart (ℓ : ℝ) :
    Measurable (leftPositionChart (d := d) ℓ) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i.val < d
  · simpa only [leftPositionChart, dite_eq_left hi, Function.comp_def] using
      (measurable_pi_apply ⟨i.val, hi⟩).comp (measurable_scaledTorusChart ℓ)
  · simp only [leftPositionChart, dite_eq_right hi]
    exact measurable_const

/-- Measurability of the second physical chart (`app:ch_osc:lem:osc-amplitude`). -/
theorem measurable_rightPositionChart (ℓ : ℝ) :
    Measurable (rightPositionChart (d := d) ℓ) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i.val < d
  · simp only [rightPositionChart, dite_eq_left hi]
    exact measurable_const
  · simpa only [rightPositionChart, dite_eq_right hi, Function.comp_def] using
      (measurable_pi_apply ⟨i.val - d, by omega⟩).comp (measurable_scaledTorusChart ℓ)

/-- Factorization of a two-position Fourier character into the physical
modulations in `app:ch_osc:lem:osc-amplitude`. -/
theorem mFourier_apply_add (k : Fin (2 * d) → ℤ) (x y : Torus (2 * d)) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp [UnitAddTorus.mFourier, fourier_apply,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- Exact two-position expansion of the cutoff amplitude in
`app:ch_osc:lem:osc-amplitude`. No coefficient bound is assumed: it follows from
the physical derivatives. -/
theorem hasSum_cutoff_twoPosition_expansion (hd : 0 < d)
    {f : Torus (2 * d) → ℂ} (hf : IsSmoothPeriodic f) {A : ℝ}
    (hzero : ∀ z, ‖f z‖ ≤ A)
    (hderiv : ∀ i z,
      ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) f z‖ ≤ A)
    (ℓ : ℝ) (χ ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    HasSum (fun k ↦ (χ x * UnitAddTorus.mFourier k (leftPositionChart ℓ x)) *
      UnitAddTorus.mFourierCoeff f k *
      (ψ y * UnitAddTorus.mFourier k (rightPositionChart ℓ y)))
      (χ x * f (leftPositionChart ℓ x + rightPositionChart ℓ y) * ψ y) := by
  convert ((hasSum_mFourierCoeff_of_twoPosition_derivatives hd hf hzero hderiv
    (leftPositionChart ℓ x + rightPositionChart ℓ y)).mul_left (χ x)).mul_right (ψ y) using 1
  funext k
  rw [mFourier_apply_add]
  ring

end JanetCartan.AmplitudeBound
