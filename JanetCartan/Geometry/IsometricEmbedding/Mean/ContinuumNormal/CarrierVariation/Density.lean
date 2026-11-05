module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds.InitialMultiplier

/-!
# The two transported initial-density factors

The density perturbation in `app:ch_background:prop:bg-frame` enters at both
physical positions. These identities retain the literal normal factors, masks,
Jacobian and reduced covectors. The small-density estimate is a pointwise
prerequisite for the finite mixed-jet estimate, not an operator estimate.
The original wider density class is not reduced to a small neighborhood here.
-/

@[expose] public noncomputable section
open Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation
open ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- The actual normal density contains the square of the initial amplitude
at each of the two footpoints. Source:
`app:ch_background:eq:bg-full-complex-amplitude`, `app:ch_background:eq:bg-T`. -/
theorem inputDensity_withInitialMultiplier
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n) :
    inputDensity (withInitialMultiplier a r Y) J p =
      (r (p.2.1, Y (p.1.1, p.2.1)) ^ 2 * r (p.2.1, Y (p.1.2, p.2.1)) ^ 2) •
        inputDensity a J p := by
  ext i j
  simp only [inputDensity, inputWeight, withInitialMultiplier, initialWeightedNormal,
    Matrix.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- For initial amplitude `sqrt (1+v)`, the literal density factors are
`(1+v(z,Y(x,z)))(1+v(z,Y(y,z)))`. Positivity is required only at those genuine
footpoints; no assumption on the resulting amplitude is used.
Source: `app:ch_background:prop:bg-frame` and `app:ch_background:eq:bg-T`. -/
theorem inputDensity_sqrtDensity
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (v : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n)
    (hl : 0 ≤ 1 + v (p.2.1, Y (p.1.1, p.2.1)))
    (hr : 0 ≤ 1 + v (p.2.1, Y (p.1.2, p.2.1))) :
    inputDensity (withInitialMultiplier a (fun q ↦ Real.sqrt (1 + v q)) Y) J p =
      ((1 + v (p.2.1, Y (p.1.1, p.2.1))) *
        (1 + v (p.2.1, Y (p.1.2, p.2.1)))) • inputDensity a J p := by
  rw [inputDensity_withInitialMultiplier, Real.sq_sqrt hl, Real.sq_sqrt hr]

/-- Exact difference of the two-position transported densities, including the
quadratic cross term. This identity is the algebraic input to the small-density
jet estimate; replacing it by a single density factor would lose a contribution.
Source: `app:ch_background:prop:bg-frame`. -/
theorem inputDensity_sqrtDensity_sub
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (v : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n)
    (hl : 0 ≤ 1 + v (p.2.1, Y (p.1.1, p.2.1)))
    (hr : 0 ≤ 1 + v (p.2.1, Y (p.1.2, p.2.1))) :
    inputDensity (withInitialMultiplier a (fun q ↦ Real.sqrt (1 + v q)) Y) J p -
      inputDensity a J p =
      (v (p.2.1, Y (p.1.1, p.2.1)) + v (p.2.1, Y (p.1.2, p.2.1)) +
        v (p.2.1, Y (p.1.1, p.2.1)) * v (p.2.1, Y (p.1.2, p.2.1))) •
          inputDensity a J p := by
  rw [inputDensity_sqrtDensity a J v Y p hl hr]
  conv_lhs => arg 2; rw [← one_smul ℝ (inputDensity a J p)]
  rw [← sub_smul]
  congr 1
  ring

/-- Zeroth-order small-density dependence is linear plus quadratic in the
primitive scalar tolerance. The unchanged literal density carries all masks,
normal factors and Jacobian division. Source: `app:ch_background:prop:bg-frame`.
This is not the finite-jet or normal-operator estimate. -/
theorem norm_inputDensity_sqrtDensity_sub_le
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (v : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n) {ε : ℝ} (hε : 0 ≤ ε)
    (hl : 0 ≤ 1 + v (p.2.1, Y (p.1.1, p.2.1)))
    (hr : 0 ≤ 1 + v (p.2.1, Y (p.1.2, p.2.1)))
    (hvl : |v (p.2.1, Y (p.1.1, p.2.1))| ≤ ε)
    (hvr : |v (p.2.1, Y (p.1.2, p.2.1))| ≤ ε) :
    ‖inputDensity (withInitialMultiplier a (fun q ↦ Real.sqrt (1 + v q)) Y) J p -
      inputDensity a J p‖ ≤ (2 * ε + ε ^ 2) * ‖inputDensity a J p‖ := by
  rw [inputDensity_sqrtDensity_sub a J v Y p hl hr, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ |v (p.2.1, Y (p.1.1, p.2.1))| + |v (p.2.1, Y (p.1.2, p.2.1))| +
        |v (p.2.1, Y (p.1.1, p.2.1))| * |v (p.2.1, Y (p.1.2, p.2.1))| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_of_eq (abs_mul _ _)))
    _ ≤ ε + ε + ε * ε :=
      add_le_add (add_le_add hvl hvr) (mul_le_mul hvl hvr (abs_nonneg _) hε)
    _ = _ := by ring

/-- The same two density factors persist after inverse substitution and
literal zero extension. This supplies the density-only branch of the full
amplitude comparison across the common chart boundary.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem extendedDensity_sqrtDensity_sub
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (v : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2))
    (hv : ∀ p ∈ Ω,
      0 ≤ 1 + v ((inverseCoordinates u p).2.1,
        Y ((inverseCoordinates u p).1.1, (inverseCoordinates u p).2.1)) ∧
      0 ≤ 1 + v ((inverseCoordinates u p).2.1,
        Y ((inverseCoordinates u p).1.2, (inverseCoordinates u p).2.1)))
    (p : Variables n × Euclidean 2) :
    extendedDensity (withInitialMultiplier a (fun q ↦ Real.sqrt (1 + v q)) Y) J u Ω p -
      extendedDensity a J u Ω p =
      (let q := inverseCoordinates u p
       v (q.2.1, Y (q.1.1, q.2.1)) + v (q.2.1, Y (q.1.2, q.2.1)) +
         v (q.2.1, Y (q.1.1, q.2.1)) * v (q.2.1, Y (q.1.2, q.2.1))) •
           extendedDensity a J u Ω p := by
  classical
  by_cases hp : p ∈ Ω
  · simpa only [extendedDensity, indicator_of_mem hp] using
      inputDensity_sqrtDensity_sub a J v Y (inverseCoordinates u p) (hv p hp).1 (hv p hp).2
  · simp [extendedDensity, hp]

end JanetCartan.ContinuumNormal.CarrierVariation
