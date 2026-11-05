module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Basic

/-!
# Exact degree-zero cancellation and the homogeneous diagonal

The algebraic part of Step 1 of `app:ch_background:prop:bg-frame`.
Only the geometric inverse and Jacobian scaling identities are inputs; the
normal amplitude's homogeneity is a conclusion. All masks and spectators are
retained. Estimates for derivatives and low-frequency completion are separate.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Positive radial dilation of the output covector, keeping both positions.
Source: `app:ch_background:eq:bg-symbol`. -/
def scaleFrequency (t : ℝ) (p : Variables n) : Variables n := (p.1, p.2.1, t • p.2.2)

/-- Positive radial dilation of the original transverse covector.
Source: `app:ch_background:eq:bg-jacobian`. -/
def scaleInput (t : ℝ) (p : InputVariables n) : InputVariables n :=
  (p.1, p.2.1, t • p.2.2)

/-- Angular normalization is unchanged by positive radial scaling, including
at zero under Lean's total inverse convention. The conic use is away from zero.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem direction_pos_smul {t : ℝ} (ht : 0 < t) (η : Euclidean (n - 1)) :
    ‖t • η‖⁻¹ • (t • η) = ‖η‖⁻¹ • η := by
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv_rev, smul_smul,
    ht.ne']

/-- The transverse norm cancels exactly the degree-one Jacobian, including
all the primitive factors of the homogeneous normal density. Source:
`app:ch_background:eq:bg-jacobian` and `app:ch_background:eq:bg-symbol`. -/
theorem inputDensity_homogeneous (a : Coefficients n N) (J : InputVariables n → ℝ)
    {t : ℝ} (ht : 0 < t) (p : InputVariables n)
    (hJ : J (scaleInput t p) = t * J p) :
    inputDensity (homogeneousCoefficients a) J (scaleInput t p) =
      inputDensity (homogeneousCoefficients a) J p := by
  have hnorm : ‖t • p.2.2‖ = t * ‖p.2.2‖ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hweight : inputWeight (homogeneousCoefficients a) J (scaleInput t p) =
      inputWeight (homogeneousCoefficients a) J p := by
    simp only [inputWeight, homogeneousCoefficients, one_pow, mul_one]
    dsimp only [scaleInput] at hJ ⊢
    rw [direction_pos_smul ht, hJ, hnorm]
    by_cases hj : J p = 0
    · simp [hj]
    · field_simp
  exact congrArg (fun w ↦ w • Matrix.vecMulVec (a.reduced (p.1.1, p.2.1))
    (a.reduced (p.1.2, p.2.1))) hweight

/-- The zero-extended homogeneous density is degree zero when the output
chart, the actual inverse and the absolute Jacobian have the stated conic
scaling identities. Source: `app:ch_background:eq:bg-symbol`. -/
theorem extendedDensity_homogeneous
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) {t : ℝ} (ht : 0 < t)
    (hΩ : ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hu : ∀ p ∈ Ω, u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJ : ∀ p ∈ Ω, J (scaleInput t (inverseCoordinates u p)) =
      t * J (inverseCoordinates u p)) (p : Variables n × Euclidean 2) :
    extendedDensity (homogeneousCoefficients a) J u Ω (scaleFrequency t p.1, p.2) =
      extendedDensity (homogeneousCoefficients a) J u Ω p := by
  by_cases hp : p ∈ Ω
  · have he : inverseCoordinates u (scaleFrequency t p.1, p.2) =
        scaleInput t (inverseCoordinates u p) := by
      simp only [inverseCoordinates, hu p hp]
      rfl
    simp only [extendedDensity, indicator_of_mem hp, indicator_of_mem ((hΩ p).mpr hp), he]
    exact inputDensity_homogeneous a J ht _ (hJ p hp)
  · simp [extendedDensity, hp, (hΩ p).not.mpr hp]

/-- Integration over the literal spectator measure preserves the exact
homogeneity. This is an identity, not a symbol estimate or operator bound.
Source: `app:ch_background:eq:bg-symbol`. -/
theorem amplitude_homogeneous
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    {t : ℝ} (ht : 0 < t)
    (hΩ : ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hu : ∀ p ∈ Ω, u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJ : ∀ p ∈ Ω, J (scaleInput t (inverseCoordinates u p)) =
      t * J (inverseCoordinates u p)) (p : Variables n) :
    amplitude (homogeneousCoefficients a) J u Ω K (scaleFrequency t p) =
      amplitude (homogeneousCoefficients a) J u Ω K p := by
  apply integral_congr_ae
  filter_upwards [] with v
  exact extendedDensity_homogeneous a J u Ω ht hΩ hu hJ (p, v)

/-- The homogeneous diagonal in the paper is degree zero, with no evenness
assumption on the angular mask. Its geometric instantiation is for `k ≠ 0`.
Source: `app:ch_background:eq:bg-symbol`. -/
theorem homogeneousDiagonal_pos_smul
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    {t : ℝ} (ht : 0 < t)
    (hΩ : ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hu : ∀ p ∈ Ω, u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJ : ∀ p ∈ Ω, J (scaleInput t (inverseCoordinates u p)) =
      t * J (inverseCoordinates u p)) (x k : Euclidean n) :
    homogeneousDiagonal a J u Ω K x (t • k) = homogeneousDiagonal a J u Ω K x k :=
  amplitude_homogeneous a J u Ω K ht hΩ hu hJ (x, x, k)

end JanetCartan.ContinuumNormalReduction.TransportSymbol
