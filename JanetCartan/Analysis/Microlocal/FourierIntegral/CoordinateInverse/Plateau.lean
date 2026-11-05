module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.RightMultiplier

/-!
# Fourier plateaux for the weighted coordinate inverse

The operator cancellation in Step 4 of `app:ch_regular_base:thm:actual-calculus`.
The inverse averaged-gradient chart is supplied by phase geometry. Physical
covectors are `2π • ξ` in the unit-frequency PDO API. All integrals use Euclidean
Lebesgue measure. No periodic data identification is made here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace JanetCartan.FourierIntegral.CoordinateInverse

variable {n r : ℕ}

/-- The uncut `V₀` from `app:ch_regular_base:eq:actual-matrix-inverse`, using
the shared weighted reverse graph and its original normalization. -/
def reverseCore (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg : Euclidean n → ℝ) (f : Euclidean n → Fin r → ℂ) :=
  weightedReverseGraph S U (fun _ ↦ 1) (fun _ ↦ 1) χg f

/-- Both physical positions remain in `V = χs V₀ χt`
(`app:ch_regular_base:eq:actual-matrix-inverse`). -/
theorem weightedReverseGraph_eq_cut_reverseCore
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (f : Euclidean n → Fin r → ℂ)
    (y : Euclidean n) :
    weightedReverseGraph S U χs χt χg f y =
      (χs y : ℂ) • reverseCore S U χg (fun x ↦ (χt x : ℂ) • f x) y := by
  simp [reverseCore, weightedReverseGraph]

/-- The diagonal scalar factor in unit Fourier frequencies after the actual
inverse averaged-gradient change (`app:ch_regular_base:eq:actual-right-inverse`). -/
def principalSymbol (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (χg : Euclidean n → ℝ) (x ξ : Euclidean n) : ℂ :=
  (χg (η x x ((2 * Real.pi) • ξ)) : ℂ) ^ 2

/-- The weighted matrix cancellation retains the square of the graph cutoff,
as required in Step 4 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem weighted_diagonal_eq_principal (j : ℝ) (hj : j ≠ 0)
    (U : Matrix (Fin r) (Fin r) ℂ) (hU : IsUnit U.det) (χ : ℝ) :
    (j : ℂ)⁻¹ • (((χ : ℂ) • U) * ((χ : ℂ) • reverseWeight j U)) =
      (χ : ℂ) ^ 2 • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  rw [Matrix.smul_mul, Matrix.mul_smul,
    smul_comm (j : ℂ)⁻¹ (χ : ℂ), smul_comm (j : ℂ)⁻¹ (χ : ℂ),
    weighted_principal_amplitude j hj U hU, smul_smul, pow_two]

/-- Exact PDO cancellation on a Fourier plateau; the hypothesis concerns only
the symbol on the multiplier support, not the operator inverse.
Consumer: `app:ch_regular_base:eq:actual-right-inverse`. -/
theorem principalOperator_frequency_plateau
    (a : Euclidean n → Euclidean n → ℂ) (q : Euclidean n → ℂ)
    (hq : q.HasTemperateGrowth) (ha : ∀ x ξ, q ξ ≠ 0 → a x ξ = 1)
    (u : 𝓢(Euclidean n, ℂ)) (x : Euclidean n) :
    Pseudodifferential.sourceIndependentOperator a
      (Pseudodifferential.schwartzFrequencyMultiplier q u) x =
        Pseudodifferential.schwartzFrequencyMultiplier q u x := by
  rw [Pseudodifferential.sourceIndependentOperator_schwartzFrequencyMultiplier a q hq,
    Pseudodifferential.schwartzFrequencyMultiplier_eq_sourceIndependentOperator q hq]
  congr 1
  funext z ξ
  by_cases h : q ξ = 0
  · simp [h]
  · simp [ha z ξ h]

/-- The actual `χg(η(x,x,2πξ))² I` principal operator is the identity on the
inner Fourier plateau, componentwise for matrix-valued data.
Source: `app:ch_regular_base:eq:actual-right-inverse`. -/
theorem weighted_principalOperator_frequency_plateau
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (χg : Euclidean n → ℝ) (q : Euclidean n → ℂ)
    (hq : q.HasTemperateGrowth)
    (hplateau : ∀ x ξ, q ξ ≠ 0 → χg (η x x ((2 * Real.pi) • ξ)) = 1)
    (u : Fin r → 𝓢(Euclidean n, ℂ)) (x : Euclidean n) (i : Fin r) :
    Pseudodifferential.sourceIndependentOperator (principalSymbol η χg)
      (Pseudodifferential.schwartzFrequencyMultiplier q (u i)) x =
        Pseudodifferential.schwartzFrequencyMultiplier q (u i) x := by
  apply principalOperator_frequency_plateau _ q hq _ (u i) x
  intro z ξ h
  simp [principalSymbol, hplateau z ξ h]

/-- The plateau is needed only on the inner physical evaluation set. This is
the localized principal cancellation consumed by the complete inverse ledger
in `app:ch_regular_base:eq:actual-right-inverse`. -/
theorem weighted_principalOperator_inner_plateau
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (χg χe : Euclidean n → ℝ) (q : Euclidean n → ℂ)
    (hq : q.HasTemperateGrowth)
    (hplateau : ∀ x ξ, χe x ≠ 0 → q ξ ≠ 0 →
      χg (η x x ((2 * Real.pi) • ξ)) = 1)
    (u : 𝓢(Euclidean n, ℂ)) (x : Euclidean n) :
    (χe x : ℂ) * Pseudodifferential.sourceIndependentOperator (principalSymbol η χg)
      (Pseudodifferential.schwartzFrequencyMultiplier q u) x =
        (χe x : ℂ) * Pseudodifferential.schwartzFrequencyMultiplier q u x := by
  by_cases he : χe x = 0
  · simp [he]
  congr 1
  rw [Pseudodifferential.sourceIndependentOperator_schwartzFrequencyMultiplier _ q hq,
    Pseudodifferential.schwartzFrequencyMultiplier_eq_sourceIndependentOperator q hq]
  unfold Pseudodifferential.sourceIndependentOperator
  apply congrArg (fun f : Euclidean n → ℂ ↦ 𝓕⁻ f x)
  funext ξ
  by_cases hqξ : q ξ = 0
  · simp [hqξ]
  · simp [principalSymbol, hplateau x ξ he hqξ]

/-- The canonical Fourier density of `V₀` before inverse transformation,
in unit-frequency coordinates. The physical covector in its weight and phase
is `2πξ` (`app:ch_regular_base:eq:actual-matrix-inverse`). -/
def reverseFourierDensity (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg : Euclidean n → ℝ) (f : Euclidean n → Fin r → ℂ)
    (ξ : Euclidean n) : Fin r → ℂ :=
  (χg ((2 * Real.pi) • ξ) : ℂ) •
    ∫ x, Complex.exp (-Complex.I * (S x ((2 * Real.pi) • ξ) : ℂ)) •
      (reverseWeight (phaseJacobian S x ((2 * Real.pi) • ξ))
        (U x ((2 * Real.pi) • ξ))).mulVec (f x)

/-- The actual canonical density vanishes off the graph cutoff. No
integrability premise is needed for this support statement.
Source: `app:ch_regular_base:eq:source-cut-normal`. -/
theorem reverseFourierDensity_eq_zero
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg : Euclidean n → ℝ) (f : Euclidean n → Fin r → ℂ)
    (ξ : Euclidean n) (h : χg ((2 * Real.pi) • ξ) = 0) :
    reverseFourierDensity S U χg f ξ = 0 := by
  simp [reverseFourierDensity, h]

/-- `Πin V₀ = V₀` follows from the actual Fourier density and the larger
canonical plateau, rather than being an assumed operator identity.
The analytic producer must identify the Fourier transform of each realized
component with this density. Source: `app:ch_regular_base:eq:source-cut-normal`. -/
theorem reverseCore_frequency_plateau
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg : Euclidean n → ℝ) (f : Euclidean n → Fin r → ℂ)
    (q : Euclidean n → ℂ) (hq : q.HasTemperateGrowth)
    (hplateau : ∀ ξ, χg ((2 * Real.pi) • ξ) ≠ 0 → q ξ = 1)
    (v : Fin r → 𝓢(Euclidean n, ℂ))
    (hfourier : ∀ i ξ, (𝓕 (v i) : 𝓢(Euclidean n, ℂ)) ξ =
      reverseFourierDensity S U χg f ξ i) (i : Fin r) :
    Pseudodifferential.schwartzFrequencyMultiplier q (v i) = v i := by
  apply (FourierTransform.fourierEquiv ℂ 𝓢(Euclidean n, ℂ)).injective
  simp only [FourierTransform.fourierEquiv_apply]
  ext ξ
  rw [Pseudodifferential.fourier_schwartzFrequencyMultiplier q hq, hfourier]
  by_cases h : χg ((2 * Real.pi) • ξ) = 0
  · simp [reverseFourierDensity_eq_zero S U χg f ξ h]
  · simp [hplateau ξ h]

end JanetCartan.FourierIntegral.CoordinateInverse
