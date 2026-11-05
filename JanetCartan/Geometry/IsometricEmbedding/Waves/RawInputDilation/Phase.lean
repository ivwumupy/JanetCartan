module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Representation

/-!
# Physical covectors and the dilated phase

The phase in `app:ch_waves:eq:individual-representation` is evaluated at the
actual physical covector. The shifted quotient rescales algebraically. Its
identification with a physical homogeneous phase requires the explicit positive
homogeneity supplied by the Hamilton-phase construction.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputDilation
open RawInputRealization
variable {n : ℕ} {K τ : ℝ} {X : Type*}

/-- Exact rescaling of the shifted quotient in `app:ch_waves:eq:phase-quotient`.
No homogeneity is needed for this quotient identity: its parameter becomes `τK`. -/
theorem rawPrimaryPhaseDifference_dilate (S : X → Euclidean (n - 1) → ℝ)
    (ζ : Euclidean (n - 1)) (hτ : τ ≠ 0) (hK : 0 < K)
    (x : X) (θ : Euclidean (n - 1)) :
    rawPrimaryPhaseDifference S ζ τ x (K • θ) =
      K * rawPrimaryPhaseDifference S ζ (τ * K) x θ := by
  simp only [rawPrimaryPhaseDifference, smul_smul]
  field_simp

/-- The physical covector is `τ⁻¹ζ + η`. Homogeneity at the physical scale
identifies its phase difference with the shifted quotient of
`app:ch_waves:eq:individual-representation`. Homogeneity is required only on the
specified covector chart `U`, containing the two shifted covectors. -/
theorem physical_phase_eq_rawPrimaryPhaseDifference
    (S : X → Euclidean (n - 1) → ℝ) (ζ : Euclidean (n - 1)) (hτ : 0 < τ)
    (x : X) (η : Euclidean (n - 1)) (U : Set (Euclidean (n - 1)))
    (hS : ∀ ξ ∈ U, S x (τ⁻¹ • ξ) = τ⁻¹ * S x ξ)
    (hζ : ζ ∈ U) (hshift : ζ + τ • η ∈ U) :
    S x (τ⁻¹ • ζ + η) - S x (τ⁻¹ • ζ) =
      rawPrimaryPhaseDifference S ζ τ x η := by
  have he : τ⁻¹ • ζ + η = τ⁻¹ • (ζ + τ • η) := by
    rw [smul_add, inv_smul_smul₀ hτ.ne']
  rw [he, hS _ hshift, hS _ hζ, rawPrimaryPhaseDifference]
  ring

/-- The phase at the actual dilated physical covector in
`app:ch_waves:thm:sampling` is `K φ_{τK}` under the stated chart homogeneity.
The chart conditions refer to the actual carrier and shifted covector. -/
theorem physical_phase_dilate (S : X → Euclidean (n - 1) → ℝ)
    (ζ : Euclidean (n - 1)) (hτ : 0 < τ) (hK : 0 < K)
    (x : X) (θ : Euclidean (n - 1)) (U : Set (Euclidean (n - 1)))
    (hS : ∀ ξ ∈ U, S x (τ⁻¹ • ξ) = τ⁻¹ * S x ξ)
    (hζ : ζ ∈ U) (hshift : ζ + (τ * K) • θ ∈ U) :
    S x (τ⁻¹ • ζ + K • θ) - S x (τ⁻¹ • ζ) =
      K * rawPrimaryPhaseDifference S ζ (τ * K) x θ := by
  rw [physical_phase_eq_rawPrimaryPhaseDifference S ζ hτ x (K • θ) U hS hζ
    (by simpa only [smul_smul] using hshift),
    rawPrimaryPhaseDifference_dilate S ζ hτ.ne' hK]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/-- The normalized raw half-derivative integral, including its `K φ_{τK}` phase
and unchanged physical masks/amplitudes (`app:ch_waves:eq:actual-T`). This
identity uses the literal shifted quotient from the raw-primary representation. -/
theorem normalized_rawPrimary_integral (hn : 1 ≤ n) (hK : 0 < K) (hτ : τ ≠ 0)
    (S : X → Euclidean (n - 1) → ℝ) (ζ : Euclidean (n - 1)) (x : X)
    (β : Euclidean (n - 1) → ℂ) (a : Euclidean (n - 1) → F)
    (f : AnnularL2 n K) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      (∫ η, ((Real.sqrt ‖η‖ : ℂ) *
        (Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℂ)) * β η) *
          f η) • a η ∂annularMeasure n K) =
    NormalComparison.normalOperatorScale n K •
      ∫ θ, ((Real.sqrt ‖θ‖ : ℂ) *
        (NormalComparison.oscillatoryFactor K
          (rawPrimaryPhaseDifference S ζ (τ * K) x θ) * β (K • θ)) *
          annularDilation n K hK f θ) • a (K • θ) ∂annularMeasure n 1 := by
  rw [normalized_halfDerivative_integral hn hK]
  simp only [rawPrimaryPhaseDifference_dilate S ζ hτ hK,
    NormalComparison.oscillatoryFactor, Complex.ofReal_mul]

end JanetCartan.RawInputDilation
