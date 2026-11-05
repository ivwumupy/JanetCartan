module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.Amplitude

/-!
# The unreflected amplitude for complex-normal comparison

`norm_augmentedNormal_sub_le_channel_normals` consumes complex normal
differences. Their amplitude is the unreflected full amplitude, whereas the
published real-normal realization uses the reflected amplitude. These shared
definitions fix the physical-frequency normalization for the independent
amplitude estimate and operator-identification deductions. No reverse bound
from a real compression to an arbitrary complex difference is asserted.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation
open ContinuumNormalReduction TransportSymbol ContinuumRow CarrierNormalRealization
open TransportKernel Pseudodifferential AmplitudeBound
variable {n N : ℕ}

/-- The full complex normal amplitude, before reflection, in the same paired
PDO coordinates and with physical frequency `k = 2πξ`. The multiplier
`(2π)^n` is the change of frequency measure, with no quadrature factor.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
def fullComplexMatrixAmplitude
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (ξ : Euclidean n) (z : Euclidean (2 * n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ (((2 * Real.pi) ^ n * amplitude a J u Ω S
    (freezingOutputProjection z, freezingSourceProjection z, (2 * Real.pi) • ξ) i j : ℝ) : ℂ)

/-- Exact two-position coordinates for the unreflected full amplitude.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
@[simp] theorem fullComplexMatrixAmplitude_pairedPosition
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (x y ξ : Euclidean n) (i j : Fin n) :
    fullComplexMatrixAmplitude a J u Ω S ξ (pairedPosition x y) i j =
      (((2 * Real.pi) ^ n * amplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℝ) : ℂ) := by
  simp [fullComplexMatrixAmplitude]

/-- Reflection contributes twice the sum of the two unreflected amplitudes.
Thus the real quadrature factor four is already in `fullReflectedMatrixAmplitude`;
it must not be applied again to its operator bound.
Source: `app:ch_background:eq:bg-real-symbol`. -/
theorem fullReflectedMatrixAmplitude_eq_complex_add_reflection
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (ξ : Euclidean n) (z : Euclidean (2 * n)) :
    fullReflectedMatrixAmplitude a J u Ω S ξ z =
      (2 : ℂ) • (fullComplexMatrixAmplitude a J u Ω S ξ z +
        fullComplexMatrixAmplitude a J u Ω S (-ξ) z) := by
  ext i j
  simp only [fullReflectedMatrixAmplitude, fullComplexMatrixAmplitude,
    reflectedSymbolAmplitude, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul, smul_neg, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

/-- The unreflected amplitude keeps both original measurement supports; no
additional localization is introduced for the complex-normal estimate.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem fullComplexMatrixAmplitude_supportedInCenteredBox
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (R : ℝ) (hs : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ R)
    (ξ : Euclidean n) (i j : Fin n) :
    SupportedInCenteredBox R (fun z ↦ fullComplexMatrixAmplitude a J u Ω S ξ z i j) := by
  intro z hz k
  have hzero (x y k : Euclidean n) (hxy : a.measurement x = 0 ∨ a.measurement y = 0) :
      amplitude a J u Ω S (x, y, k) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with v
    by_cases hv : ((x, y, k), v) ∈ Ω
    · rcases hxy with hx | hy <;>
        simp [extendedDensity, inputDensity, inputWeight, inverseCoordinates, *]
    · simp [extendedDensity, hv]
  have hx : a.measurement (freezingOutputProjection z) ≠ 0 := by
    intro he
    simp [fullComplexMatrixAmplitude, hzero _ _ _ (Or.inl he)] at hz
  have hy : a.measurement (freezingSourceProjection z) ≠ 0 := by
    intro he
    simp [fullComplexMatrixAmplitude, hzero _ _ _ (Or.inr he)] at hz
  by_cases hk : k.val < n
  · exact hs _ hx ⟨k.val, hk⟩
  · simpa [freezingSourceProjection, show n + (k.val - n) = k.val by omega] using
      hs _ hy ⟨k.val - n, by omega⟩

end JanetCartan.ContinuumNormal.CarrierVariation
