module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.Amplitude
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Basic

/-!
# Common measurement restriction of the full amplitude

Both physical positions, the inverse-chart indicator, spectator Lebesgue
measure, frequency normalization, and the existing quadrature factor are
retained in `app:ch_background:eq:bg-full-complex-amplitude` and `bg-real-symbol`.
These identities supply the full-normal restriction used by `jc-continuum-row`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped FourierTransform Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CommonMeasurement
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
  Pseudodifferential ContinuumNormal AmplitudeBound
variable {n N : ℕ}

/-- Restrict only the physical measurement coefficient
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def restrictCoefficients (a : Coefficients n N) (χ : Euclidean n → ℝ) : Coefficients n N :=
  { a with measurement := fun x ↦ χ x * a.measurement x }

/-- Both measurement positions enter the original density, with the same
Jacobian and original carrier variables (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem inputDensity_restrictCoefficients (a : Coefficients n N) (χ : Euclidean n → ℝ)
    (J : InputVariables n → ℝ) (p : InputVariables n) :
    inputDensity (restrictCoefficients a χ) J p =
      (χ p.1.1 * χ p.1.2) • inputDensity a J p := by
  ext i j
  simp only [inputDensity, inputWeight, restrictCoefficients, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Restriction retains the ORIGINAL inverse-chart indicator
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem extendedDensity_restrictCoefficients (a : Coefficients n N) (χ : Euclidean n → ℝ)
    (J : InputVariables n → ℝ) (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (p : Variables n × Euclidean 2) :
    extendedDensity (restrictCoefficients a χ) J u Ω p =
      (χ p.1.1 * χ p.1.2.1) • extendedDensity a J u Ω p := by
  classical
  by_cases hp : p ∈ Ω
  · simpa only [extendedDensity, indicator_of_mem hp, inverseCoordinates] using
      inputDensity_restrictCoefficients a χ J (inverseCoordinates u p)
  · simp [extendedDensity, hp]

/-- The original spectator integration is unchanged
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem amplitude_restrictCoefficients (a : Coefficients n N) (χ : Euclidean n → ℝ)
    (J : InputVariables n → ℝ) (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2)) (p : Variables n) :
    amplitude (restrictCoefficients a χ) J u Ω S p =
      (χ p.1 * χ p.2.1) • amplitude a J u Ω S p := by
  simp only [amplitude, extendedDensity_restrictCoefficients, integral_smul]

/-- Reflection already includes both quadratures. Restriction introduces only
the two physical cutoffs (`app:ch_background:eq:bg-real-symbol`). -/
theorem reflectedSymbolAmplitude_restrictCoefficients (a : Coefficients n N)
    (χ : Euclidean n → ℝ) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2)) (p : Variables n) :
    reflectedSymbolAmplitude (restrictCoefficients a χ) J u Ω S p =
      (χ p.1 * χ p.2.1) • reflectedSymbolAmplitude a J u Ω S p := by
  simp only [reflectedSymbolAmplitude, amplitude_restrictCoefficients, ← smul_add]
  exact smul_comm _ _ _

/-- Two-sided physical multiplication of a full matrix PDO amplitude
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def restrictAmplitude (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (χ : Euclidean n → ℝ) (ξ : Euclidean n) (z : Euclidean (2 * n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  (χ (freezingOutputProjection z) * χ (freezingSourceProjection z)) • b ξ z

/-- Exact normalization `k = 2πξ` and both physical positions, with no new
quadrature factor (`app:ch_background:eq:bg-real-symbol`). -/
theorem fullReflectedMatrixAmplitude_restrictCoefficients (a : Coefficients n N)
    (χ : Euclidean n → ℝ) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2)) :
    fullReflectedMatrixAmplitude (restrictCoefficients a χ) J u Ω S =
      restrictAmplitude (fullReflectedMatrixAmplitude a J u Ω S) χ := by
  funext ξ z
  ext i j
  simp [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude_restrictCoefficients,
    restrictAmplitude]

/-- Exact source-first integral identity, valid without changing integration
order (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem fullAmplitudeOperator_cutoff (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (χ : Euclidean n → ℝ) (f : Euclidean n → ℂ) (x : Euclidean n) :
    fullAmplitudeOperator (fun x y ξ ↦ (χ x * χ y : ℝ) • c x y ξ) f x =
      χ x • fullAmplitudeOperator c (fun y ↦ (χ y : ℂ) * f y) x := by
  simp only [fullAmplitudeOperator, sourceAmplitudeTransform, Real.fourierInv_eq,
    Real.fourier_eq, Circle.smul_def, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  simp_rw [show ∀ ξ y, (Real.fourierChar (-inner ℝ y ξ) : ℂ) *
      (f y * ((χ x : ℂ) * (χ y : ℂ) * c x y ξ)) =
        (χ x : ℂ) * ((Real.fourierChar (-inner ℝ y ξ) : ℂ) *
          (((χ y : ℂ) * f y) * c x y ξ)) by intros; ring]
  simp only [integral_const_mul]
  simp_rw [← mul_assoc, mul_comm _ (χ x : ℂ), mul_assoc]
  rw [integral_const_mul]

/-- The full matrix action retains both physical cutoff factors and finite
matrix contractions (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem matrixFullAmplitudeOperator_restrictAmplitude
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (χ : Euclidean n → ℝ) (f : Euclidean n → Fin n → ℂ) (x : Euclidean n) (i : Fin n) :
    matrixFullAmplitudeOperator (fun x y ξ ↦ restrictAmplitude b χ ξ (pairedPosition x y)) f x i =
      χ x • matrixFullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y))
        (fun y j ↦ (χ y : ℂ) * f y j) x i := by
  simp only [matrixFullAmplitudeOperator, restrictAmplitude, freezingOutputProjection_pairedPosition,
    freezingSourceProjection_pairedPosition, Matrix.smul_apply]
  simp_rw [fullAmplitudeOperator_cutoff]
  exact (Finset.smul_sum ..).symm

end JanetCartan.ContinuumRow.CommonMeasurement
