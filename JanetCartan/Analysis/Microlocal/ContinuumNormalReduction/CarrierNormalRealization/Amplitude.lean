module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TestChartTransfer.Output
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.Realization.Amplitude
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.VectorInteger
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Transfer

/-!
# The global carrier amplitude in PDO coordinates

The full reflected amplitude of `app:ch_background:eq:bg-real-symbol` in the
coordinates used by `vectorTwoPositionL2Operator`. This is the original
two-position amplitude, including its high-frequency mask and spectator
integral. The real-quadrature factor four is already included. No localization
or diagonal reduction is performed here. Consumers are the finite carrier normal
identification and the global representation in `ContinuumCommutator.Translation.Assembly`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open ContinuumNormalReduction ContinuumNormal TransportKernel Pseudodifferential AmplitudeBound
variable {n N : ℕ}

/-- The full real carrier symbol, with physical frequency `k = 2πξ`, in paired
PDO coordinates (`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`). Its reflected normalization already
accounts for both real quadratures. -/
def fullReflectedMatrixAmplitude
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (ξ : Euclidean n) (z : Euclidean (2 * n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ (reflectedSymbolAmplitude a J u Ω S
    (freezingOutputProjection z, freezingSourceProjection z, (2 * Real.pi) • ξ) i j : ℂ)

variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))

/-- Exact physical coordinates and normalization of the global full amplitude
(`app:ch_background:eq:bg-real-symbol`). -/
@[simp] theorem fullReflectedMatrixAmplitude_pairedPosition (x y ξ : Euclidean n)
    (i j : Fin n) :
    fullReflectedMatrixAmplitude a J u Ω S ξ (pairedPosition x y) i j =
      (reflectedSymbolAmplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℂ) := by
  simp [fullReflectedMatrixAmplitude]

/-- Both measurement supports remain in the GLOBAL full symbol. In particular,
the finite PDO support budget does not require a new cutoff whose plateau would
need to be identified (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem fullReflectedMatrixAmplitude_supportedInCenteredBox (R : ℝ)
    (hs : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ R)
    (ξ : Euclidean n) (i j : Fin n) :
    SupportedInCenteredBox R (fun z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) := by
  intro z hz k
  have hx : a.measurement (freezingOutputProjection z) ≠ 0 := by
    intro he
    simp [fullReflectedMatrixAmplitude,
      TestChartTransfer.reflectedAmplitude_eq_zero_of_output_measurement a J u Ω S _ _ _ he] at hz
  have hy : a.measurement (freezingSourceProjection z) ≠ 0 := by
    intro he
    simp [fullReflectedMatrixAmplitude,
      TestChartTransfer.reflectedAmplitude_eq_zero_of_source_measurement a J u Ω S _ _ _ he] at hz
  by_cases hk : k.val < n
  · exact hs _ hx ⟨k.val, hk⟩
  · simpa [freezingSourceProjection, show n + (k.val - n) = k.val by omega] using
      hs _ hy ⟨k.val - n, by omega⟩

/-- The source-tested matrix API agrees literally with this paired full symbol,
including both finite sums and `k = 2πξ` (`app:ch_background:eq:bg-real-symbol`). -/
theorem matrixFullAmplitudeOperator_fullReflectedMatrixAmplitude
    (f : Fin n → Euclidean n → ℂ) (x : Euclidean n) (i : Fin n) :
    matrixFullAmplitudeOperator
      (fun x y ξ ↦ fullReflectedMatrixAmplitude a J u Ω S ξ (pairedPosition x y))
      (fun y j ↦ f j y) x i = reflectedMatrixTestAction a J u Ω S f x i := by
  simp only [matrixFullAmplitudeOperator, reflectedMatrixTestAction,
    fullReflectedMatrixAmplitude_pairedPosition]

end JanetCartan.ContinuumRow.CarrierNormalRealization
