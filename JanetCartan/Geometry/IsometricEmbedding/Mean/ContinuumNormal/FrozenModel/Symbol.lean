module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.CarrierData
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Positivity
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.Amplitude
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Jacobian.Basic

/-!
# The literal frozen matrix expression

The image term and reflected spectator integrals of the frozen step in
`app:ch_background:prop:bg-frame`. The carrier coefficients are those of
`uncutFrozenCoefficients`; the Jacobian is the absolute determinant of the
actual zero-scale transport map. Neither a positive symbol nor a coercivity
estimate is an input.

The inverse chart, its domain and spectator support remain explicit arguments.
Their geometric construction, integrability, boundedness, the high-frequency
gap and identification with the carrier extension are further obligations.
The nonnegativity proof below also covers the totalized Bochner integral; it
does not infer integrability from nonnegativity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel

open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization

private theorem integral_posSemidef {n : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → Matrix (Fin n) (Fin n) ℝ)
    (hf : ∀ x, (f x).PosSemidef) : (∫ x, f x ∂μ).PosSemidef := by
  by_cases hi : Integrable f μ
  · have he : (∫ x, f x ∂μ) = fun i j ↦ ∫ x, f x i j ∂μ := by
      ext i j
      exact ((realMatrixEntry i j).integral_comp_comm hi).symm
    rw [he]
    exact NormalizedBackground.posSemidef_integral_entries
      (fun i j ↦ (realMatrixEntry i j).integrable_comp hi) hf
  · rw [integral_undef hi]
    exact Matrix.PosSemidef.zero

section Carrier

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (c : TransportSliceCoordinates n)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))

/-- One actual frozen carrier's real reflected matrix, in physical radian
frequency. The coefficient `2 (2π)^n` on each of the two reflections retains
the realification factor four (`app:ch_background:eq:bg-real-symbol`). -/
def frozenCarrierSymbol (k : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  reflectedSymbolAmplitude (uncutFrozenCoefficients T Q F row col Φ Y initial angular high)
    (transportAbsoluteJacobian c (normalizedTransportPosition T Q 0)) u Ω S (0, 0, k)

/-- The actual frozen input density is a nonnegative scalar times a detector
square. This uses the genuine absolute Jacobian and constant seed coefficients
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenInputDensity_posSemidef (p : InputVariables n) :
    (inputDensity (uncutFrozenCoefficients T Q F row col Φ Y initial angular high)
      (transportAbsoluteJacobian c (normalizedTransportPosition T Q 0)) p).PosSemidef := by
  let a := uncutFrozenCoefficients T Q F row col Φ Y initial angular high
  have hw : 0 ≤ inputWeight a
      (transportAbsoluteJacobian c (normalizedTransportPosition T Q 0)) p := by
    dsimp [inputWeight, a, uncutFrozenCoefficients, transportAbsoluteJacobian]
    positivity
  exact (Matrix.posSemidef_vecMulVec_self_star
    (ActualCarriers.quadratic (Q.1 0) (T.carrierGradient Q 0 (CanonicalCarrier.parameter p.2.1)))).smul hw

/-- Every Euclidean frequency has a nonnegative reflected carrier matrix.
This is positivity of the literal spectator expression, with the original
high mask; it does not assert its integrability or identify an operator
(`app:ch_background:prop:bg-frame`, frozen step). -/
theorem frozenCarrierSymbol_posSemidef (k : Euclidean n) :
    (frozenCarrierSymbol T Q F row col Φ Y initial angular high c u Ω S k).PosSemidef := by
  have hp (k : Euclidean n) :
      (amplitude (uncutFrozenCoefficients T Q F row col Φ Y initial angular high)
        (transportAbsoluteJacobian c (normalizedTransportPosition T Q 0)) u Ω S
        (0, 0, k)).PosSemidef := by
    apply integral_posSemidef
    intro v
    by_cases h : ((0, 0, k), v) ∈ Ω
    · simp only [extendedDensity, indicator_of_mem h]
      exact frozenInputDensity_posSemidef T Q F row col Φ Y initial angular high c _
    · simp only [extendedDensity, indicator_of_notMem h]
      exact Matrix.PosSemidef.zero
  exact ((hp k).add (hp (-k))).smul (by positivity)

/-- The shared full normal amplitude uses the same reflection and the exact
physical conversion `k = 2πξ`. In particular no integer-frequency sampling is
used (`app:ch_background:eq:bg-real-symbol`). -/
theorem fullReflectedMatrixAmplitude_at_origin (ξ : Euclidean n) :
    fullReflectedMatrixAmplitude
      (uncutFrozenCoefficients T Q F row col Φ Y initial angular high)
      (transportAbsoluteJacobian c (normalizedTransportPosition T Q 0)) u Ω S ξ
      (AmplitudeBound.pairedPosition 0 0) =
    fun i j ↦ (frozenCarrierSymbol T Q F row col Φ Y initial angular high c u Ω S
      ((2 * Real.pi) • ξ) i j : ℂ) := by
  ext i j
  exact fullReflectedMatrixAmplitude_pairedPosition _ _ _ _ _ _ _ _ _ _

end Carrier

/-- The ideal image contribution, `M₀(k) M₀(k)ᵀ / (1 + |k|²)`, in the
frozen step of `app:ch_background:prop:bg-frame`. -/
def frozenImageSymbol {n : ℕ} (Q₀ : Fin n → MetricTensor n) (k : Euclidean n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 + ‖k‖ ^ 2)⁻¹ • (pencil Q₀ k * (pencil Q₀ k).transpose)

/-- Positivity of the literal image matrix at every Euclidean frequency
(`app:ch_background:prop:bg-frame`). -/
theorem frozenImageSymbol_posSemidef {n : ℕ} (Q₀ : Fin n → MetricTensor n)
    (k : Euclidean n) : (frozenImageSymbol Q₀ k).PosSemidef := by
  simpa only [frozenImageSymbol, conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_self_mul_conjTranspose (pencil Q₀ k)).smul
      (show 0 ≤ (1 + ‖k‖ ^ 2)⁻¹ by positivity)

section Family

variable {n N : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : ∀ a, PatchQuantitativeFamily (P a) U hU)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ a, cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < (T a).family.threshold)
    (F : Euclidean n → Euclidean N) (row col : ι → Fin n)
    (Φ Y : ι → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
    (angular : ι → CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (c : ι → TransportSliceCoordinates n)
    (u : ι → Variables n × Euclidean 2 → SliceVariable n)
    (Ω : ι → Set (Variables n × Euclidean 2)) (S : ι → Set (Euclidean 2))

/-- The frozen matrix expression for the SAME finite family: ideal image
normal plus the actual reflected spectator integrals. No coercivity or chart
existence assertion is stored in this definition
(`app:ch_background:prop:bg-frame`, frozen step). -/
def frozenMatrixSymbol (k : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  frozenImageSymbol (Q 0) k + ∑ a, frozenCarrierSymbol (T a) ⟨Q, hQ, hlow a⟩ F
    (row a) (col a) (Φ a) (Y a) (initial a) (angular a) high (c a) (u a) (Ω a) (S a) k

/-- Nonnegativity of the actual frozen matrix expression at every Euclidean
frequency, derived from its image and spectator formulas
(`app:ch_background:prop:bg-frame`, frozen step). -/
theorem frozenMatrixSymbol_posSemidef (k : Euclidean n) :
    (frozenMatrixSymbol T Q hQ hlow F row col Φ Y initial angular high c u Ω S k).PosSemidef :=
  (frozenImageSymbol_posSemidef (Q 0) k).add
    (Matrix.posSemidef_sum _ (fun a _ ↦ frozenCarrierSymbol_posSemidef
      (T a) ⟨Q, hQ, hlow a⟩ F (row a) (col a) (Φ a) (Y a) (initial a)
        (angular a) high (c a) (u a) (Ω a) (S a) k))

end Family

end JanetCartan.ContinuumNormal.FrozenModel
