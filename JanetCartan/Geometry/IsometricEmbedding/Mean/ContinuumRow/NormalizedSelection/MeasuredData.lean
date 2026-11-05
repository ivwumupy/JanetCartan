module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.CarrierData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.FullNormal

/-!
# The original normalized carrier on the common measurement chart

Instantiate the supplied-family measurement construction on the literal
`normalizedCarrierData`, retaining the original seed scalar, masks, labels
and carrier measure. This connects the normalized carrier producer to the
common row without a second choice of geometric or bounded-operator data.
The consumer is the normalized image/carrier assembly for
`app:ch_background:defn:bg-row` and `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier
open ContinuumNormal.FrozenModel CommonMeasurement NormalizedMeasurement

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hcell : 4 * r < 1 / 2) (hlocal : 4 * a < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) (σ : ℝ)

/-- Restriction to the common chart commutes literally with source
normalization at every scale, including zero. In particular the initial
scalar and masks are not reselected (`new:lem:scaling`, `bg-T`). -/
theorem commonChartData_normalizedCarrierData :
    commonChartData (normalizedCarrierData T Q F row col Φ Y initial
      ha hlocal angular high σ) (closedBall 0 (4 * r)) (FixedCutoffs.periodic hr hcell 1) =
    normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high σ := rfl

/-- The supplied normalized carrier has the literal restricted kernel and
the same test and adjoint realizations on the common measurement chart.
Every initial scalar is allowed. The operator is the supplied local carrier;
its realization premises are precisely the outputs of the supported carrier
producer, not a normal gap or inverse estimate
(`app:ch_background:eq:bg-T`, `bg-realification`, `bg-uniform-normalized`). -/
theorem normalizedCarrierData_common_measurement (hra : 6 * r < a) :
    let d := normalizedCarrierData T Q F row col Φ Y initial ha hlocal angular high σ
    let e := normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high σ
    let χ := FixedCutoffs.periodic (n := n) hr hcell 1
    (∀ x u, carrierKernel e x u = χ x • carrierKernel d x u) ∧
    ∀ V : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      ‖restrictCarrier χ V‖ ≤ ‖V‖ ∧
      ((∀ v : carrierInitialTestSpace n,
          V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val) →
        (∀ v : carrierInitialTestSpace n,
          restrictCarrier χ V (carrierInitialTestToLp v) =ᵐ[volume]
            carrierTestIntegral e v.val) ∧
        ∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → restrictCarrier χ V f x = 0) ∧
      ((∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n) ∧
          V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) →
        ∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
          (restrictCarrier χ V).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
      carrierChannel (restrictCarrier χ V) ∘L (carrierChannel (restrictCarrier χ V)).adjoint =
        cutoffMultiplier χ ∘L (carrierChannel V ∘L (carrierChannel V).adjoint) ∘L
          cutoffMultiplier χ := by
  intro d e χ
  have h := supplied_carrier_common_measurement d hr ha hcell hlocal hra rfl
    (fun _ _ ↦ rfl) rfl
  refine ⟨h.2.2.2.2.2.2.2.1, ?_⟩
  intro V
  obtain ⟨hV, htest, hadj⟩ := h.2.2.2.2.2.2.2.2 V
  exact ⟨hV, htest, hadj, carrierChannel_restrictCarrier_normal χ V⟩

/-- At every scale, the normalized common-chart coefficients are literally
the original coefficients multiplied by the new physical measurement
cutoff. The seed scalar, masks and reduced detector are unchanged
(`app:ch_background:eq:bg-full-complex-amplitude`, `bg-uniform-normalized`). -/
theorem normalizedCarrierData_common_coefficients (hra : 6 * r < a) :
    TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high σ)
      (FixedCutoffs.physical hr 1) =
    restrictCoefficients
      (TransportKernel.coefficientsOfCarrier
        (normalizedCarrierData T Q F row col Φ Y initial ha hlocal angular high σ)
        (FixedCutoffs.physical ha 1)) (FixedCutoffs.physical hr 1) := by
  unfold TransportKernel.coefficientsOfCarrier restrictCoefficients
  congr 1
  funext x
  exact (physical_measurement_mul hr ha (by linarith : 3 * r ≤ 2 * a) x).symm

/-- The FULL reflected amplitude on the common chart has exactly the two
physical cutoff factors. The original inverse, Jacobian, spectator measure,
physical frequency `2πξ` and quadrature factor four are retained through
source scale zero (`app:ch_background:eq:bg-real-symbol`,
`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalizedCarrierData_common_reflectedAmplitude (hra : 6 * r < a)
    (J : ContinuumNormalReduction.TransportSymbol.InputVariables n → ℝ)
    (u : ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2 →
      ℝ × Euclidean (n - 1))
    (Ω : Set (ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2))
    (S : Set (Euclidean 2)) :
    CarrierNormalRealization.fullReflectedMatrixAmplitude
      (TransportKernel.coefficientsOfCarrier
        (normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high σ)
        (FixedCutoffs.physical hr 1)) J u Ω S =
    restrictAmplitude
      (CarrierNormalRealization.fullReflectedMatrixAmplitude
        (TransportKernel.coefficientsOfCarrier
          (normalizedCarrierData T Q F row col Φ Y initial ha hlocal angular high σ)
          (FixedCutoffs.physical ha 1)) J u Ω S) (FixedCutoffs.physical hr 1) := by
  rw [normalizedCarrierData_common_coefficients T Q F row col Φ Y initial hr ha hcell hlocal
    angular high σ hra, fullReflectedMatrixAmplitude_restrictCoefficients]

end JanetCartan.ContinuumRow.NormalizedSelection
