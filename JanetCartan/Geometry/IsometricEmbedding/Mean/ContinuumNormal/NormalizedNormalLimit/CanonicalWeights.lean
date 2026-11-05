module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.DensityWeights

/-!
# Identification of the prescribed canonical initial multiplier

The coefficient update used in `FullAmplitude` is identified with the actual
canonical carrier and its original initial scalar. In particular, the source
scalar `σ` is retained rather than replaced by a unit initial scalar.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier CarrierVariation.FamilyInputs.PositiveReference

/-- The actual prescribed scalar multiplied by `sqrt (1 + v)` is exactly the
normal-field update used by `exists_fullAmplitude_sqrtFootpoints_sub_bounds`.
The identity holds for the SAME immersion, null column, forward flow, ODE
inverse, initial scalar, measurement cutoff and masks. It assumes neither
coefficient nor normal-operator matching. Sources:
`app:ch_background:eq:bg-Nsigma`, `bg-T`, and `bg-full-complex-amplitude`. -/
theorem canonical_coefficients_initial_mul_sqrtDensity
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    let a := TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1)
    TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y (fun q ↦ initial q * Real.sqrt (1 + v q))
        hr hcell angular high) (FixedCutoffs.physical hr 1) =
      {a with normal := fun q ↦ Real.sqrt (1 + v (densityFootpoint T Y q)) • a.normal q} := by
  dsimp only
  rw [coefficientsOfCarrier_data, coefficientsOfCarrier_data]
  congr 1
  funext q
  change normalField T Q F row col Φ Y (fun p ↦ initial p * Real.sqrt (1 + v p)) q.1 q.2 =
    Real.sqrt (1 + v (densityFootpoint T Y q)) • normalField T Q F row col Φ Y initial q.1 q.2
  rw [normalField_eq_scalar_smul, normalField_eq_scalar_smul, ← mul_smul]
  congr 1
  simp only [carrierScalarAmplitude, transportFromFootpoint, characteristicTransport,
    scalarTransport, densityFootpoint_eq]
  ring

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
