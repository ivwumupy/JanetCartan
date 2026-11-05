module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.UnitRealization.Geometry

/-!
# Retained primitive geometry for the supplied-family spectral theorem

This is the geometric conclusion retained by the joint local constructor,
not a hypothesis replacing spectral positivity. The actual construction proves
all these facts before finite incidence selection. Consumer:
`retained_incidence_spectral_bounds` (`app:ch_background:prop:bg-frame`, Step 2).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic

/-- The outer inverse, transverse comparison and half-gap actually proved by
`exists_retained_joint_supported_geometry`. The inner masks remain independent
of these outer radii (`app:ch_background:eq:bg-Psi`, `bg-jacobian`). -/
def RetainedSpectralGeometry {n : ℕ} {P : Patch n} {U : Set (Euclidean n)}
    {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) : Prop :=
  6 * a ≤ 3 * r ∧
  (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
    carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
  ∃ (G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))
    (b cJ : ℝ) (V L : Set (ℝ × Euclidean (n - 1))),
    0 < cJ ∧ IsOpen V ∧ L ⊆ V ∧
    ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) ∧
    BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G ∧
    (∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) ∧
    (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖G.symm.toContinuousLinearMap.comp (fderiv ℝ (adaptedTransportChart T Q p) u) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)

end JanetCartan.ContinuumNormal.RetainedFrozen
