module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.CoefficientBuffers

/-!
# Final geometric inputs of the supported carrier constructor

These deductions connect the retained outer inverse and smaller original masks
to `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.
The actual producer of their chart hypotheses is
`exists_actual_refined_supported_geometry`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}

/-- Smoothness of the literal Hamilton position on the entire outer coefficient
domain, and hence on the finite field chart (`app:ch_background:eq:bg-Psi`). -/
theorem transportPosition_smooth_coefficientDomain {c C : ℝ} (hP : P.IsValid c C)
    (hr : 0 < r) (haR : a < T.family.radius) (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ContDiffOn ℝ ∞ (transportPosition T Q) (coefficientDomain z₀ r a) := by
  apply (transportPosition_smooth T Q hP).mono
  intro p hp
  refine ⟨ball_subset_ball haR.le hp.1, ?_⟩
  exact hcarrier (a := (p.2.2, p.2.1))
    ⟨closedBall_subset_closedBall har (ball_subset_closedBall hp.2.2),
      closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hp.2.1)⟩

variable {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hηb hr hf hInv htrans in
/-- The globally measurable kernel Jacobian has the exact degree-one scaling
at every inverse input (`app:ch_background:eq:bg-jacobian`). -/
theorem symbolJacobian_scale_inverse {p : Variables n × Euclidean 2}
    (hp : p ∈ symbolDomain T Q z₀ ηb r a) {t : ℝ} (ht : 0 < t) :
    symbolJacobian T Q (scaleInput t (inverseCoordinates (symbolInverse T Q z₀ ηb r a) p)) =
      t * symbolJacobian T Q (inverseCoordinates (symbolInverse T Q z₀ ηb r a) p) := by
  have hi := symbolInverse_maps T Q hηb hr hInv htrans hp
  have hit : scaleInput t (inverseCoordinates (symbolInverse T Q z₀ ηb r a) p) ∈
      symbolInputDomain z₀ ηb r a :=
    ⟨hi.1, radialScale_mem_supportedCone hi.2 ht⟩
  rw [symbolJacobian_eq_actual T Q hηb hr hf hit,
    symbolJacobian_eq_actual T Q hηb hr hf hi]
  exact transportAbsoluteJacobian_scaling T Q hηb hr hf hInv htrans hi ht

include hηb hr hf hInv htrans in
/-- The forward frequency comparison for the exact inverse, in the physical
Euclidean norm. Its constant is fixed by the frozen differential half-gap
(`app:ch_background:eq:bg-Psi`, `bg-jacobian`). -/
theorem symbolInverse_frequency_comparison {C : ℝ}
    (hgap : ∀ p ∈ physicalParameterSet z₀ a, ∀ u ∈ dataBox z₀ ηb (2 * r),
      ‖G.symm.toContinuousLinearMap.comp (fderiv ℝ (adaptedTransportChart T Q p) u) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)
    (hC : ∀ D : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1)),
      ‖G.symm.toContinuousLinearMap.comp D -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2 → ‖D‖ ≤ C)
    {p : Variables n × Euclidean 2} (hp : p ∈ symbolDomain T Q z₀ ηb r a) :
    ‖p.1.2.2‖ ≤ (‖(adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap‖ * C) *
      ‖(symbolInverse T Q z₀ ηb r a p).2‖ := by
  have hi := symbolInverse_maps T Q hηb hr hInv htrans hp
  have hb := (adaptedTransportChart_norm_bounds T Q hηb hr hf hInv htrans hgap hC hi.1 hi.2).2
  rw [← transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp]
  exact (physicalTransportChart_norm_le_adapted T Q
    (p.2, p.1.1, p.1.2.1) (symbolInverse T Q z₀ ηb r a p)).trans
      ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

end JanetCartan.ContinuumRow.CanonicalConic
