module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelCoefficients

/-!
# Fixed determinant bounds on the finite canonical input buffer

The lower constant uses the published actual conic comparison and the positive
input-frequency lower bound. Its choice precedes the current coefficient field.
The original physical coordinates and measure-normalized determinant are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

private theorem coefficient_jacobian_lower
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    {p : InputVariables n} (hp : p ∈ symbolInputDomain z₀ ηb r a) :
    (cJ / ‖ηb‖) * ‖p.2.2‖ ≤
      transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) p := by
  have hd := adaptedTransportChart_differentiableAt_on_cone T Q hηb hr hf
    (p := (p.2.1.2, p.1.1, p.1.2)) (u := (p.2.1.1, p.2.2)) hp.1 hp.2
  rw [transportAbsoluteJacobian_eq_adaptedJacobian T Q p hd]
  have hμ := norm_pos_iff.mpr hηb
  have hη := norm_pos_iff.mpr hp.2.2.1
  have hw : radialScale (‖ηb‖ / ‖p.2.2‖) (p.2.1.1, p.2.2) ∈ dataBox z₀ ηb (2 * r) :=
    prod_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
        (normalizedInput_mem_dataSet (u := (p.2.1.1, p.2.2)) hηb hr hp.2)
  have hl := (hInv.differential_bounds (p.2.1.2, p.1.1, p.1.2) hp.1 _ hw).2.2
  change cJ ≤ adaptedJacobian T Q (p.2.1.2, p.1.1, p.1.2)
    (radialScale (‖ηb‖ / ‖p.2.2‖) (p.2.1.1, p.2.2)) at hl
  rw [adaptedJacobian_radialScale T Q hηb hr hf hInv htrans hp.1 hp.2 (div_pos hμ hη)] at hl
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hμ).mpr
  have h := (le_div_iff₀ hη).mp (show cJ ≤
      ‖ηb‖ * adaptedJacobian T Q (p.2.1.2, p.1.1, p.1.2) (p.2.1.1, p.2.2) / ‖p.2.2‖ by
    simpa only [div_mul_eq_mul_div] using hl)
  simpa only [mul_comm] using h

/-- The actual annular comparison gives a positive fixed determinant lower
bound before `Q`, and identifies the same measurable symbol Jacobian on the
finite input buffer. The geometric premises are produced by
`exists_coefficient_buffers_cap`; the local analytic premises are exact
outputs of `exists_actual_refined_supported_geometry`.
Consumer: `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`
(`app:ch_background:eq:bg-jacobian`). -/
theorem exists_fixed_coefficient_jacobian_lower_bound
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a cJ ε ρ : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hcJ : 0 < cJ) (hε : 0 < ε)
    {p₀ : InputVariables n} {W : Set (InputVariables n)}
    (hball : closedBall p₀ ρ ⊆ W) (hW : W ⊆ symbolInputDomain z₀ ηb r a)
    (hη : ∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖) :
    ∃ δ > (0 : ℝ), ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)) →
      ∀ {b : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
        {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
      (∀ p ∈ physicalParameterSet z₀ a,
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      EqOn (symbolJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)) W ∧
      (∀ p ∈ W, symbolJacobian T Q p ≠ 0) ∧
      (∀ p ∈ closedBall p₀ ρ, δ ≤
        transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) p) := by
  refine ⟨(cJ / ‖ηb‖) * ε, mul_pos (div_pos hcJ (norm_pos_iff.mpr hηb)) hε, ?_⟩
  intro Q hf b V L G hInv htrans
  have he := (symbolJacobian_eq_actual T Q hηb hr hf).mono hW
  refine ⟨he, ?_, ?_⟩
  · intro p hp
    rw [he hp]
    exact ne_of_gt (transportAbsoluteJacobian_pos T Q hηb hr hf hInv htrans hcJ (hW hp))
  · intro p hp
    exact (mul_le_mul_of_nonneg_left (hη p hp)
      (div_pos hcJ (norm_pos_iff.mpr hηb)).le).trans
        (coefficient_jacobian_lower T Q hηb hr hf hInv htrans (hW (hball hp)))

end JanetCartan.ContinuumRow.CanonicalConic
