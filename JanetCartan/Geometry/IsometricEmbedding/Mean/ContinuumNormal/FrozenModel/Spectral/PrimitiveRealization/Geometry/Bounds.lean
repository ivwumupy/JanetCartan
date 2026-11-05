module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.Freezing
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.CoefficientBuffers.Jacobian
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Homogeneity

/-!
# Frozen geometric norms and the fixed Jacobian lower bound

The coefficient buffers and the outer conic chart supply all domains used here.
The Jacobian lower constant is chosen before the current frame; the finite
geometry norms may depend on the fixed seed. Consumer: the primitive supported
carrier constructor (`new:lem:scaling`, `app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The original input region embeds in its frozen counterpart by setting
only the physical positions to zero (`new:lem:scaling`). -/
theorem symbolInputDomain_subset_frozenInputDomain
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r : ℝ) {a : ℝ} (ha : 0 < a) :
    symbolInputDomain z₀ ηb r a ⊆ frozenInputDomain z₀ ηb r a := by
  intro p hp
  exact ⟨⟨hp.1.1, mem_ball_self ha, mem_ball_self ha⟩, hp.2⟩

/-- The fixed lower bound on the input frequency and the retained annular
determinant gap give a fixed positive frozen Jacobian lower bound. This
instantiates the geometric determinant premise of the supported constructor;
`exists_frozenMeasured_coefficient_buffers` supplies the ball and `ε`.
Source: `new:lem:scaling`, `app:ch_background:eq:bg-jacobian`. -/
theorem exists_frozen_primitive_jacobian_lower_bound
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a cJ ε ρ : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hcJ : 0 < cJ) (hε : 0 < ε)
    {W : Set (InputVariables n)}
    (hball : closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ ⊆ W)
    (hW : W ⊆ symbolInputDomain z₀ ηb r a)
    (hη : ∀ p ∈ closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ,
      ε ≤ ‖p.2.2‖) :
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
      (∀ p ∈ W, transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0) p ≠ 0) ∧
      (∀ p ∈ closedBall (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ρ,
        δ ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (normalizedTransportPosition T Q 0) p) := by
  obtain ⟨δ, hδ, hlower⟩ := exists_fixed_coefficient_jacobian_lower_bound T
    hηb hr hcJ hε hball hW hη
  refine ⟨δ, hδ, ?_⟩
  intro Q hf b V L G hInv htrans
  obtain ⟨_, _, hl⟩ := hlower Q hf hInv htrans
  refine ⟨fun p hp ↦ (frozenJacobian_pos T Q hP hηb hr har hcarrier hInv htrans hf hcJ
    (symbolInputDomain_subset_frozenInputDomain z₀ ηb r ha (hW hp))).ne', ?_⟩
  intro p hp
  rw [frozenJacobian_eq_origin T Q hP hr har hcarrier _
    (symbolInputDomain_subset_frozenInputDomain z₀ ηb r ha (hW (hball hp)))]
  exact hl _ (originInput_mem_closedBall_centered_at_zero_positions hp)

/-- Finite geometry norms for the actual normalized zero-scale transport on
the coefficient region. The carrier buffer is an exact outer local-chart
output; the finite norm budget is chosen for the fixed seed before the high
budget `H`. Consumer: the supported primitive constructor (`bg-mixed-input`). -/
theorem exists_frozen_geometry_norms
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} {r a : ℝ} (hr : 0 < r) (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {V L : Set (Euclidean n × CarrierParameter)} (hV : V ⊆ coefficientDomain z₀ r a) :
    ∃ M ≥ (0 : ℝ), ∃ B : ℕ → ℝ, (∀ s, 1 ≤ B s) ∧
      ContDiffOn ℝ ∞ (normalizedTransportPosition T Q 0) V ∧
      cNorm L 3 (normalizedTransportPosition T Q 0) ≤ M ∧
      ∀ s H, 1 ≤ H → 1 + cNorm L (s + 2) (normalizedTransportPosition T Q 0) ≤ B s * H := by
  let Y := normalizedTransportPosition T Q 0
  refine ⟨cNorm L 3 Y, cNorm_nonneg _ _ _, fun s ↦ 1 + cNorm L (s + 2) Y,
    fun s ↦ le_add_of_nonneg_right (cNorm_nonneg _ _ _), ?_, le_rfl, ?_⟩
  · apply (normalizedTransportPosition_zero_smooth T Q hP).mono
    intro p hp
    have hd := hV hp
    exact ⟨mem_univ _, hcarrier (a := (p.2.2, p.2.1))
      ⟨closedBall_subset_closedBall har (ball_subset_closedBall hd.2.2),
        closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hd.2.1)⟩⟩
  · intro s H hH
    exact le_mul_of_one_le_right (add_nonneg zero_le_one (cNorm_nonneg _ _ _)) hH

end JanetCartan.ContinuumNormal.FrozenModel
