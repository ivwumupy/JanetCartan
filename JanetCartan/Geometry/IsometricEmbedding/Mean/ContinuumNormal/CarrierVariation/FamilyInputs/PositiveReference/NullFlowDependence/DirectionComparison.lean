module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.RetainedMaps
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.DensityFootpoint

/-!
# From the primitive null direction to the retained ODE maps

This is the direction-to-flow portion of the fixed-positive-reference
comparison in `app:ch_background:prop:bg-frame`. The SAME forward and inverse
maps from `ActualAmplitude.UniformFlow` are compared by their equations. The
coefficient compact set, original low bound, and original existence time are
retained. No flow-family continuity is a premise.

Consumer: `FamilyInputs.PositiveReference` and the characteristic integral in
`carrierScalarAmplitude`. Potential-to-scalar comparison remains separate from
this direction-to-flow implication. The parent must instantiate the common
buffers and prove immersion-to-direction/potential comparison; these lemmas do
not certify that immersion-level theorem or the wider initial-density class.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Primitive `carrierTransportDirection` differences control the SAME retained
forward and inverse ODE maps at a fixed reference. The threshold is chosen
before the varying frame, solutions and tube. It uses precisely order `m` of
the primitive direction to control order `m` of both outputs.

The smoothness, compact buffer and low norm are the inputs of
`exists_uniform_actual_flow_chart`; that theorem produces `τ`, `D`, `Φ`, `Y`
and every initial/range/ODE/inverse premise below. It is also the flow producer
inside `exists_projected_local_positive_amplitude`. This implication does not
assume or assert the parent's immersion-level comparison
(`app:ch_background:prop:bg-frame`, `app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_cNorm_carrier_characteristics_sub_lt
    {Ω K : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R M τ : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hbuffer : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K)
    (hτeq : τ = existenceTime R (liftedLowBound T M) / 4)
    {KΦ KY : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hKΦ : KΦ ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 8))
    (hKY : KY ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 32))
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (row col : Fin n)
    (hd₀ : ContDiffOn ℝ ∞ (carrierTransportDirection T Q₀ row col) Ω)
    (hlow₀ : cNorm K 1 (carrierTransportDirection T Q₀ row col) ≤ M)
    {D₀ : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    {Φ₀ Y₀ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    (hsmall₀ : Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D₀)
    (hbig₀ : D₀ ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4))
    (hΦD₀ : MapsTo (fun q ↦ (q.1, Φ₀ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D₀)
    (hYD₀ : MapsTo (fun q ↦ (q.1, Y₀ q)) D₀ (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)))
    (hi₀ : ∀ p ∈ ball p₀ (R / 8), Φ₀ (0, p) = p)
    (hode₀ : ∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φ₀ (s, p))
        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q₀ row col
          ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
            (t, Φ₀ (t, p))))).2, 0) t)
    (hΦY₀ : ∀ q ∈ D₀, Φ₀ (q.1, Y₀ q) = q.2)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
      (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω →
      cNorm K 1 (carrierTransportDirection T Q row col) ≤ M →
      Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D →
      D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) →
      MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) D →
      MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) →
      (∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p) →
      (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ,
        HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
            ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
              (t, Φ (t, p))))).2, 0) t) →
      (∀ q ∈ D, Φ (q.1, Y q) = q.2) →
      cNorm K m (carrierTransportDirection T Q row col -
        carrierTransportDirection T Q₀ row col) < δ →
      cNorm KΦ m (Φ - Φ₀) + cNorm KY m (Y - Y₀) < ε := by
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  have hL : 0 ≤ liftedLowBound T M := liftedLowBound_nonneg T hM
  have htime := existenceTime_pos hR hL
  have hτ : 0 < τ := by rw [hτeq]; positivity
  have hτT : τ < existenceTime R (liftedLowBound T M) / 2 := by rw [hτeq]; linarith
  have hτR : τ ≤ R / 16 := by
    have hh := (existenceTime_le hR hL).1
    rw [hτeq]
    linarith
  have hb₀ (q) (hq : q ∈ closedBall (0, p₀) R) :=
    liftedDirection_low_bounds T Q₀ row col hΩ hd₀ hK hKΩ hM hlow₀ (hbuffer hq)
  obtain ⟨δ, hδ, hcompare⟩ := exists_cNorm_retained_characteristics_sub_lt
    (hΩ.preimage C.symm.continuous) (fun q hq ↦ hKΩ (hbuffer hq)) hR hL hτ hτT hτR
    hKΦ hKY (contDiffOn_liftedDirection T Q₀ row col hd₀) (fun _ ↦ rfl) hb₀
    hsmall₀ hbig₀ hΦD₀ hYD₀ hi₀ hode₀ hΦY₀ m hε
  obtain ⟨B, hB, hb⟩ := exists_liftedDirection_sub_bound T hK p₀ R hbuffer
  refine ⟨δ / B m, div_pos hδ (hB m), ?_⟩
  intro Q Φ Y D hd hlow hsmall hbig hΦD hYD hi hode hΦY hclose
  apply hcompare (liftedDirection T Q row col) Φ Y D
    (contDiffOn_liftedDirection T Q row col hd) (fun _ ↦ rfl)
    (fun q hq ↦ liftedDirection_low_bounds T Q row col hΩ hd hK hKΩ hM hlow (hbuffer hq))
    hsmall hbig hΦD hYD hi hode hΦY
  apply (hb Q Q₀ row col
    (fun w hw ↦ hd.contDiffAt (hΩ.mem_nhds (hKΩ hw)))
    (fun w hw ↦ hd₀.contDiffAt (hΩ.mem_nhds (hKΩ hw))) m).trans_lt
  simpa only [mul_comm] using (lt_div_iff₀ (hB m)).mp hclose

/-- The literal physical/carrier density footpoint inherits any proved
finite-order inverse-map comparison without derivative loss. Its definition
is `Y (FlowAmplitude.coordinates e (x, parameter z))`, as required by
`app:ch_background:eq:bg-full-complex-amplitude`. This is the final fixed
pullback after `exists_cNorm_carrier_characteristics_sub_lt`.
Smoothness on the compact adapted set is produced by
`ActualAmplitude.LocalConstruction`'s larger inverse buffer. -/
theorem exists_densityFootpoint_sub_tolerance
    {K : Set (Euclidean n × ContinuumRow.CarrierParameter)}
    {L : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hK : IsCompact K) (hL : IsCompact L) (hmaps : MapsTo (densityCoordinates T) K L)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Y Y₀ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      (∀ q ∈ L, ContDiffAt ℝ ∞ Y q) → (∀ q ∈ L, ContDiffAt ℝ ∞ Y₀ q) →
      cNorm L m (Y - Y₀) < δ →
      cNorm K m (densityFootpoint T Y - densityFootpoint T Y₀) < ε := by
  obtain ⟨B, hB, hb⟩ := exists_densityFootpoint_sub_bound T hK hL hmaps
  refine ⟨ε / B m, div_pos hε (hB m), fun Y Y₀ hY hY₀ hsmall ↦
    (hb Y Y₀ hY hY₀ m).trans_lt ?_⟩
  simpa only [mul_comm] using (lt_div_iff₀ (hB m)).mp hsmall

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
