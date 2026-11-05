module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Footpoint.Direction

/-!
# Conservation of the actual Hamilton phase footpoint

Differentiate `d_ζ S` along the normalized null direction using the Hamilton
ODE and the genuine inverse chart. This is the geometric conservation law
needed by `Canonical.Footpoint`; it is not an input to that construction.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_waves:thm:leading`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.Footpoint
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase NullTransport

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The spatial derivative of the canonical phase footpoint is the spatial
part of the actual inverse-chart derivative
(`app:ch_background:defn:bg-carriers`). -/
theorem hasFDerivAt_transportPosition {x : Euclidean n} {z : CarrierParameter}
    (ht : (x, (0, T.reference.spatialPatch (CanonicalCarrier.parameter z))) ∈
      (T.currentChart Q).target) :
    HasFDerivAt (fun y ↦ CanonicalCarrier.transportPosition T Q (y, z))
      ((ContinuousLinearMap.snd ℝ ℝ (Euclidean (n - 1))).comp
        ((T.currentChart Q).coordinatePositionDerivative
          (x, (0, T.reference.spatialPatch (CanonicalCarrier.parameter z))))) x := by
  apply ((T.currentChart Q).hasFDerivAt_coordinates_position ht).snd.congr_of_eventuallyEq
  have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
    ((T.currentChart Q).isOpen_target.mem_nhds ht)
  filter_upwards [hn] with y hy using transportPosition_eq_chartCoordinate T Q hy

/-- The actual normalized null direction annihilates `d_ζ S`. The hypotheses
are the pointwise nullvector outputs of `LocalConstruction` and frame symmetry;
the Hamilton conservation equation is proved here
(`app:ch_waves:thm:leading`). -/
theorem fderiv_transportPosition_carrierTransportDirection
    (row col : Fin n) {x : Euclidean n} {z : CarrierParameter}
    (ht : (x, (0, T.reference.spatialPatch (CanonicalCarrier.parameter z))) ∈
      (T.currentChart Q).target)
    (hs : ∀ i, (Q.1 x i).IsSymm)
    (hk : carrierNullvector T Q col (x, CanonicalCarrier.parameter z) ≠ 0)
    (hl : carrierConullvector T Q row (x, CanonicalCarrier.parameter z) ≠ 0) :
    fderiv ℝ (fun y ↦ CanonicalCarrier.transportPosition T Q (y, z)) x
      (carrierTransportDirection T Q row col (x, CanonicalCarrier.parameter z)) = 0 := by
  have hξ : T.carrierGradient Q x (CanonicalCarrier.parameter z) =
      (T.currentChart Q).chartMomentum
        (x, (0, T.reference.spatialPatch (CanonicalCarrier.parameter z))) :=
    (T.currentChart Q).gradient_phase_eq_chartMomentum ht
  rw [(hasFDerivAt_transportPosition T Q ht).fderiv,
    carrierTransportDirection_eq_smul_hamiltonVelocity T Q row col ht hs hk hl,
    ContinuousLinearMap.comp_apply, map_smul, hξ,
    coordinatePositionDerivative_hamiltonVelocity (T.currentChart Q) ht]
  simp

/-- Convert the exact adapted ODE exported by `LocalConstruction` back to
the original physical characteristic. The denominator is the SAME nonzero
adapted coefficient exported on its tube (`app:ch_waves:thm:leading`). -/
theorem hasDerivAt_physical_nullCharacteristic (row col : Fin n)
    (Φ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (p : Euclidean (n - 1) × Euclidean 3) (t : ℝ)
    (hode : HasDerivAt (fun s ↦ Φ (s, p))
      ((ActualFlow.adaptedCoordinates T.data.adapted
        (carrierTransportDirection T Q row col
          ((FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)).symm
            (t, Φ (t, p))))).2, 0) t)
    (hd : carrierAdaptedDenominator T Q row col
      ((FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)).symm
        (t, Φ (t, p))) ≠ 0) :
    HasDerivAt (fun s ↦
      ((FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)).symm
        (s, Φ (s, p))).1)
      (carrierTransportDirection T Q row col
        ((FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)).symm
          (t, Φ (t, p)))) t := by
  let C := FlowAmplitude.coordinates (Z := Euclidean 3)
    (ActualFlow.adaptedCoordinates T.data.adapted)
  have hpush := ActualFlow.liftedDirection_eq_pushforward T Q row col
    (C.symm (t, Φ (t, p))) hd
  rw [C.apply_symm_apply] at hpush
  have ht : HasDerivAt (fun s ↦ (s, Φ (s, p)))
      (C (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))), 0)) t := by
    rw [← hpush]
    exact (hasDerivAt_id t).prodMk hode
  have hh : HasDerivAt (fun s ↦ C.symm (s, Φ (s, p)))
      (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))), (0 : Euclidean 3)) t := by
    convert! C.symm.hasFDerivAt.comp_hasDerivAt t ht using 1
    exact (C.symm_apply_apply _).symm
  exact hh.fst

end JanetCartan.ContinuumAdjoint.Canonical.Footpoint
