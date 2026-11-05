module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.FlowAmplitude.Coordinates

/-!
# Coordinates for the actual null-characteristic direction

The characteristic construction for `app:ch_waves:thm:leading` uses the normal
and section of the SAME retained carrier family. The Hilbert-space isometry in
`FullPhaseCharts.Coordinates` supplies a continuous linear equivalence for the
ordinary product norm used by `PositiveTransport.FlowSolution`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.ActualFlow
open ActualCarriers FrozenMenu CurrentFullPhase FrozenPhaseReference

variable {n : ℕ}

/-- The actual adapted coordinates, consumed by the null characteristic ODE
in `app:ch_waves:thm:leading`. No standard coordinate index is selected. -/
def adaptedCoordinates {ξ : Euclidean n} (a : AdaptedSection ξ) :
    Euclidean n ≃L[ℝ] (ℝ × Euclidean (n - 1)) :=
  ((LinearIsometryEquiv.ofSurjective (FullPhaseCharts.adaptedSpacetime a)
    (FullPhaseCharts.adaptedSpacetime_surjective a)).symm.toLinearEquiv.trans
      (WithLp.linearEquiv 2 ℝ (ℝ × Euclidean (n - 1)))).toContinuousLinearEquiv

/-- Reconstruction in the original physical coordinates
(`app:ch_waves:thm:leading`). -/
@[simp] theorem adaptedCoordinates_symm_apply {ξ : Euclidean n}
    (a : AdaptedSection ξ) (q : ℝ × Euclidean (n - 1)) :
    (adaptedCoordinates a).symm q = q.1 • a.normal + a.embedding q.2 := rfl

/-- Forward adapted coordinates use the actual normal and the adjoint of the
retained section embedding (`app:ch_waves:thm:leading`). -/
@[simp] theorem adaptedCoordinates_apply {ξ : Euclidean n}
    (a : AdaptedSection ξ) (x : Euclidean n) :
    adaptedCoordinates a x = (⟪a.normal, x⟫_ℝ, a.embedding.toContinuousLinearMap.adjoint x) := by
  apply (adaptedCoordinates a).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply, adaptedCoordinates_symm_apply,
    a.covector_decomposition]

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The autonomous lift of the literal normalized null direction. Carrier
velocity is zero, and adapted time velocity is one. Its flow supplies the
characteristic and footpoint chart in `app:ch_waves:thm:leading`. -/
def liftedDirection (row col : Fin n)
    (q : ℝ × (Euclidean (n - 1) × Euclidean 3)) :
    ℝ × (Euclidean (n - 1) × Euclidean 3) :=
  (1, (adaptedCoordinates T.data.adapted
    (carrierTransportDirection T Q row col
      ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm q))).2, 0)

/-- The lifted field is the pushforward of the actual physical direction,
with the carrier labels fixed (`app:ch_waves:thm:leading`). -/
theorem liftedDirection_eq_pushforward (row col : Fin n)
    (w : Euclidean n × Euclidean 3)
    (hd : carrierAdaptedDenominator T Q row col w ≠ 0) :
    liftedDirection T Q row col
        (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted) w) =
      FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)
        (carrierTransportDirection T Q row col w, (0 : Euclidean 3)) := by
  unfold liftedDirection
  rw [ContinuousLinearEquiv.symm_apply_apply]
  apply Prod.ext
  · simpa only [FlowAmplitude.coordinates_apply, adaptedCoordinates_apply] using
      (carrierTransportDirection_normal T Q row col w hd).symm
  · rfl

/-- Smoothness on the exact open coefficient patch transfers to the lifted
field (`app:ch_waves:thm:leading`). The input is produced by
`exists_projected_null_coefficients` for the literal projected stress frame. -/
theorem contDiffOn_liftedDirection (row col : Fin n)
    {Ω : Set (Euclidean n × Euclidean 3)}
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω) :
    ContDiffOn ℝ ∞ (liftedDirection T Q row col)
      ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm ⁻¹' Ω) := by
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  have hdir : ContDiffOn ℝ ∞ (fun q ↦ carrierTransportDirection T Q row col (C.symm q))
      (C.symm ⁻¹' Ω) := hd.comp C.symm.contDiff.contDiffOn (fun _ hq ↦ hq)
  have hadapt := (adaptedCoordinates T.data.adapted).contDiff.comp_contDiffOn hdir
  exact contDiffOn_const.prodMk (hadapt.snd.prodMk contDiffOn_const)

end JanetCartan.NullTransport.ActualFlow
