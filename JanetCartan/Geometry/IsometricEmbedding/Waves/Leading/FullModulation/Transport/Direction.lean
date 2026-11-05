module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Coefficients

/-! # The autonomous full-modulation direction

The state retains BOTH independent parameters `(z, ζ)` for
`app:ch_waves:thm:leading`. This supplies the coefficient lift for the
actual flow and its inverse.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase
variable {n : ℕ}

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The autonomous lift of the literal normalized null direction. Both parameter
velocities are zero, and adapted time velocity is one. Its flow supplies the
characteristic and footpoint chart in `app:ch_waves:thm:leading`. -/
def liftedDirection (row col : Fin n)
    (q : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))) :
    ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) :=
  (1, (adaptedCoordinates T.data.adapted
    (transportDirection T Q row col
      ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm q))).2, 0)

/-- The lifted field is the pushforward of the actual physical direction,
with both independent parameters fixed (`app:ch_waves:thm:leading`). -/
theorem liftedDirection_eq_pushforward (row col : Fin n)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    (hd : adaptedDenominator T Q row col w ≠ 0) :
    liftedDirection T Q row col
        (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted) w) =
      FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)
        (transportDirection T Q row col w, (0 : (Euclidean 3 × Euclidean (n - 1)))) := by
  unfold liftedDirection
  rw [ContinuousLinearEquiv.symm_apply_apply]
  apply Prod.ext
  · simpa only [FlowAmplitude.coordinates_apply, adaptedCoordinates_apply] using
      (transportDirection_normal T Q row col w hd).symm
  · rfl

/-- Smoothness on the exact open coefficient patch transfers to the lifted
field (`app:ch_waves:thm:leading`). The input is produced by
`jc-leading-full-modulation-coefficients` for the literal projected stress frame. -/
theorem contDiffOn_liftedDirection (row col : Fin n)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hd : ContDiffOn ℝ ∞ (transportDirection T Q row col) Ω) :
    ContDiffOn ℝ ∞ (liftedDirection T Q row col)
      ((FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm ⁻¹' Ω) := by
  let C := FlowAmplitude.coordinates (Z := (Euclidean 3 × Euclidean (n - 1))) (adaptedCoordinates T.data.adapted)
  have hdir : ContDiffOn ℝ ∞ (fun q ↦ transportDirection T Q row col (C.symm q))
      (C.symm ⁻¹' Ω) := hd.comp C.symm.contDiff.contDiffOn (fun _ hq ↦ hq)
  have hadapt := (adaptedCoordinates T.data.adapted).contDiff.comp_contDiffOn hdir
  exact contDiffOn_const.prodMk (hadapt.snd.prodMk contDiffOn_const)

end JanetCartan.LeadingWave.FullModulation
