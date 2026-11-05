module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SymbolGeometry
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Jacobian.Differential
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Determinant

/-!
# Smooth nonvanishing physical Jacobian

The physical determinant used by the carrier producer is the actual slice
determinant. Its smoothness, nonvanishing and degree-one scaling follow from
the constructed cone and the retained local determinant gap (`bg-jacobian`).
These facts discharge the geometric fields of `PrimitiveRegularity`; the
normal and reduced coefficient fields remain the amplitude producer's work.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ a ×ˢ dataSet z₀ ηb (3 * r)))

include hηb hr hf in
/-- Joint smoothness of the literal physical averaged gradient on the actual
original input cone (`app:ch_background:eq:bg-Psi`). -/
theorem transportAveragedGradient_smooth_on_symbolInputDomain :
    ContDiffOn ℝ ∞ (transportAveragedGradient (transportPosition T Q))
      (symbolInputDomain z₀ ηb r a) := by
  have harg : ContDiff ℝ ∞ (fun p : InputVariables n ↦
      ((p.2.1.2, p.1.1, p.1.2), (p.2.1.1, p.2.2))) :=
    (contDiff_snd.fst.snd.prodMk (contDiff_fst.fst.prodMk contDiff_fst.snd)).prodMk
      (contDiff_snd.fst.fst.prodMk contDiff_snd.snd)
  have hg := (adaptedTransportChart_smooth_on_cone T Q hηb hr hf).comp harg.contDiffOn
    (fun _ hp ↦ hp)
  have hh := (adaptedSliceCoordinates T).equiv.symm.contDiff.comp_contDiffOn hg
  apply hh.congr
  intro p _
  dsimp only [Function.comp_apply, Function.uncurry]
  apply (adaptedSliceCoordinates T).equiv.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

variable
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
include hηb hr hf hInv htrans

/-- The original physical Jacobian is strictly positive throughout the actual
supported cone, from the local determinant gap (`bg-jacobian`). -/
theorem transportAbsoluteJacobian_pos (hcJ : 0 < cJ)
    {p : InputVariables n} (hp : p ∈ symbolInputDomain z₀ ηb r a) :
    0 < transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) p := by
  have hd := adaptedTransportChart_differentiableAt_on_cone T Q hηb hr hf
    (p := (p.2.1.2, p.1.1, p.1.2)) (u := (p.2.1.1, p.2.2)) hp.1 hp.2
  rw [transportAbsoluteJacobian_eq_adaptedJacobian T Q p hd]
  have ht : 0 < ‖ηb‖ / ‖p.2.2‖ :=
    div_pos (norm_pos_iff.mpr hηb) (norm_pos_iff.mpr hp.2.2.1)
  have hw : radialScale (‖ηb‖ / ‖p.2.2‖) (p.2.1.1, p.2.2) ∈ dataBox z₀ ηb (2 * r) :=
    prod_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
        (normalizedInput_mem_dataSet (u := (p.2.1.1, p.2.2)) hηb hr hp.2)
  have hdet : 0 < adaptedJacobian T Q (p.2.1.2, p.1.1, p.1.2)
      (radialScale (‖ηb‖ / ‖p.2.2‖) (p.2.1.1, p.2.2)) :=
    hcJ.trans_le (hInv.differential_bounds (p.2.1.2, p.1.1, p.1.2) hp.1
      (radialScale (‖ηb‖ / ‖p.2.2‖) (p.2.1.1, p.2.2)) hw).2.2
  rw [adaptedJacobian_radialScale T Q hηb hr hf hInv htrans
    (p := (p.2.1.2, p.1.1, p.1.2)) (u := (p.2.1.1, p.2.2)) hp.1 hp.2 ht] at hdet
  exact (mul_pos_iff_of_pos_left ht).mp hdet

/-- Smoothness of the literal absolute Jacobian in all input variables.
The sign issue is discharged by the constructed positive determinant gap,
not assumed as primitive coefficient regularity (`bg-jacobian`). -/
theorem transportAbsoluteJacobian_smooth (hcJ : 0 < cJ) :
    ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q))
      (symbolInputDomain z₀ ηb r a) := by
  have hD := transportSliceDifferential_contDiffOn (adaptedSliceCoordinates T) (transportPosition T Q)
    (symbolInputDomain_open z₀ ηb r a)
      (transportAveragedGradient_smooth_on_symbolInputDomain T Q hηb hr hf)
  have hdet := NormalComparison.contDiff_normalJacobianDet.comp_contDiffOn hD
  apply hdet.abs
  intro p hp
  exact abs_pos.mp (transportAbsoluteJacobian_pos T Q hηb hr hf hInv htrans hcJ hp)

/-- Degree-one scaling for the actual physical measure-normalized Jacobian.
The original initial coordinates and both positions are unchanged
(`app:ch_background:eq:bg-jacobian`). -/
theorem transportAbsoluteJacobian_scaling
    {p : InputVariables n} (hp : p ∈ symbolInputDomain z₀ ηb r a)
    {t : ℝ} (ht : 0 < t) :
    transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) (scaleInput t p) =
      t * transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) p := by
  have hd := adaptedTransportChart_differentiableAt_on_cone T Q hηb hr hf
    (p := (p.2.1.2, p.1.1, p.1.2)) (u := (p.2.1.1, p.2.2)) hp.1 hp.2
  have hdt := adaptedTransportChart_differentiableAt_on_cone T Q hηb hr hf
    (p := (p.2.1.2, p.1.1, p.1.2)) (u := radialScale t (p.2.1.1, p.2.2)) hp.1
      (radialScale_mem_supportedCone hp.2 ht)
  rw [transportAbsoluteJacobian_eq_adaptedJacobian T Q p hd,
    transportAbsoluteJacobian_eq_adaptedJacobian T Q (scaleInput t p) hdt]
  exact adaptedJacobian_radialScale T Q hηb hr hf hInv htrans
    (p := (p.2.1.2, p.1.1, p.1.2)) (u := (p.2.1.1, p.2.2)) hp.1 hp.2 ht

end JanetCartan.ContinuumRow.CanonicalConic
