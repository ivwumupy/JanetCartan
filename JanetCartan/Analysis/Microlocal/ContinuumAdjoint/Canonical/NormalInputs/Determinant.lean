module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Geometry

/-!
# The actual degree-one determinant on the working domain

The annular determinant gap retained by
`CanonicalConic.exists_actual_refined_supported_geometry` gives the conic
lower bound with constant `cJ / ‖ηb‖`. Positive dilation preserves the phase
restriction, so the determinant law holds on this whole working domain.
Consumer: `PrimitiveJetGeometry.determinant_gap` (`bg-jacobian`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol ContinuumNormalReduction.ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r aOuter aPhase : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ aOuter ×ˢ dataSet z₀ ηb (3 * r)))
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ aOuter)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ aOuter,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

local notation "g" => normalChart T Q z₀ ηb r aOuter aPhase
include hηb hr hf hInv htrans

/-- The restricted physical Jacobian still has degree one in the original
covector, with the incidence label, positions and spectator unchanged
(`app:ch_background:eq:bg-jacobian`). -/
theorem normalChart_determinant_scaling {p : JointVariables n} (hp : p ∈ (g).inputDomain)
    {t : ℝ} (ht : 0 < t) :
    let q := scaleJointInput T t p
    |((g).jacobian q.1.1 q.1.2.1 q.2 q.1.2.2).det| =
      t * |((g).jacobian p.1.1 p.1.2.1 p.2 p.1.2.2).det| := by
  have hscaled := normalChart_scaleJointInput_mem T Q z₀ ηb r aOuter aPhase hp ht
  change symbolJacobian T Q (jointInputCoordinates T (scaleJointInput T t p)) =
    t * symbolJacobian T Q (jointInputCoordinates T p)
  rw [symbolJacobian_eq_actual T Q hηb hr hf
      (x := jointInputCoordinates T (scaleJointInput T t p)) hscaled.1,
    symbolJacobian_eq_actual T Q hηb hr hf (x := jointInputCoordinates T p) hp.1]
  simpa only [scaleJointInput, ContinuousLinearEquiv.apply_symm_apply] using
    transportAbsoluteJacobian_scaling T Q hηb hr hf hInv htrans
      (p := jointInputCoordinates T p) hp.1 ht

/-- The annular lower gap gives the exact frequency-weighted determinant
gap for `PrimitiveJetGeometry`. Its constant is fixed by the original
reference direction and the published annular construction (`bg-jacobian`). -/
theorem normalChart_determinant_gap {p : JointVariables n} (hp : p ∈ (g).inputDomain) :
    (cJ / ‖ηb‖) * ‖((g).carrier p).2‖ ≤
      |((g).jacobian p.1.1 p.1.2.1 p.2 p.1.2.2).det| := by
  let q := jointInputCoordinates T p
  have hq : q ∈ symbolInputDomain z₀ ηb r aOuter := hp.1
  have hμ := norm_pos_iff.mpr hηb
  have hη := norm_pos_iff.mpr hq.2.2.1
  have hw : radialScale (‖ηb‖ / ‖q.2.2‖) (q.2.1.1, q.2.2) ∈
      dataBox z₀ ηb (2 * r) :=
    prod_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
        (normalizedInput_mem_dataSet (u := (q.2.1.1, q.2.2)) hηb hr hq.2)
  have hl := (hInv.differential_bounds (q.2.1.2, q.1.1, q.1.2) hq.1 _ hw).2.2
  change cJ ≤ adaptedJacobian T Q (q.2.1.2, q.1.1, q.1.2)
    (radialScale (‖ηb‖ / ‖q.2.2‖) (q.2.1.1, q.2.2)) at hl
  rw [adaptedJacobian_radialScale T Q hηb hr hf hInv htrans hq.1 hq.2 (div_pos hμ hη)] at hl
  change (cJ / ‖ηb‖) * ‖q.2.2‖ ≤ symbolJacobian T Q q
  rw [symbolJacobian_eq_actual T Q hηb hr hf hq,
    transportAbsoluteJacobian_eq_adaptedJacobian T Q q
      (adaptedTransportChart_differentiableAt_on_cone T Q hηb hr hf hq.1 hq.2)]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hμ).mpr
  have hh := (le_div_iff₀ hη).mp
    (show cJ ≤ ‖ηb‖ * adaptedJacobian T Q (q.2.1.2, q.1.1, q.1.2)
        (q.2.1.1, q.2.2) / ‖q.2.2‖ by
      simpa only [div_mul_eq_mul_div] using hl)
  simpa only [mul_comm] using hh

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
