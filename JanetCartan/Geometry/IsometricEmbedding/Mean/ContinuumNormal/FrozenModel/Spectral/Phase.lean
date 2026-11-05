module
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Coordinates
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Match the actual frozen phase and Jacobian

The frozen inverse in `app:ch_background:prop:bg-frame` is obtained by
restricting the retained conic geometry to the physical origin. Symmetry of
the actual Hamilton phase's mixed derivatives identifies its forward map
with `normalizedTransportPosition T Q 0`. The Jacobian equality is local on
the original carrier buffer, so no global smooth phase extension is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow ContinuumRow.CanonicalCarrier
open ContinuumNormalReduction.TransportSymbol
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The canonical derivative of the actual seed phase has the mixed physical
covector derivative at the origin. This identifies the forward map used by
the frozen inverse (`new:lem:scaling`, `app:ch_background:eq:bg-Psi`). -/
theorem gradient_transportPosition_origin {z : CarrierParameter}
    (hz : T.reference.spatialPatch (parameter z) ∈
      ball (ActualPhase.covectorCenter T) T.family.radius) (η : Euclidean (n - 1)) :
    gradient (fun x ↦ inner ℝ (transportPosition T Q (x, z)) η) 0 =
      fderiv ℝ (seedCovector T Q) (T.reference.spatialPatch (parameter z)) η := by
  let ζ := T.reference.spatialPatch (parameter z)
  let S := T.zeroEnergyPhase Q
  have h0 : (0 : Euclidean n) ∈ ball 0 T.family.radius := by
    simpa using T.family.radius_pos
  have hs : ContDiffOn ℝ ∞ S
      (ball (0 : Euclidean n) T.family.radius ×ˢ
        ball (ActualPhase.covectorCenter T) T.family.radius) := zeroEnergyPhase_smooth T Q
  have hΩ : IsOpen (ball (0 : Euclidean n) T.family.radius ×ˢ
      ball (ActualPhase.covectorCenter T) T.family.radius) := isOpen_ball.prod isOpen_ball
  have hd (x : Euclidean n) (hx : x ∈ ball 0 T.family.radius)
      (w : Euclidean (n - 1)) (hw : w ∈ ball (ActualPhase.covectorCenter T) T.family.radius) :
      DifferentiableAt ℝ S (x, w) :=
    by
      have hc : ContDiffAt ℝ ∞ S (x, w) := hs.contDiffAt (hΩ.mem_nhds ⟨hx, hw⟩)
      exact hc.differentiableAt (by simp)
  have hs0 : ContDiffAt ℝ ∞ S (0, ζ) :=
    hs.contDiffAt (hΩ.mem_nhds ⟨h0, hz⟩)
  have hD0 : ContDiffAt ℝ ∞ (fderiv ℝ S) (0, ζ) := hs0.fderiv_right (by simp)
  have hD := hD0.differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (seedCovector T Q) ζ :=
    ((seedCovector_smooth T Q).contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  apply ext_inner_right ℝ
  intro v
  have heL : (fun x ↦ inner ℝ (transportPosition T Q (x, z)) η) =ᶠ[𝓝 0]
      (fun x ↦ fderiv ℝ S (x, ζ) (0, η)) := by
    filter_upwards [isOpen_ball.mem_nhds h0] with x hx
    simp only [transportPosition, current_physicalCoordinates, inner_gradient_left]
    have h := (hd x hx ζ hz).hasFDerivAt.comp ζ
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) x ζ)
    exact congrArg (fun L ↦ L η) h.fderiv
  have heR : (fun w ↦ inner ℝ (seedCovector T Q w) v) =ᶠ[𝓝 ζ]
      (fun w ↦ fderiv ℝ S (0, w) (v, 0)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    rw [seedCovector, inner_gradient_left]
    have h := (hd 0 h0 w hw).hasFDerivAt.comp (0 : Euclidean n)
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : Euclidean n) w)
    exact congrArg (fun L ↦ L v) h.fderiv
  have hL := (hD.hasFDerivAt.comp (0 : Euclidean n)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : Euclidean n) ζ)).clm_apply
      (hasFDerivAt_const ((0 : Euclidean n), η) (0 : Euclidean n))
  have hR := (hD.hasFDerivAt.comp ζ
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : Euclidean n) ζ)).clm_apply
      (hasFDerivAt_const (v, (0 : Euclidean (n - 1))) ζ)
  have hi : inner ℝ (fderiv ℝ (seedCovector T Q) ζ η) v =
      fderiv ℝ (fun w ↦ inner ℝ (seedCovector T Q w) v) ζ η := by
    rw [fderiv_inner_apply ℝ hg (differentiableAt_const _)]
    simp only [fderiv_const_apply, zero_apply, inner_zero_right, zero_add]
  dsimp only [Function.comp_def] at hL hR
  rw [inner_gradient_left, hi, heL.fderiv_eq, heR.fderiv_eq, hL.fderiv, hR.fderiv]
  simpa using hs0.isSymmSndFDerivAt (by simp) (v, 0) (0, η)


/-- The literal zero-scale averaged gradient is the original chart's gradient
at both positions zero, throughout the retained phase buffer
(`new:lem:scaling`, `app:ch_background:eq:bg-Psi`). -/
theorem transportAveragedGradient_zero_eq_origin (p : InputVariables n)
    (hz : T.reference.spatialPatch (parameter p.2.1) ∈
      ball (ActualPhase.covectorCenter T) T.family.radius) :
    transportAveragedGradient (normalizedTransportPosition T Q 0) p =
      transportAveragedGradient (transportPosition T Q) (originInput p) := by
  rw [transportAveragedGradient_zero T Q p hz]
  simp only [transportAveragedGradient, originInput, sub_self, smul_zero, add_zero,
    gradient_transportPosition_origin T Q hz, intervalIntegral.integral_const,
    sub_zero, one_smul]

/-- The zero-scale absolute Jacobian equals the original Jacobian at the
physical origin. The derivative comparison holds on a neighborhood in the
original `(s,η)` slice (`app:ch_background:eq:bg-jacobian`). -/
theorem transportAbsoluteJacobian_zero_eq_origin {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    (c : TransportSliceCoordinates n) (p : InputVariables n)
    (hz : parameter p.2.1 ∈ parameterInterior (3 * P.radius / 2)) :
    transportAbsoluteJacobian c (normalizedTransportPosition T Q 0) p =
      transportAbsoluteJacobian c (transportPosition T Q) (originInput p) := by
  have hc : Continuous (fun w : Euclidean n ↦ parameter ((c.equiv w).1, p.2.1.2)) :=
    parameter.continuous.comp (c.equiv.continuous.fst.prodMk continuous_const)
  have hm : parameter ((c.equiv (c.equiv.symm (p.2.1.1, p.2.2))).1, p.2.1.2) ∈
      parameterInterior (3 * P.radius / 2) := by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
  have he : transportSliceForward c (normalizedTransportPosition T Q 0) p =ᶠ[
      𝓝 (c.equiv.symm (p.2.1.1, p.2.2))]
      transportSliceForward c (transportPosition T Q) (originInput p) := by
    filter_upwards [((isOpen_parameterInterior _).preimage hc).mem_nhds hm] with w hw
    exact transportAveragedGradient_zero_eq_origin T Q _
      (spatialPatch_mem_phaseBuffer T hP (fun i ↦ (hw i).le))
  exact congrArg (fun D : Euclidean n →L[ℝ] Euclidean n ↦ |D.det|) he.fderiv_eq

end JanetCartan.ContinuumNormal.FrozenModel
