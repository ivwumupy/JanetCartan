module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.PrimaryRoot
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation.Suspension
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalCoordinates

/-!
# Canonical coordinates for the same primary phase

For `app:ch_response:eq:response-exact-phase`, connect the literal primary
chart to the direct root equation. The coordinate permutation preserves the
pairing, so transforming both physical position and covector is justified.
The actual root constructor and scalar uniqueness supply the eikonal equation;
no new phase or Hamilton flow is substituted. `RootBuffers` consumes this
local construction and discharges its transverse gap from the full-energy chart.
-/

open Set Filter Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.CompatibleResponse
open ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- Move the selected transverse coordinate into the time-first convention of the direct
kernel. This is a permutation of the original physical coordinates
(`app:ch_response:eq:response-exact-phase`). -/
def primaryCoordinateChange (i : Fin (d + 1)) : Euclidean (d + 1) ≃L[ℝ] Euclidean (d + 1) :=
  (coordinateSplit i).trans (coordinateSplit 0).symm

/-- The coordinate permutation is the literal time/space recombination used by the elapsed
kernel (`app:ch_response:lem:energy-carrier-jets`). -/
theorem primaryCoordinateChange_apply (i : Fin (d + 1)) (x : Euclidean (d + 1)) :
    primaryCoordinateChange i x = timeSpacePoint (x i) (coordinateSplit i x).2 := by
  rfl

/-- The selected coordinate permutation preserves the physical covector pairing. This
discharges canonicality for the actual direct root coordinates
(`app:ch_response:eq:response-exact-phase`). -/
theorem primaryCoordinateChange_pairing (i : Fin (d + 1)) (x y : Euclidean (d + 1)) :
    ⟪primaryCoordinateChange i x, primaryCoordinateChange i y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [primaryCoordinateChange_apply, primaryCoordinateChange_apply, inner_eq_time_add_spatial]
  simp only [timeSpacePoint_time, spatialPart_timeSpacePoint]
  simpa only [ContinuousLinearEquiv.symm_apply_apply, coordinateSplit_fst] using
    (coordinateSplit_covector_pairing i (coordinateSplit i x) y).symm

/-- Transform the actual differential by the same orthogonal coordinate permutation, with no
assumed gradient identification (`app:ch_response:eq:response-exact-phase`). -/
theorem gradient_primaryCoordinateChange (i : Fin (d + 1))
    {φ : Euclidean (d + 1) → ℝ} {x : Euclidean (d + 1)}
    (hφ : DifferentiableAt ℝ φ ((primaryCoordinateChange i).symm x)) :
    gradient (fun y ↦ φ ((primaryCoordinateChange i).symm y)) x =
      primaryCoordinateChange i (gradient φ ((primaryCoordinateChange i).symm x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  change fderiv ℝ (φ ∘ (primaryCoordinateChange i).symm) x v = _
  rw [(hφ.hasFDerivAt.comp x (primaryCoordinateChange i).symm.hasFDerivAt).fderiv]
  change fderiv ℝ φ ((primaryCoordinateChange i).symm x)
      ((primaryCoordinateChange i).symm v) = _
  rw [← inner_gradient_left]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (primaryCoordinateChange_pairing i (gradient φ ((primaryCoordinateChange i).symm x))
      ((primaryCoordinateChange i).symm v)).symm

/-- The state of the direct elapsed kernel is exactly the adapted pencil state after the
constructed coordinate permutation (`app:ch_response:eq:response-exact-phase`). -/
theorem spacetimeRootState_primaryCoordinateChange (i : Fin (d + 1))
    (x ξ : Euclidean (d + 1)) :
    spacetimeRootState (primaryCoordinateChange i x, primaryCoordinateChange i ξ) =
      adaptedPrimaryRootState (coordinateSplit i) x ξ := by
  simp [spacetimeRootState, primaryCoordinateChange_apply, adaptedPrimaryRootState]

end JanetCartan.CompatibleResponse

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The SAME selected primary phase in time-first physical coordinates. Only the coordinate
order changes (`app:ch_response:eq:response-exact-phase`). -/
def primaryPhaseInCoordinates (i : Fin (d + 1))
    (Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold}) (x : Euclidean (d + 1))
    (z : Euclidean 3) : ℝ := T.carrier Q ((primaryCoordinateChange i).symm x) z

/-- The actual selected primary gradient transforms by the canonical coordinate permutation
(`app:ch_response:eq:response-exact-phase`). -/
theorem primaryPhaseInCoordinates_gradient {c C : ℝ} (hP : P.IsValid c C)
    (i : Fin (d + 1)) (Q : _) {x : Euclidean (d + 1)} {z : Euclidean 3}
    (hx : (primaryCoordinateChange i).symm x ∈ ball 0 T.physicalRadius)
    (hz : z ∈ parameterInterior (2 * P.radius)) :
    gradient (fun y ↦ T.primaryPhaseInCoordinates i Q y z) x =
      primaryCoordinateChange i (T.carrierGradient Q ((primaryCoordinateChange i).symm x) z) := by
  apply gradient_primaryCoordinateChange i (φ := fun y ↦ T.carrier Q y z)
  have hb : ((primaryCoordinateChange i).symm x, z) ∈
      ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius) := ⟨hx, hz⟩
  have hs := (T.carrier_smooth hP Q).contDiffAt
    ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds hb)
  have hc : ContDiffAt ℝ ∞ (fun y ↦ T.carrier Q y z) ((primaryCoordinateChange i).symm x) :=
    hs.comp (f := fun y : Euclidean (d + 1) ↦ (y, z))
      ((primaryCoordinateChange i).symm x) (contDiffAt_id.prodMk contDiffAt_const)
  exact hc.differentiableAt (by simp)

/-- Construct the direct pencil root and prove the eikonal equation for the literal selected
primary phase in canonical coordinates, jointly on an open physical/parameter
neighborhood (`app:ch_response:eq:response-exact-phase`). The transverse derivative is
the sole additional primitive input here; `exists_buffered_primary_root` discharges it
from the same full-energy chart. -/
theorem exists_primary_root_equation_in_coordinates {c C : ℝ} (hP : P.IsValid c C)
    (i : Fin (d + 1)) (Q : _) {x₀ : Euclidean (d + 1)} {z₀ : Euclidean 3}
    (hx₀ : x₀ ∈ ball 0 T.physicalRadius) (hz₀ : z₀ ∈ parameterInterior (2 * P.radius))
    (hgap : fderiv ℝ (determinant (Q.1 x₀)) (T.carrierGradient Q x₀ z₀)
      ((coordinateSplit i).symm (1, 0)) ≠ 0) :
    ∃ D : Set (RootState (Euclidean d)), ∃ h : RootState (Euclidean d) → ℝ,
      IsOpen D ∧ ContDiffOn ℝ ∞ h D ∧
      (∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ U ∧ w.2.2 ≠ 0 ∧
        determinant (Q.1 ((coordinateSplit i).symm (w.1, w.2.1)))
          ((coordinateSplit i).symm (h w, w.2.2)) = 0 ∧
        fderiv ℝ (determinant (Q.1 ((coordinateSplit i).symm (w.1, w.2.1))))
          ((coordinateSplit i).symm (h w, w.2.2)) ((coordinateSplit i).symm (1, 0)) ≠ 0) ∧
      (∀ w ∈ D, ∀ a : ℝ, 0 < a →
        (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w) ∧
      ∃ V : Set (Euclidean (d + 1) × Euclidean 3), IsOpen V ∧
        (primaryCoordinateChange i x₀, z₀) ∈ V ∧
        (∀ q ∈ V, (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
          q.2 ∈ parameterInterior (2 * P.radius)) ∧
        ContDiffOn ℝ ∞ (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2) V ∧
        ContDiffOn ℝ ∞ (fun q ↦ gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x q.2) q.1) V ∧
        ∀ q ∈ V,
          spacetimeRootState (q.1, gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x q.2) q.1) ∈ D ∧
          rootSuspension h (q.1, gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x q.2) q.1) = 0 := by
  obtain ⟨D, h, hD, hh, hr, hscale, V₀, hV₀, hb, hsub, hm⟩ :=
    T.exists_primary_matching_pencilRoot hP Q (coordinateSplit i) hx₀ hz₀ hgap
  let F : Euclidean (d + 1) × Euclidean 3 → Euclidean (d + 1) × Euclidean 3 :=
    fun q ↦ ((primaryCoordinateChange i).symm q.1, q.2)
  have hF : ContDiff ℝ ∞ F :=
    ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd
  let V := F ⁻¹' V₀
  have hV : IsOpen V := hV₀.preimage hF.continuous
  have hv q (hq : q ∈ V) := hsub hq
  have hg q (hq : q ∈ V) := T.primaryPhaseInCoordinates_gradient hP i Q (hv q hq).1 (hv q hq).2
  refine ⟨D, h, hD, hh, hr, hscale, V, hV, ?_, hv, ?_, ?_, ?_⟩
  · simpa only [V, F, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hb
  · exact (T.carrier_smooth hP Q).comp hF.contDiffOn (fun q hq ↦ hv q hq)
  · exact ((primaryCoordinateChange i).contDiff.comp_contDiffOn
      ((T.carrierGradient_smooth hP Q).comp hF.contDiffOn (fun q hq ↦ hv q hq))).congr
        (fun q hq ↦ hg q hq)
  · intro q hq
    rw [hg q hq]
    have hstate : spacetimeRootState
        (q.1, primaryCoordinateChange i (T.carrierGradient Q (F q).1 q.2)) =
        adaptedPrimaryRootState (coordinateSplit i) (F q).1 (T.carrierGradient Q (F q).1 q.2) := by
      convert spacetimeRootState_primaryCoordinateChange i (F q).1
        (T.carrierGradient Q (F q).1 q.2) using 1
      simp [F]
    refine ⟨hstate ▸ (hm (F q) hq).1, ?_⟩
    change (primaryCoordinateChange i (T.carrierGradient Q (F q).1 q.2)) 0 - h _ = 0
    rw [hstate, primaryCoordinateChange_apply, timeSpacePoint_time]
    exact sub_eq_zero.mpr (hm (F q) hq).2

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
