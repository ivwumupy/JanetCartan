module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.RootMatching
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Phase.Extension

/-!
# Retained-root matching for the original full source phase

The supported primary strain has the phase `FullModulation.phase T Q x ζ`,
with the full covector `ζ` independent of the three carrier parameters. Match
that exact phase to a retained solver root on its actual incidence domain.
No new primary patch is chosen and no carrier-graph restriction is imposed.

Consumer: the full-source stationary-domain construction needed before
`exists_actualMaskFamily_with_stationary_source_radii` can be instantiated
for `app:ch_response:thm:response-compatible-choice` and
`app:ch_response:eq:direct-envelope-profile`. These results prove the root
equation on the literal incidence domain; they do not assert that one local
stationary domain covers every original source parameter.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ArbitraryAccuracy
open RegularSector.Characteristic RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open ResponseTransfer.RetainedFactors LeadingWave.FullModulation

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d

/-- The original full source phase after only the solver's physical coordinate
permutation. Both original source parameters are retained; the free covector
is not replaced by `spatialPatch` (`app:ch_response:cor:current-atoms`). -/
def fullSourcePhaseInCoordinates (i : Fin (d + 1))
    (Q : {Q : E → Coeff // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (x : E) (c : Param) : ℝ :=
  LeadingWave.FullModulation.phase T Q ((primaryCoordinateChange i).symm x) c.2

/-- The exact gradient of the full source transforms by the same canonical
coordinate permutation as the solver. The only domain is the original full
Hamilton phase domain (`app:ch_response:eq:response-exact-phase`). -/
theorem fullSourcePhaseInCoordinates_gradient (i : Fin (d + 1)) (Q : _)
    {x : E} {c : Param}
    (hx : ((primaryCoordinateChange i).symm x, c.2) ∈ phaseDomain T) :
    gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y c) x =
      primaryCoordinateChange i
        (phaseGradient T Q ((primaryCoordinateChange i).symm x) c.2) := by
  apply gradient_primaryCoordinateChange i
    (φ := fun y ↦ LeadingWave.FullModulation.phase T Q y c.2)
  have hs := (phase_smooth T Q).contDiffAt (isOpen_ball.mem_nhds
    (ball_subset_ball (by linarith [T.family.radius_pos] :
      T.family.radius ≤ 2 * T.family.radius) hx))
  have hc : ContDiffAt ℝ ∞ (fun y ↦ LeadingWave.FullModulation.phase T Q y c.2)
      ((primaryCoordinateChange i).symm x) :=
    hs.comp (f := fun y : E ↦ (y, c.2)) ((primaryCoordinateChange i).symm x)
      (contDiffAt_id.prodMk contDiffAt_const)
  exact hc.differentiableAt (by simp)

/-- The supplied retained root matches the SAME full source phase on the
literal pullback of its characteristic neighborhood. This applies to all free
covectors in that incidence domain. Smoothness and characteristicity come
from the original `T.currentChart Q`; no phase identity or analytic estimate
is assumed (`app:ch_response:eq:response-exact-phase`). -/
theorem exists_retained_full_source_root_domain
    {i row col : Fin (d + 1)} {A₀ : Coeff} {ξ : E} (hξ : ξ ≠ 0)
    {H : Coeff × Euclidean d → ℝ} {ε L μ ν : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i row col A₀ ξ H ε L μ ν) :
    ∃ V : Set (Coeff × E), IsOpen V ∧ (A₀, ξ) ∈ V ∧
      ∀ Q : _,
        let D : Set (E × Param) := {q |
          ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T ∧
          (Q.1 ((primaryCoordinateChange i).symm q.1),
            phaseGradient T Q ((primaryCoordinateChange i).symm q.1) q.2.2) ∈ V}
        IsOpen D ∧
        ContDiffOn ℝ ∞ (Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) D ∧
        ∀ q ∈ D,
          rootSuspension (fieldRoot (coordinateSplit i) Q.1 H)
            (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1) = 0 := by
  obtain ⟨V, hV, hbase, hmatch⟩ :=
    exists_retained_root_characteristic_neighborhood hξ hε hL hμ hν hH
  refine ⟨V, hV, hbase, ?_⟩
  intro Q D
  let F : E × Param → E × Euclidean d :=
    fun q ↦ ((primaryCoordinateChange i).symm q.1, q.2.2)
  let O : Set (E × Param) := F ⁻¹' phaseDomain T
  have hF : ContDiff ℝ ∞ F :=
    ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd.snd
  have hO : IsOpen O := isOpen_ball.preimage hF.continuous
  have hphysical (q : E × Param) (hq : q ∈ O) : (F q).1 ∈ U := by
    have ht : ((F q).1, (0, (F q).2)) ∈ (T.currentChart Q).target :=
      (LeadingWave.FullModulation.inclusion_mem_ball T
        (r := T.family.radius) (w := F q)).mpr hq
    exact (carrierPhase_gradient_mem_domain (T.currentChart Q) id ht).1
  have hQphys : ContDiffOn ℝ ∞ (fun q ↦ Q.1 (F q).1) O :=
    Q.2.1.comp hF.fst.contDiffOn hphysical
  have hg : ContDiffOn ℝ ∞ (fun q ↦ phaseGradient T Q (F q).1 (F q).2) O :=
    (phaseGradient_smooth T Q).comp hF.contDiffOn (fun _ hq ↦ hq)
  have hD : IsOpen D := by
    have ho := (hQphys.continuousOn.prodMk hg.continuousOn).isOpen_inter_preimage hO hV
    convert ho using 1
    ext q
    simp only [D, O, F, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  have hφ : ContDiffOn ℝ ∞ (Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) O :=
    (phase_smooth T Q).comp hF.contDiffOn (fun _ hq ↦
      ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius) hq)
  refine ⟨hD, hφ.mono (fun _ hq ↦ hq.1), ?_⟩
  intro q hq
  rw [T.fullSourcePhaseInCoordinates_gradient i Q hq.1]
  have hm := (hmatch _ hq.2).2.2.mp (phase_characteristic T Q hq.1)
  have hstate : spacetimeRootState
      (q.1, primaryCoordinateChange i (phaseGradient T Q (F q).1 (F q).2)) =
      adaptedPrimaryRootState (coordinateSplit i) (F q).1
        (phaseGradient T Q (F q).1 (F q).2) := by
    convert spacetimeRootState_primaryCoordinateChange i (F q).1
      (phaseGradient T Q (F q).1 (F q).2) using 1
    simp only [F, ContinuousLinearEquiv.apply_symm_apply]
  change (primaryCoordinateChange i (phaseGradient T Q (F q).1 (F q).2)) 0 -
    fieldRoot (coordinateSplit i) Q.1 H _ = 0
  rw [hstate, primaryCoordinateChange_apply, timeSpacePoint_time]
  simp only [fieldRoot, adaptedPrimaryRootState, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]
  simpa only [coordinateSplit_fst, F] using sub_eq_zero.mpr hm.symm

/-- The existing full-source cutoff representative has exactly the same
coordinate gradient on its full plateau. Thus it can use the incidence
domains above without changing the source cutoff or free covector support
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retainedPhaseExtension_coordinate_gradient_eq (i : Fin (d + 1)) (Q : _)
    {θ : E × Param → ℝ} {x : E} {c : Param}
    (hx : ((primaryCoordinateChange i).symm x, c) ∈ interior {v | θ v = 1}) :
    gradient (fun y ↦ ResponsePrimarySources.retainedPhaseExtension T Q θ
      ((primaryCoordinateChange i).symm y) c) x =
        gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y c) x := by
  have he := ResponsePrimarySources.retainedPhaseExtension_physical_eventuallyEq T Q hx
  exact (he.comp_tendsto (primaryCoordinateChange i).symm.continuous.continuousAt).gradient_eq

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
