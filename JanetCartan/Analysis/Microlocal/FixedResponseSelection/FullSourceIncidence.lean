module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.FullSourceRoot
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Uniform incidence protection of the fixed full source

The actual retained Hamilton family gives full momentum comparison before
restriction to the carrier graph. Compactness converts it to one coefficient
threshold on the ENTIRE supplied compact source/parameter support. This
retains `T`, its free covector, and its original reference covector map.
Consumer: the source-incidence refinement for
`app:ch_response:eq:direct-envelope-profile`; the uniform positive-time
stationary/Hessian construction for the full parameters remains separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu LeadingWave.FullModulation
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d

/-- The original momentum comparison controls every free source covector,
not just its carrier-graph values. Its threshold precedes all source labels
and varying coefficient fields (`app:ch_response:eq:response-exact-phase`). -/
theorem exists_full_source_covector_comparison {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ w ∈ phaseDomain T,
        ‖phaseGradient T Q w.1 w.2 - T.reference.covector (0, w.2)‖ < ε := by
  obtain ⟨δ, hδ, hcomp⟩ := T.family.exists_momentum_comparison_threshold hε
  refine ⟨δ, hδ, ?_⟩
  intro Q hQ w hw
  have ht : (w.1, (0, w.2)) ∈ T.reference.chart.target :=
    (LeadingWave.FullModulation.inclusion_mem_ball T (r := T.family.radius) (w := w)).mpr hw
  rw [phaseGradient_eq_chartMomentum T Q hw,
    ← chartMomentum_eq_of_phase_linear T.reference.chart T.reference.covector
      T.reference.phase_linear ht]
  exact (hcomp Q hQ _ (ball_subset_closedBall ht)).1

private theorem full_source_physical_mem_frameBall
    (Q : {Q : E → Coeff // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    {w : E × Euclidean d} (hw : w ∈ phaseDomain T) :
    w.1 ∈ closedBall (0 : E) T.data.localReference.stateRadius := by
  have ht : (w.1, (0, w.2)) ∈ (T.currentChart Q).target :=
    (LeadingWave.FullModulation.inclusion_mem_ball T (r := T.family.radius) (w := w)).mpr hw
  have ha := (T.currentChart Q).source_admissible _
    ((T.currentChart Q).maps_to_source _ ht)
  have hs := T.family.state_mem Q _ ha
  rw [(T.currentChart Q).right_inverse _ ht] at hs
  exact (show dist w.1 0 ≤ dist (w.1, _) (0, T.data.center) by
    rw [Prod.dist_eq]; exact le_max_left _ _).trans hs

/-- The frozen full-source covector map is continuous on the literal full
source domain, as a restriction of the SAME reference chart's smooth momentum.
This supplies compactness for the source-incidence selector
(`app:ch_response:thm:response-compatible-choice`). -/
theorem continuousOn_frozen_full_source_pair :
    ContinuousOn (fun w : E × Param ↦
      (cubeStress (d + 1), T.reference.covector (0, w.2.2))) (domain T) := by
  have hmap : ContDiff ℝ ∞ (fun w : E × Param ↦ (w.1, ((0 : ℝ), w.2.2))) :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd.snd)
  have htarget (w : E × Param) (hw : w ∈ domain T) :
      (w.1, (0, w.2.2)) ∈ T.reference.chart.target :=
    (LeadingWave.FullModulation.inclusion_mem_ball T (r := T.family.radius)
      (w := (w.1, w.2.2))).mpr hw
  have hm := (T.reference.chart.contDiffOn_chartMomentum
    T.reference.momentum_smooth T.reference.coordinates_smooth).comp
      hmap.contDiffOn htarget
  apply (continuousOn_const.prodMk hm.continuousOn).congr
  intro w hw
  exact congrArg (fun v ↦ (cubeStress (d + 1), v))
    (chartMomentum_eq_of_phase_linear T.reference.chart T.reference.covector
      T.reference.phase_linear (htarget w hw)).symm

/-- A fixed compact full-source support whose FROZEN coefficient/covector
pairs lie in an open incidence neighborhood remains in that same neighborhood
for all sufficiently close admitted fields. The actual full momentum producer
proves the comparison; compactness gives one threshold before fields and
parameters. No source support or covector label is shrunk or replaced
(`app:ch_response:eq:response-exact-phase`, `app:ch_response:cor:current-atoms`). -/
theorem exists_uniform_full_source_pair_neighborhood
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {J : Set (E × Param)} (hJ : IsCompact J) (hJdomain : J ⊆ domain T)
    {V : Set (Coeff × E)} (hV : IsOpen V)
    (hJV : ∀ w ∈ J, (cubeStress (d + 1), T.reference.covector (0, w.2.2)) ∈ V) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ w ∈ J, (Q.1 w.1, phaseGradient T Q w.1 w.2.2) ∈ V := by
  let F : E × Param → Coeff × E :=
    fun w ↦ (cubeStress (d + 1), T.reference.covector (0, w.2.2))
  have hF : IsCompact (F '' J) :=
    hJ.image_of_continuousOn (T.continuousOn_frozen_full_source_pair.mono hJdomain)
  obtain ⟨ε, hε, hεV⟩ := hF.exists_thickening_subset_open hV (by
    rintro _ ⟨w, hw, rfl⟩
    exact hJV w hw)
  obtain ⟨δ₀, hδ₀, hcomp⟩ := T.exists_full_source_covector_comparison hε
  let δ := min T.family.threshold (min ε δ₀)
  refine ⟨δ, lt_min T.family.threshold_pos (lt_min hε hδ₀), min_le_left _ _, ?_⟩
  intro Q hQ w hw
  have hQdiff : ∀ y ∈ closedBall (0 : E) T.data.localReference.stateRadius,
      ContDiffAt ℝ 6 (Q.1 - fun _ ↦ cubeStress (d + 1)) y := by
    intro y hy
    exact ((Q.2.1.contDiffAt (hU.mem_nhds (hframe hy))).sub contDiffAt_const).of_le
      (by simp)
  have hv := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
    hQdiff (T.full_source_physical_mem_frameBall Q (w := (w.1, w.2.2)) (hJdomain hw)) (Nat.zero_le 6)
  have hvalue : dist (Q.1 w.1) (cubeStress (d + 1)) < ε := by
    have hh : ‖Q.1 w.1 - cubeStress (d + 1)‖ ≤
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hv
    exact hh.trans_lt (hQ.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hgrad : dist (phaseGradient T Q w.1 w.2.2)
      (T.reference.covector (0, w.2.2)) < ε :=
    hcomp Q (hQ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
      (w.1, w.2.2) (hJdomain hw)
  apply hεV
  exact mem_thickening_iff.mpr ⟨F w, mem_image_of_mem F hw, by
    rw [Prod.dist_eq]
    exact max_lt hvalue hgrad⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
