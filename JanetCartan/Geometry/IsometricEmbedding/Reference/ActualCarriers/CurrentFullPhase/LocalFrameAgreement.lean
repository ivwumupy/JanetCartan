module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.PatchFamily
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.LocalFrameAgreement.HamiltonFlows
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FrameExtension

/-!
# Original-target agreement of locally identical coefficient frames

The retained inner state ball and its transverse gap, produced by the common
initializer, identify the roots and trajectories. Both charts have the same
source ball, so inverse uniqueness preserves the entire original `T.target`.
This connects `app:ch_regular:eq:coefficient-extension` to
`app:lem:common-hamilton-phase`, including independent energy and covector
parameters. The consumers are initialized primary atoms and extended full
source stationary certificates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference NormalizedSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q Q' : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  {V : Set (Euclidean n)} (hV : IsOpen V) (hVU : V ⊆ U)
  {R : ℝ} (hR : R ≤ T.data.localReference.stateRadius)
  (hRV : closedBall (0 : Euclidean n) R ⊆ V)
  (he : EqOn Q.1 Q'.1 V)
  (hgap : ∀ z ∈ closedBall (0, T.data.center) R,
    ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
  (hrange : ∀ q ∈ (T.family.flow Q).time ×ˢ (T.family.flow Q).parameters,
    ((T.family.flow Q).position q, (T.family.flow Q).momentum q) ∈
      closedBall (0, T.data.center) R)
  (hrange' : ∀ q ∈ (T.family.flow Q').time ×ˢ (T.family.flow Q').parameters,
    ((T.family.flow Q').position q, (T.family.flow Q').momentum q) ∈
      closedBall (0, T.data.center) R)

include hV hVU hR hRV he hgap hrange hrange'

/-- Equality of actual coefficients on an open neighborhood of the retained
state ball identifies the original full state maps on their entire common
source ball (`app:lem:common-hamilton-phase`). The inner state ball and gap
are the literal witnesses retained by the common initializer. -/
theorem states_eqOn_of_frame_eqOn :
    EqOn (fun q ↦ ((T.family.flow Q).position q, (T.family.flow Q).momentum q))
      (fun q ↦ ((T.family.flow Q').position q, (T.family.flow Q').momentum q))
      (ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius)) := by
  have hdomain : normalizedSymbolDomain V ⊆ normalizedSymbolDomain U :=
    fun _ hz ↦ ⟨hVU hz.1, hz.2⟩
  have hball : closedBall (0, T.data.center) R ⊆ normalizedSymbolDomain V := by
    intro z hz
    refine ⟨hRV ?_, ?_⟩
    · exact (le_max_left _ _).trans (show max (dist z.1 0) (dist z.2 T.data.center) ≤ R from hz)
    · apply (mem_frozenSymbol_domain z).mp
      apply T.data.localReference.state_subset
      apply T.data.localReference.stateBall_subset
      rw [T.data.adapted.baseState_eq]
      exact closedBall_subset_closedBall hR hz
  have hν : T.data.adapted.normal ≠ 0 := by
    intro hz
    have hh := T.data.adapted.normal_unit
    rw [hz, norm_zero] at hh
    norm_num at hh
  apply LocalFrameAgreement.state_eqOn_of_local_symbol_eq
    (T.family.flow Q) (T.family.flow Q') (isOpen_normalizedSymbolDomain hV)
    hdomain hdomain
    ((contDiffOn_normalizedSymbol hU Q.2.1).mono hdomain)
    (fun z hz ↦ by
      change normalizedSymbol Q.1 z = normalizedSymbol Q'.1 z
      simp only [normalizedSymbol, he hz.1])
    hball (by positivity [T.family.sourceRadius_pos])
    T.data.adapted.embedding T.data.adapted.normal hν
    T.data.adapted.orthogonal T.data.adapted.spanning
    (T.family.section_eq Q) (T.family.section_eq Q') hgap
    (T.family.source_admissible Q) (T.family.source_admissible Q') hrange hrange'

/-- Direct inverse uniqueness on the same source ball identifies both charts
on the FULL original target, with no new radius or parameter restriction
(`app:lem:common-hamilton-phase`). -/
theorem coordinates_eqOn_of_frame_eqOn :
    EqOn (T.currentChart Q).coordinates (T.currentChart Q').coordinates T.target := by
  have hs := T.states_eqOn_of_frame_eqOn Q Q' hV hVU hR hRV he hgap hrange hrange'
  intro z hz
  have hzQ : z ∈ (T.currentChart Q).target := hz
  have hzQ' : z ∈ (T.currentChart Q').target := hz
  have hlift := (T.currentChart Q).maps_to_source z hzQ
  have hball : chartLift (T.currentChart Q).coordinates z ∈
      ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius) := by
    have hh := hlift.1
    rw [T.family.source_eq Q] at hh
    exact hh.1
  have hp : (T.family.flow Q').position (chartLift (T.currentChart Q).coordinates z) = z.1 :=
    (congrArg Prod.fst (hs hball)).symm.trans ((T.currentChart Q).right_inverse z hzQ)
  have hsource : chartLift (T.currentChart Q).coordinates z ∈ (T.currentChart Q').source := by
    change _ ∈ (T.family.chart Q').source ∩ _
    rw [T.family.source_eq Q']
    have hproj : (T.family.flow Q').augmentedProjection
        (chartLift (T.currentChart Q).coordinates z) = z := Prod.ext hp rfl
    refine ⟨⟨hball, ?_⟩, ?_⟩
    · change (T.family.flow Q').augmentedProjection _ ∈ (T.family.chart Q').target
      rw [hproj]
      exact T.family.target_contains Q'
        (ball_subset_ball (by linarith [T.family.radius_pos]) hz)
    · change (T.family.flow Q').augmentedProjection _ ∈ T.target
      rwa [hproj]
  have hh := ((T.currentChart Q').left_inverse _ hsource).symm
  rw [hp] at hh
  exact hh

/-- All full phase and coordinate jets agree on the unchanged open target.
There is no derivative reserve loss in this identification
(`app:lem:common-hamilton-phase`). -/
theorem phase_jets_eqOn_of_frame_eqOn :
    EqOn (phase (T.currentChart Q).coordinates) (phase (T.currentChart Q').coordinates) T.target ∧
      ∀ m : ℕ,
        EqOn (iteratedFDeriv ℝ m (T.currentChart Q).coordinates)
          (iteratedFDeriv ℝ m (T.currentChart Q').coordinates) T.target ∧
        EqOn (iteratedFDeriv ℝ m (phase (T.currentChart Q).coordinates))
          (iteratedFDeriv ℝ m (phase (T.currentChart Q').coordinates)) T.target := by
  have hc := T.coordinates_eqOn_of_frame_eqOn Q Q' hV hVU hR hRV he hgap hrange hrange'
  have hp : EqOn (phase (T.currentChart Q).coordinates)
      (phase (T.currentChart Q').coordinates) T.target := by
    intro z hz
    simp only [phase, hc hz]
  refine ⟨hp, fun m ↦ ⟨?_, ?_⟩⟩
  · intro z hz
    exact ((eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)
      (fun _ hw ↦ hc hw)).iteratedFDeriv ℝ m).eq_of_nhds
  · intro z hz
    exact ((eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)
      (fun _ hw ↦ hp hw)).iteratedFDeriv ℝ m).eq_of_nhds

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
