module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.LocalFamily

/-!
# Actual full-phase inputs on a decorated patch

The patch is shrunk after choosing the quantitative family. Its doubled closed
cube stays in both the common target and the zero-section source ball. This
produces every field of `CarrierFullPhaseInput`, including both full momentum
comparisons, from primitive frame closeness (`app:ch_seed:prop:seed-actual-menu`,
Step 1).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase
open HamiltonPhase FrozenMenu FrozenPhaseReference

/-- The decoration constructed before the finite cover: frozen data, the
already constructed quantitative family, and only geometric patch containment.
The producer is `exists_quantitative_frozenReference_coverData` below
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
structure PatchQuantitativeFamily {n : ℕ} (P : Patch n)
    (U : Set (Euclidean n)) (hU : IsOpen U) where
  data : FrozenPatchData P
  family : LocalQuantitativeFamily data.localReference U hU
  patch_buffer : ∀ z ∈ parameterCube (2 * P.radius),
    (0, data.adapted.embedding.toContinuousLinearMap.adjoint (P.toFun z)) ∈
      ball data.adapted.baseData.2 (min family.radius (3 * family.sourceRadius))

namespace PatchQuantitativeFamily
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The common open target chosen before the current frame and every requested
accuracy (`app:lem:common-hamilton-phase`). -/
def target : Set (Euclidean n × (ℝ × Euclidean (n - 1))) :=
  ball (T.data.adapted.embedding T.data.adapted.baseData.1, T.data.adapted.baseData.2)
    T.family.radius

/-- Restrict the actual frozen chart without changing coordinates or phase
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
def referenceChart : ProjectionChart T.data.localReference.family.flow :=
  restrictChart T.data.localReference.family.chart (V := T.target) isOpen_ball
    ((ball_subset_ball (by linarith [T.family.radius_pos] : T.family.radius ≤ 2 * T.family.radius)).trans T.family.reference_target)

/-- A physical radius compatible with both common target and zero-section
source, independent of frame and accuracy (`app:lem:common-hamilton-phase`). -/
def physicalRadius : ℝ := min T.family.radius (3 * T.family.sourceRadius) / 2

/-- Positivity of the constructed physical radius. -/
theorem physicalRadius_pos : 0 < T.physicalRadius := by
  have hr := T.family.radius_pos
  have hs := T.family.sourceRadius_pos
  dsimp [physicalRadius]
  positivity

/-- Containment of the doubled closed patch over the physical ball in the
fixed full target (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem target_contains_closed {x : Euclidean n}
    (hx : x ∈ ball 0 T.physicalRadius) {z : Euclidean 3}
    (hz : z ∈ parameterCube (2 * P.radius)) :
    (x, (0, T.data.reference.spatialPatch z)) ∈ T.target := by
  have hr := T.physicalRadius_pos
  have hlt : T.physicalRadius < T.family.radius := by
    have hh := min_le_left T.family.radius (3 * T.family.sourceRadius)
    dsimp [physicalRadius] at hr ⊢
    linarith
  have hb := T.patch_buffer z hz
  rw [mem_ball] at hb
  change dist (x, (0, T.data.reference.spatialPatch z))
    (T.data.adapted.embedding T.data.adapted.baseData.1, T.data.adapted.baseData.2) < _
  rw [Prod.dist_eq, max_lt_iff]
  refine ⟨?_, hb.trans_le (min_le_left _ _)⟩
  simpa only [AdaptedSection.baseData, map_zero] using (mem_ball.mp hx).trans hlt

/-- The reference used by finite carrier assembly, with the smaller common
full target and the original literal frozen symbol and affine covector
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
def reference : CarrierPhaseReference P where
  sectionEmbedding := T.data.adapted.embedding
  symbol := frozenSymbol n
  flow := T.data.localReference.family.flow
  chart := T.referenceChart
  radius := T.physicalRadius
  radius_pos := T.physicalRadius_pos
  momentum_smooth := T.data.localReference.family.reference_control.momentum_smooth
  coordinates_smooth := by
    exact T.data.reference.coordinates_smooth.mono
      ((ball_subset_ball (by linarith [T.family.radius_pos] : T.family.radius ≤ 2 * T.family.radius)).trans T.family.reference_target)
  covector := T.data.localReference.covector
  phase_linear := fun q hq ↦ T.data.localReference.phase_linear q
    (T.family.reference_target (ball_subset_ball (by linarith [T.family.radius_pos] : T.family.radius ≤ 2 * T.family.radius) hq))
  patch_covector := T.data.reference.patch_covector
  target_contains := fun _ hx _ hz ↦ T.target_contains_closed hx (fun i ↦ (hz i).le)

/-- The current chart has exactly the reference target and exactly the chosen
coordinates of the quantitative family (`app:lem:common-hamilton-phase`). -/
def currentChart (Q : _) : ProjectionChart (T.family.flow Q) :=
  restrictChart (T.family.chart Q) (V := T.target) isOpen_ball
    ((ball_subset_ball (by linarith [T.family.radius_pos] : T.family.radius ≤ 2 * T.family.radius)).trans (T.family.target_contains Q))

/-- The doubled closed patch lies in the actual current zero-section source.
This is derived from the constructed source-ball description and the initial
position identity, without assuming any momentum comparison
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem current_section_source (Q : _) {u : Euclidean (n - 1)}
    (hu : T.reference.sectionEmbedding u ∈ ball 0 T.reference.radius)
    {z : Euclidean 3} (hz : z ∈ parameterCube (2 * P.radius)) :
    (0, (u, (0, T.reference.spatialPatch z))) ∈ (T.currentChart Q).source := by
  have hlt : T.physicalRadius < 3 * T.family.sourceRadius := by
    have hh := min_le_right T.family.radius (3 * T.family.sourceRadius)
    have hp := T.physicalRadius_pos
    dsimp [physicalRadius] at hp ⊢
    linarith
  have hball : (0, (u, (0, T.reference.spatialPatch z))) ∈
      ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius) := by
    have hb := (mem_ball.mp (T.patch_buffer z hz)).trans_le (min_le_right _ _)
    have hu' : ‖u‖ < T.physicalRadius := by
      simpa only [reference, mem_ball, dist_zero_right, LinearIsometry.norm_map] using hu
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_self]
    refine ⟨by linarith [T.family.sourceRadius_pos], ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa [AdaptedSection.baseData] using hu'.trans hlt, hb⟩
  have hadm := T.family.source_admissible Q hball
  rw [currentChart, restrictChart_source_eq _ _ _ (T.family.source_eq Q)]
  refine ⟨hball, ?_⟩
  change ((T.family.flow Q).position (0, (u, (0, T.reference.spatialPatch z))),
    (0, T.reference.spatialPatch z)) ∈ T.target
  rw [(T.family.flow Q).initial_position _ hadm.2, T.family.section_eq]
  exact T.target_contains_closed hu hz

/-- Construct an actual `CarrierFullPhaseInput` for every positive requested
comparison tolerance, using the same chosen charts and low neighborhood.
Both full Fréchet comparisons follow from the proved `C²` phase continuity;
no linear modulus is asserted (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_fullPhaseInput_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ d > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < d →
      ∃ I : CarrierFullPhaseInput T.reference
          (normalizedHomogeneousSymbol hU Q.1 Q.2.1) ε,
        I.flow = T.family.flow Q ∧ HEq I.chart (T.currentChart Q) := by
  obtain ⟨d, hd, hc⟩ := T.family.exists_momentum_comparison_threshold hε
  refine ⟨d, hd, fun Q hq ↦ ?_⟩
  let I : CarrierFullPhaseInput T.reference
      (normalizedHomogeneousSymbol hU Q.1 Q.2.1) ε := {
    flow := T.family.flow Q
    chart := T.currentChart Q
    target_eq := rfl
    section_eq := T.family.section_eq Q
    momentum_smooth := T.family.momentum_smooth Q
    coordinates_smooth := (T.family.coordinates_smooth Q).mono
      (ball_subset_ball (by linarith [T.family.radius_pos] : T.family.radius ≤ 2 * T.family.radius))
    section_source := fun _ hu _ hz ↦ T.current_section_source Q hu (fun i ↦ (hz i).le)
    comparison := fun q hqtarget ↦ by
      have hh := hc Q hq q (ball_subset_closedBall hqtarget)
      exact ⟨hh.1.le, hh.2.le⟩ }
  exact ⟨I, rfl, HEq.rfl⟩

/-- Sharp phase order `m` uses frame order `m+1` on the same current chart.
The parent instantiates the projected-frame loss two to obtain immersion
order `m+3` (`app:ch_seed:eq:seed-phase-tame`). -/
theorem current_phase_bound (Q : _) (m : ℕ) :
    cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
      T.data.adapted.baseData.2) T.family.radius) m
      (phase (T.currentChart Q).coordinates) ≤ T.family.coefficient m *
        (1 + cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m + 1) Q.1) :=
  T.family.phase_bound Q m

/-- In particular the identical current chart has `C⁵` phase comparison from
primitive `C⁶` frame comparison (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem current_phase_continuity (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m + 1)
        (Q.1 - fun _ ↦ cubeStress n) < d →
      cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
        T.data.adapted.baseData.2) T.family.radius) m
        (phase (T.currentChart Q).coordinates - phase T.reference.chart.coordinates) < ε :=
  T.family.phase_continuity m ε hε

end PatchQuantitativeFamily
end JanetCartan.ActualCarriers.CurrentFullPhase
