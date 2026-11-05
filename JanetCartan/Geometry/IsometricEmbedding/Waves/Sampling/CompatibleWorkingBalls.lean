module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.JointIncidentCover

/-!
# Sampling balls inside the same compatible carrier cell

Retain the original parent selected by the carrier/full-flow compatibility
cover. The new full raw ball lies inside that parent's working ball and its
carrier projection lies in the SAME compatibility cell. All choices precede
immersion, scalar, frequency and sample selection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.Sampling
open ContinuumRow FullPhaseCharts FullPhaseCharts.ActualComparison
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
open ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive

/-- Construct a sampling ball whose complete carrier projection stays in
the original compatible parent cell. This supplies the normal-field matching
input for `exists_compatible_retained_joint_sampling_transport_realization`, without
shrinking a finite cover selected before its local radii
(`app:ch_waves:thm:sampling`, `app:ch_background:eq:bg-T`). -/
theorem exists_sampling_workingBall_in_compatible_cell
    {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)}
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {z b : Euclidean 3} (hz : z ∈ parameterCube P.radius) {σ : ℝ}
    {cell : Set (Euclidean n × CarrierParameter)} (hcell : IsOpen cell)
    (hpoint : ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈ cell)
    (hgraph : MapsTo (carrierGraph T) cell
      (ball ((0 : Euclidean n), (b, T.reference.spatialPatch b)) σ)) :
    ∃ ρ > (0 : ℝ),
      closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (2 * ρ) ⊆
        ball ((0 : Euclidean n), (b, T.reference.spatialPatch b)) σ ∧
      closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (2 * ρ) ⊆ domain T ∧
      closedBall (0 : Euclidean n) (2 * ρ) ⊆ K ∧
      closedBall z (2 * ρ) ⊆ parameterInterior (2 * P.radius) ∧
      MapsTo (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        (w.1, (w.2.1 0, spectatorCenter w.2.1)))
        (closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (2 * ρ)) cell := by
  have hparent : ((0 : Euclidean n), (z, T.reference.spatialPatch z)) ∈
      ball ((0 : Euclidean n), (b, T.reference.spatialPatch b)) σ := by
    simpa only [carrierGraph, parameter_apply, carrierParameters_spectatorCenter] using hgraph hpoint
  obtain ⟨ρ₀, hρ₀, hparent₀, hphase₀, hspace₀, hcarrier₀⟩ :=
    exists_sampling_workingBall_in_retained_cell hP T hball hz hparent
  let project := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
    (w.1, (w.2.1 0, spectatorCenter w.2.1))
  have hspectator : Continuous (spectatorCenter : Euclidean 3 → Euclidean 2) := by
    unfold spectatorCenter
    fun_prop
  have hfirst : Continuous (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
      w.2.1 0) := by fun_prop
  have hproject : Continuous project :=
    continuous_fst.prodMk (hfirst.prodMk
      (hspectator.comp (continuous_fst.comp continuous_snd)))
  have hpre : IsOpen (project ⁻¹' cell) := hcell.preimage hproject
  have hpoint' : ((0 : Euclidean n), (z, T.reference.spatialPatch z)) ∈ project ⁻¹' cell := hpoint
  obtain ⟨s, hs, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hpre.mem_nhds hpoint')
  let ρ := min ρ₀ (s / 4)
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  have hle : 2 * ρ ≤ 2 * ρ₀ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  have hles : 2 * ρ ≤ s := by
    have hh : ρ ≤ s / 4 := min_le_right _ _
    linarith
  refine ⟨ρ, hρ, (closedBall_subset_closedBall hle).trans hparent₀,
    (closedBall_subset_closedBall hle).trans hphase₀,
    (closedBall_subset_closedBall hle).trans hspace₀,
    (closedBall_subset_closedBall hle).trans hcarrier₀, ?_⟩
  exact (closedBall_subset_closedBall hles).trans hsub

/-- Select parents from the original compatible carrier cover and retain
that SAME parent in every local sampling ball over the full joint support.
The complete carrier projection of each ball stays in its parent's cell,
so the produced scalar/normal compatibility is valid throughout subsequent
measurement and amplitude supports (`app:ch_waves:thm:sampling`). -/
theorem exists_joint_incident_compatible_workingBalls
    {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)}
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (W : Set (Euclidean 3 × Euclidean n))
    (hz : ∀ w ∈ W, w.1 ∈ parameterInterior P.radius)
    (centers : Finset (parameterCube P.radius)) (σ : centers → ℝ)
    (cell : centers → Set (Euclidean n × CarrierParameter))
    (hcell : ∀ j, IsOpen (cell j))
    (hgraph : ∀ j, MapsTo (carrierGraph T) (cell j)
      (ball ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)))
    (hcover : ∀ z ∈ parameterCube P.radius, ∃ j : centers,
      ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈ cell j) :
    ∃ parent : W → centers, ∃ ρ : W → ℝ, ∀ w,
      0 < ρ w ∧
      closedBall ((0 : Euclidean n), (w.1.1, T.reference.spatialPatch w.1.1)) (2 * ρ w) ⊆
        ball ((0 : Euclidean n), ((parent w).1.1,
          T.reference.spatialPatch (parent w).1.1)) (σ (parent w)) ∧
      closedBall ((0 : Euclidean n), (w.1.1, T.reference.spatialPatch w.1.1)) (2 * ρ w) ⊆
        domain T ∧
      closedBall (0 : Euclidean n) (2 * ρ w) ⊆ K ∧
      closedBall w.1.1 (2 * ρ w) ⊆ parameterInterior (2 * P.radius) ∧
      MapsTo (fun q : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        (q.1, (q.2.1 0, spectatorCenter q.2.1)))
        (closedBall ((0 : Euclidean n), (w.1.1, T.reference.spatialPatch w.1.1)) (2 * ρ w))
        (cell (parent w)) := by
  classical
  choose parent hp using fun w : W ↦ hcover w.1.1 (fun j ↦ (hz w.1 w.2 j).le)
  choose ρ hρ hparent hphase hspace hcarrier hcomp using fun w : W ↦
    exists_sampling_workingBall_in_compatible_cell hP T hball
      (fun j ↦ (hz w.1 w.2 j).le) (hcell (parent w)) (hp w) (hgraph (parent w))
  exact ⟨parent, ρ, fun w ↦ ⟨hρ w, hparent w, hphase w, hspace w, hcarrier w, hcomp w⟩⟩

end JanetCartan.Sampling
