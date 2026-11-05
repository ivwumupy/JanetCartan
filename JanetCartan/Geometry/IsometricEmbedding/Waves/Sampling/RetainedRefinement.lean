module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedGrades.Refinement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Neighborhood

/-!
# Sampling buffers inside the original retained cells

The raw-family cover supplies parent cells. Sampling additionally needs fixed
physical, full-phase and carrier buffers before varying fields are chosen.
The original Hamilton reference supplies all three; none is obtained by
assuming that an admissible immersion has already been selected.

The finite refinement covers the prescribed compact carrier support and keeps
the parent map, so its scalar domains, selected minors and flow witnesses are
still those of the original raw family. These are geometric inputs of
`MeasuredAmplitude.exists_finite_retained_sampling_realization`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation

/-- Construct all three sampling buffers within a specified original raw
cell, before the current immersion or scalar is chosen. The original parent
cell is retained (`app:ch_waves:thm:sampling`). -/
theorem exists_sampling_workingBall_in_retained_cell
    {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)}
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {z b : Euclidean 3} (hz : z ∈ parameterCube P.radius) {σ : ℝ}
    (hparent : ((0 : Euclidean n), (z, T.reference.spatialPatch z)) ∈
      ball ((0 : Euclidean n), (b, T.reference.spatialPatch b)) σ) :
    ∃ ρ > (0 : ℝ),
      closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (2 * ρ) ⊆
        ball ((0 : Euclidean n), (b, T.reference.spatialPatch b)) σ ∧
      closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (2 * ρ) ⊆ domain T ∧
      closedBall (0 : Euclidean n) (2 * ρ) ⊆ K ∧
      closedBall z (2 * ρ) ⊆ parameterInterior (2 * P.radius) := by
  obtain ⟨R, hR, hphase, hphysical⟩ :=
    UniformCoefficients.exists_carrier_center_ball T hP z hz hball
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_ball.mem_nhds hparent)
  obtain ⟨s, hs, hcarrier⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_parameterInterior _).mem_nhds (parameterCube_subset_doubledInterior hP.1 hz))
  let ρ := min R (min r s) / 4
  have hρ : 0 < ρ := div_pos (lt_min hR (lt_min hr hs)) (by norm_num)
  have hρR : 2 * ρ ≤ R := by
    have := min_le_left R (min r s)
    dsimp [ρ]
    linarith [lt_min hR (lt_min hr hs)]
  have hρr : 2 * ρ ≤ r := by
    have := (min_le_right R (min r s)).trans (min_le_left r s)
    dsimp [ρ]
    linarith [lt_min hR (lt_min hr hs)]
  have hρs : 2 * ρ ≤ s := by
    have := (min_le_right R (min r s)).trans (min_le_right r s)
    dsimp [ρ]
    linarith [lt_min hR (lt_min hr hs)]
  refine ⟨ρ, hρ, (closedBall_subset_closedBall hρr).trans hsub,
    (closedBall_subset_closedBall hρR).trans hphase, ?_,
    (closedBall_subset_closedBall hρs).trans hcarrier⟩
  intro x hx
  have hp : (x, (z, T.reference.spatialPatch z)) ∈
      closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) R := by
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using
      (mem_closedBall.mp hx).trans hρR
  exact interior_subset (hphysical hp).2.2

/-- Refine the original raw cover over the SAME prescribed compact carrier
support, with all sampling buffers chosen before fields and profiles. Every
new label retains an original parent cell. In particular, recentering may not
replace the parent's initial-scalar norm domain or selected flow
(`app:ch_waves:thm:sampling`). Angular refinement remains separate. -/
theorem exists_retained_sampling_refinement
    {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)}
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {S : Set (Euclidean 3)} (hS : IsCompact S) (hSinner : S ⊆ parameterInterior P.radius)
    (centers : Finset (parameterCube P.radius)) (σ : centers → ℝ)
    (hcover : ∀ z ∈ S, ∃ j : centers,
      ((0 : Euclidean n), (z, T.reference.spatialPatch z)) ∈
        ball ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) :
    ∃ labels : Finset S, ∃ parent : labels → centers, ∃ ρ : labels → ℝ,
      (∀ i, 0 < ρ i ∧
        closedBall ((0 : Euclidean n), (i.1.1, T.reference.spatialPatch i.1.1)) (2 * ρ i) ⊆
          ball ((0 : Euclidean n), ((parent i).1.1,
            T.reference.spatialPatch (parent i).1.1)) (σ (parent i)) ∧
        closedBall ((0 : Euclidean n), (i.1.1, T.reference.spatialPatch i.1.1)) (2 * ρ i) ⊆
          domain T ∧
        closedBall (0 : Euclidean n) (2 * ρ i) ⊆ K ∧
        closedBall i.1.1 (2 * ρ i) ⊆ parameterInterior (2 * P.radius)) ∧
      ∀ z ∈ S, ∃ i : labels, (z, T.reference.spatialPatch z) ∈
        ball (i.1.1, T.reference.spatialPatch i.1.1) (ρ i / 4) := by
  classical
  choose parent hp using fun z : S ↦ hcover z.1 z.2
  choose ρ hρ hparent hphase hspace hcarrier using fun z : S ↦
    exists_sampling_workingBall_in_retained_cell hP T hball
      (fun j ↦ (hSinner z.2 j).le) (hp z)
  let graph := fun z : Euclidean 3 ↦ (z, T.reference.spatialPatch z)
  have hgraph : ContinuousOn graph S := continuousOn_id.prodMk
    ((T.reference.spatialPatch_smooth hP).continuousOn.mono fun z hz ↦
      parameterCube_subset_doubledInterior hP.1 (fun j ↦ (hSinner hz j).le))
  let O := fun z : S ↦ (fun w : S ↦ graph w.1) ⁻¹' ball (graph z.1) (ρ z / 4)
  have hO (z : S) : IsOpen (O z) := isOpen_ball.preimage hgraph.domRestrict
  have hcov : (univ : Set S) ⊆ ⋃ z, O z := by
    intro z _
    exact mem_iUnion.mpr ⟨z, mem_ball_self (div_pos (hρ z) (by norm_num))⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨labels, hlabels⟩ := isCompact_univ.elim_finite_subcover O hO hcov
  refine ⟨labels, fun i ↦ parent i.1, fun i ↦ ρ i.1,
    fun i ↦ ⟨hρ i.1, hparent i.1, hphase i.1, hspace i.1, hcarrier i.1⟩, ?_⟩
  intro z hz
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hlabels (mem_univ (⟨z, hz⟩ : S)))
  exact ⟨⟨i, hi⟩, hzi⟩

end JanetCartan.Sampling
