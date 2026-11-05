module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedRefinement
public import JanetCartan.Iteration.PhysicalSampling.Kernel

/-!
# A common scalar phase radius inside the original closed carrier cube

Choose the radius from the retained phase and the original interior incidence
label, before the current map and frequency. The full-normal carrier cutoff
then lies in the SAME closed cube used by the transverse sharp-band producer.
No already-selected sampling support or original detector is shrunk.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation Sampling

/-- Simultaneously retain the original phase/carrier extension plateau and the
closed carrier cube required by the actual scalar slice geometry. -/
theorem exists_scalar_sampling_workingRadius
    {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius) :
    ∃ ρ > (0 : ℝ),
      closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) (2 * ρ) ⊆ domain T ∧
      closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius) ∧
      closedBall z₀ (ρ / 4) ⊆ parameterCube P.radius := by
  obtain ⟨ρ₀, hρ₀, _hparent, hphase, _hphysical, hcarrier⟩ :=
    exists_sampling_workingBall_in_retained_cell hP T
      (K := closedBall 0 T.data.localReference.stateRadius) (Subset.refl _)
      (fun i ↦ (hz₀ i).le)
      (mem_ball_self (by norm_num : (0 : ℝ) < 1))
  obtain ⟨s, hs, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_parameterInterior P.radius).mem_nhds hz₀)
  let ρ := min ρ₀ s
  have hρ : 0 < ρ := lt_min hρ₀ hs
  have hρ₀' : 2 * ρ ≤ 2 * ρ₀ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  refine ⟨ρ, hρ, (closedBall_subset_closedBall hρ₀').trans hphase,
    (closedBall_subset_closedBall hρ₀').trans hcarrier, ?_⟩
  intro z hz i
  have hz' : z ∈ closedBall z₀ s := closedBall_subset_closedBall
    (by have hle : ρ ≤ s := min_le_right _ _; linarith : ρ / 4 ≤ s) hz
  exact (hsub hz' i).le

/-- Choose the SAME sampling radius inside the prescribed original leading
window, retaining the original closed carrier cube as well. The window is the
static pre-budget `σcover` cell, not a later scalar lower bound
(`new:sec:order-of-choices`, `app:ch_waves:thm:sampling`). -/
theorem exists_scalar_sampling_workingRadius_in_retained_cell
    {n : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {z₀ b : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius) {σ : ℝ}
    (hparent : ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ∈
      ball ((0 : Euclidean n), (b, T.reference.spatialPatch b)) σ) :
    ∃ ρ > (0 : ℝ),
      closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) (2 * ρ) ⊆
        ball ((0 : Euclidean n), (b, T.reference.spatialPatch b)) σ ∧
      closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) (2 * ρ) ⊆ domain T ∧
      closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius) ∧
      closedBall z₀ (ρ / 4) ⊆ parameterCube P.radius := by
  obtain ⟨ρ₀, hρ₀, hparent₀, hphase, _hphysical, hcarrier⟩ :=
    exists_sampling_workingBall_in_retained_cell hP T
      (K := closedBall 0 T.data.localReference.stateRadius) (Subset.refl _)
      (fun i ↦ (hz₀ i).le) hparent
  obtain ⟨s, hs, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_parameterInterior P.radius).mem_nhds hz₀)
  let ρ := min ρ₀ s
  have hρ : 0 < ρ := lt_min hρ₀ hs
  have hρ₀' : 2 * ρ ≤ 2 * ρ₀ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  refine ⟨ρ, hρ, (closedBall_subset_closedBall hρ₀').trans hparent₀,
    (closedBall_subset_closedBall hρ₀').trans hphase,
    (closedBall_subset_closedBall hρ₀').trans hcarrier, ?_⟩
  intro z hz i
  have hz' : z ∈ closedBall z₀ s := closedBall_subset_closedBall
    (by have hle : ρ ≤ s := min_le_right _ _; linarith : ρ / 4 ≤ s) hz
  exact (hsub hz' i).le

/-- The full scalar parameter cutoff's graph support lies in the original
closed carrier cube, so the actual sharp-band family applies at every nonzero
point of the global extension. -/
theorem scalar_parameter_cube_of_graph_support
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {z₀ z : Euclidean 3} {ρ : ℝ}
    (hcap : closedBall z₀ (ρ / 4) ⊆ parameterCube P.radius)
    (hgraph : (z, T.reference.spatialPatch z) ∈
      closedBall (z₀, T.reference.spatialPatch z₀) (ρ / 4)) :
    z ∈ parameterCube P.radius := by
  rw [← closedBall_prod_same] at hgraph
  exact hcap hgraph.1

end JanetCartan.PhysicalSampling
