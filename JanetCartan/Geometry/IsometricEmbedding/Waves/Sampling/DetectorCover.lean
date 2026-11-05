module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedRefinement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.IndexedRealization

/-!
# Cone covers chosen after the actual local sampling radii

The original compact set of incident physical directions is mapped through
its SAME adapted transverse projection. Compactness selects a finite cover
using the returned local radii; no previously chosen cone is assumed to fit a
smaller radius. The local analytic families can be retained by
`MeasuredAmplitude.exists_indexed_retained_sampling_realization`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow.CanonicalConic

/-- Original detector directions in the literal transverse input coordinates.
The set retains every direction of the prescribed compact incident support
(`app:ch_waves:thm:sampling`). -/
def incidentDetectorDirections {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (S : Set (Euclidean n)) :
    Set (Euclidean (n - 1)) :=
  (fun k ↦ NormedSpace.normalize
    (T.data.adapted.embedding.toContinuousLinearMap.adjoint k)) '' S

/-- The original incidence support has a compact unit-direction image.
Nonvanishing is proved from the actual frozen characteristic relation, rather
than assumed for the adapted projection (`app:ch_seed:prop:seed-phase-charts`). -/
theorem incidentDetectorDirections_compact {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {S : Set (Euclidean n)} (hS : IsCompact S)
    (hne : ∀ k ∈ S, k ≠ 0) (hinc : ∀ k ∈ S, incidence k (P.toFun z) = 0) :
    IsCompact (incidentDetectorDirections T S) ∧
      incidentDetectorDirections T S ⊆ sphere 0 1 := by
  let e := T.data.adapted.embedding.toContinuousLinearMap.adjoint
  have he (k) (hk : k ∈ S) : e k ≠ 0 :=
    FrozenIncidence.tangential_direction_ne_zero T hP hz (hne k hk) (hinc k hk)
  have hc : ContinuousOn (fun k ↦ NormedSpace.normalize (e k)) S := by
    exact (e.continuous.continuousOn.norm.inv₀ (fun k hk ↦ norm_ne_zero_iff.mpr (he k hk))).smul
      e.continuous.continuousOn
  refine ⟨hS.image_of_continuousOn hc, ?_⟩
  rintro θ ⟨k, hk, rfl⟩
  simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize (he k hk)

/-- Choose one positive radial interval covering the original normalized
wide band for every incident direction. Compactness and the actual nonzero
adapted projection supply both bounds, before any local normal geometry
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_incidentDetector_radial_bounds {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {S : Set (Euclidean n)} (hS : IsCompact S)
    (hne : ∀ k ∈ S, k ≠ 0) (hinc : ∀ k ∈ S, incidence k (P.toFun z) = 0) :
    ∃ amin amax : ℝ, 0 < amin ∧ amin ≤ amax ∧
      ∀ k ∈ S, amin ≤ (1 / 2) / ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint k‖ ∧
        2 / ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint k‖ ≤ amax := by
  let e := T.data.adapted.embedding.toContinuousLinearMap.adjoint
  have he (k) (hk : k ∈ S) : 0 < ‖e k‖ := norm_pos_iff.mpr
    (FrozenIncidence.tangential_direction_ne_zero T hP hz (hne k hk) (hinc k hk))
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn e.continuous.continuousOn
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
    (e.continuous.continuousOn.norm.inv₀ (fun k hk ↦ (he k hk).ne'))
  let amin := (1 / 2) / max M 1
  let amax := 2 * max B 1
  have hMpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hamin : 0 < amin := div_pos (by norm_num) hMpos
  have hamax : 2 ≤ amax := by dsimp [amax]; linarith [le_max_right B 1]
  have haminone : amin ≤ 1 / 2 := by
    exact div_le_self (by norm_num) (le_max_right _ _)
  refine ⟨amin, amax, hamin, by linarith, ?_⟩
  intro k hk
  constructor
  · exact div_le_div_of_nonneg_left (by norm_num) (he k hk)
      ((hM k hk).trans (le_max_left _ _))
  · have hb : ‖e k‖⁻¹ ≤ max B 1 := by
      have hb' := (hB k hk).trans (le_max_left B 1)
      change ‖‖e k‖⁻¹‖ ≤ max B 1 at hb'
      simpa only [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using hb'
    change 2 / ‖e k‖ ≤ 2 * max B 1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)

/-- Select a finite cone cover using the radii of the actual local
constructors. Every selected label is an original incident direction, so
all associated parent cells, flows and scalar domains can be restricted
without reselecting them. The cover has precisely the quarter-width required
by `AngularPartition` (`app:ch_waves:thm:sampling`). -/
theorem exists_finite_incidentDetector_cover {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {S : Set (Euclidean n)} (hS : IsCompact S)
    (hne : ∀ k ∈ S, k ≠ 0) (hinc : ∀ k ∈ S, incidence k (P.toFun z) = 0)
    (r : S → ℝ) (hr : ∀ k, 0 < r k) :
    ∃ labels : Finset S,
      (∀ i : labels, T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1 ≠ 0) ∧
      (∀ i : labels, 0 < r i.1) ∧
      ∀ θ ∈ incidentDetectorDirections T S, ∃ i : labels,
        θ ∈ ball (NormedSpace.normalize
          (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1))
          (angularWidth (n := n)
            (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1) (r i.1) / 4) := by
  classical
  let e := T.data.adapted.embedding.toContinuousLinearMap.adjoint
  have he (k : S) : e k.1 ≠ 0 :=
    FrozenIncidence.tangential_direction_ne_zero T hP hz (hne k.1 k.2) (hinc k.1 k.2)
  let O (k : S) := ball (NormedSpace.normalize (e k.1))
    (angularWidth (n := n) (e k.1) (r k) / 4)
  have hcover : incidentDetectorDirections T S ⊆ ⋃ k : S, O k := by
    rintro θ ⟨k, hk, rfl⟩
    exact mem_iUnion.mpr ⟨⟨k, hk⟩, mem_ball_self
      (div_pos (angularWidth_spec (he ⟨k, hk⟩) (hr ⟨k, hk⟩)).1 (by norm_num))⟩
  obtain ⟨labels, hlabels⟩ := (incidentDetectorDirections_compact T hP hz hS hne hinc).1.elim_finite_subcover
    O (fun _ ↦ isOpen_ball) hcover
  refine ⟨labels, fun i ↦ he i.1, fun i ↦ hr i.1, ?_⟩
  intro θ hθ
  obtain ⟨i, hi, hθi⟩ := mem_iUnion₂.mp (hlabels hθ)
  exact ⟨⟨i, hi⟩, hθi⟩

end JanetCartan.Sampling
