module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Kernel

/-!
# One measurement radius for finitely many local carriers

The common radius depends only on the positive local radii and the fixed
reference, before the varying immersion in `app:ch_background:defn:bg-row`.
All three common cutoffs are the existing `FixedCutoffs` cutoffs.
-/

@[expose] public noncomputable section
open Set Metric
namespace JanetCartan.ContinuumRow.CommonMeasurement
open AmplitudeBound PeriodicLocalL2
variable {n N : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private theorem finite_positive_lower_bound (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (s : Finset ι) : ∃ b > 0, ∀ i ∈ s, b ≤ a i := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨b, hb, hba⟩ := ih
    refine ⟨min (a i) b, lt_min (ha i) hb, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hba j hj)

/-- Choose the common radius before any varying field. This also covers an
empty carrier family (`app:ch_background:defn:bg-row`). -/
theorem exists_common_radius (G : FlatReference n)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ r > 0, 6 * r < G.domain.chartRadius ∧ 6 * r < 1 / 2 ∧ ∀ i, 6 * r < a i := by
  obtain ⟨b, hb, hba⟩ := finite_positive_lower_bound a ha Finset.univ
  obtain ⟨r, hr, hG, hcell, hb'⟩ := FixedCutoffs.exists_radius G hb
  exact ⟨r, hr, hG, hcell, fun i ↦ hb'.trans_le (hba i (Finset.mem_univ i))⟩

variable {r a : ℝ}

/-- The ENTIRE common measurement support lies in the local open plateau
(`app:ch_background:defn:bg-row`). -/
theorem measurement_support_subset_local_plateau (hr : 0 < r) (ha : 0 < a)
    (hra : 3 * r ≤ 2 * a) :
    tsupport (FixedCutoffs.physical (n := n) hr 1) ⊆
      interior {x | FixedCutoffs.physical ha 1 x = 1} := by
  apply (FixedCutoffs.physical_tsupport hr 1).trans
  apply (ball_subset_closedBall.trans (closedBall_subset_closedBall ?_)).trans
    (FixedCutoffs.physical_plateau ha 1)
  norm_num at ⊢
  exact hra

/-- The physical product is literally the common measurement cutoff
(`app:ch_background:eq:bg-T`). -/
theorem physical_measurement_mul (hr : 0 < r) (ha : 0 < a)
    (hra : 3 * r ≤ 2 * a) (x : Euclidean n) :
    FixedCutoffs.physical hr 1 x * FixedCutoffs.physical ha 1 x =
      FixedCutoffs.physical hr 1 x := by
  by_cases hx : FixedCutoffs.physical hr 1 x = 0
  · simp [hx]
  · have hp := interior_subset (measurement_support_subset_local_plateau hr ha hra
      (subset_tsupport _ hx))
    change FixedCutoffs.physical ha 1 x = 1 at hp
    rw [hp, mul_one]

/-- The identical product statement on the normalized unit torus; this is the
cutoff supplied to both the carriers and image channel
(`app:ch_background:defn:bg-row`). -/
theorem periodic_measurement_mul (hr : 0 < r) (ha : 0 < a)
    (hrcell : 4 * r < 1 / 2) (hacell : 4 * a < 1 / 2) (hra : 3 * r ≤ 2 * a) :
    FixedCutoffs.periodic (n := n) hr hrcell 1 * FixedCutoffs.periodic ha hacell 1 =
      FixedCutoffs.periodic hr hrcell 1 := by
  ext x
  exact physical_measurement_mul hr ha hra (centeredTorusRepresentative x)

/-- Restricting a local measurement field replaces it by the common one;
all canonical functions remain unchanged (`app:ch_background:eq:bg-T`). -/
theorem restrictData_fixed_measurement (d : CarrierData n N)
    (hr : 0 < r) (ha : 0 < a) (hrcell : 4 * r < 1 / 2) (hacell : 4 * a < 1 / 2)
    (hra : 3 * r ≤ 2 * a)
    (hd : d.measurementCutoff = FixedCutoffs.periodic ha hacell 1) :
    restrictData d (FixedCutoffs.periodic hr hrcell 1) =
      {d with measurementCutoff := FixedCutoffs.periodic hr hrcell 1} := by
  have he : (fun x ↦ FixedCutoffs.periodic hr hrcell 1 x * d.measurementCutoff x) =
      FixedCutoffs.periodic hr hrcell 1 := by
    rw [hd]
    exact congrArg DFunLike.coe (periodic_measurement_mul hr ha hrcell hacell hra)
  simp only [restrictData, he]

end JanetCartan.ContinuumRow.CommonMeasurement
