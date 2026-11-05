module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.JointIncidentCover

/-!
# The original detector and its retained incidence section

Use the closed angular support of the original detector on the unit sphere.
Its image under the SAME frozen incidence section is the compact joint
carrier/direction support used by `JointIncidentRealization`. No smaller
support or independently chosen incidence root is introduced.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow.CanonicalConic

/-- The complete closed directional support of the original physical
detector, including its boundary (`app:ch_waves:thm:sampling`). -/
def detectorDirectionSupport {n : ℕ} (a : Euclidean n → ℂ) : Set (Euclidean n) :=
  sphere 0 1 ∩ tsupport a

/-- Compactness of the actual closed detector support
(`app:ch_waves:thm:sampling`). -/
theorem detectorDirectionSupport_compact {n : ℕ} (a : Euclidean n → ℂ) :
    IsCompact (detectorDirectionSupport a) :=
  (isCompact_sphere (0 : Euclidean n) 1).inter_right (isClosed_tsupport a)

/-- A nonzero homogeneous detector retains its normalized direction in the
closed support. There is no symmetry requirement
(`app:ch_waves:thm:sampling`). -/
theorem normalize_mem_detectorDirectionSupport {n : ℕ} (a : Euclidean n → ℂ)
    (ha : ∀ t : ℝ, 0 < t → ∀ k, a (t • k) = a k)
    {k : Euclidean n} (hk : k ≠ 0) (hak : a k ≠ 0) :
    NormedSpace.normalize k ∈ detectorDirectionSupport a := by
  refine ⟨mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hk), ?_⟩
  apply subset_tsupport a
  change a (‖k‖⁻¹ • k) ≠ 0
  rwa [ha _ (inv_pos.mpr (norm_pos_iff.mpr hk))]

/-- The joint support uses the original root at every original detector
direction (`app:ch_waves:thm:sampling`). -/
def sectionDetectorSupport {n : ℕ} (root : Euclidean n → Euclidean 3)
    (a : Euclidean n → ℂ) : Set (Euclidean 3 × Euclidean n) :=
  (fun k ↦ (root k, k)) '' detectorDirectionSupport a

/-- Projection recovers the entire original closed detector support, so the
joint construction cannot discard a direction (`app:ch_waves:thm:sampling`). -/
theorem snd_image_sectionDetectorSupport {n : ℕ} (root : Euclidean n → Euclidean 3)
    (a : Euclidean n → ℂ) :
    Prod.snd '' sectionDetectorSupport root a = detectorDirectionSupport a := by
  ext k
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact hv
  · intro hk
    exact ⟨(root k, k), ⟨k, hk, rfl⟩, rfl⟩

/-- The actual incidence section supplies compactness, interior carrier
points, nonzero directions, incidence, and its first-coordinate gap on the
whole detector support. These are the geometric inputs of
`exists_joint_incident_sampling_transport_realization`, derived from the
original frozen section (`app:ch_seed:prop:seed-phase-charts`). -/
theorem sectionDetectorSupport_spec {n : ℕ} {P : Patch n} {O : Set (Euclidean n)}
    {root : Euclidean n → Euclidean 3} {c : ℝ}
    (hc : 0 < c) (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean n → ℂ) (hsupport : detectorDirectionSupport a ⊆ O) :
    IsCompact (sectionDetectorSupport root a) ∧
      ∀ w ∈ sectionDetectorSupport root a,
        w.1 ∈ parameterInterior P.radius ∧ w.2 ≠ 0 ∧
        incidence w.2 (P.toFun w.1) = 0 ∧
        fderiv ℝ (fun z ↦ incidence w.2 (P.toFun z)) w.1
          (EuclideanSpace.single 0 1) ≠ 0 := by
  refine ⟨(detectorDirectionSupport_compact a).image_of_continuousOn
    ((hroot.1.continuousOn.mono hsupport).prodMk continuousOn_id), ?_⟩
  rintro w ⟨k, hk, rfl⟩
  have hsec := hroot.2.1 k (hsupport hk)
  have hne : k ≠ 0 := by
    have hn : ‖k‖ = 1 := mem_sphere_zero_iff_norm.mp hk.1
    exact norm_ne_zero_iff.mp (by rw [hn]; norm_num)
  refine ⟨hsec.1, hne, hsec.2.2.2, ?_⟩
  exact abs_pos.mp (hc.trans_le (hroot.2.2 k (hsupport hk)
    (root k) (fun i ↦ (hsec.1 i).le)))

/-- Specialize the joint support to the SAME root and patch of the frozen
finite menu. No current-root or prepared-mean theorem is needed
(`app:ch_waves:thm:sampling`). -/
theorem cover_sectionDetectorSupport_spec {n : ℕ} {D : CoverData n} {c C : ℝ}
    (hD : D.IsValid c C) (b : Fin D.chartCount) (j : Fin (D.patchCount b))
    (a : Euclidean n → ℂ) (hsupport : detectorDirectionSupport a ⊆ D.domain b) :
    IsCompact (sectionDetectorSupport (D.roots b j) a) ∧
      ∀ w ∈ sectionDetectorSupport (D.roots b j) a,
        w.1 ∈ parameterInterior (D.patches b j).radius ∧ w.2 ≠ 0 ∧
        incidence w.2 ((D.patches b j).toFun w.1) = 0 ∧
        fderiv ℝ (fun z ↦ incidence w.2 ((D.patches b j).toFun z)) w.1
          (EuclideanSpace.single 0 1) ≠ 0 :=
  sectionDetectorSupport_spec hD.1 (hD.2.2.2.2.1 b j).2 a hsupport

/-- Literal identification of the transverse direction image of the joint
support. The original adapted projection is unchanged
(`app:ch_waves:thm:sampling`). -/
theorem sectionDetectorSupport_direction_image {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (root : Euclidean n → Euclidean 3)
    (a : Euclidean n → ℂ) :
    (fun w : Euclidean 3 × Euclidean n ↦ NormedSpace.normalize
      (T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2)) ''
        sectionDetectorSupport root a = incidentDetectorDirections T (detectorDirectionSupport a) := by
  rw [sectionDetectorSupport, Set.image_image]
  rfl

/-- The SAME adapted projection is nonzero on every original detector
direction. Unlike a single-center cone statement, the incidence point here
varies with the original section (`app:ch_seed:prop:seed-phase-charts`). -/
theorem sectionDetector_tangential_ne_zero {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {O : Set (Euclidean n)} {root : Euclidean n → Euclidean 3}
    (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean n → ℂ) (hsupport : detectorDirectionSupport a ⊆ O)
    {k : Euclidean n} (hk : k ∈ detectorDirectionSupport a) :
    T.data.adapted.embedding.toContinuousLinearMap.adjoint k ≠ 0 := by
  have h := (sectionDetectorSupport_spec hP.2.1 hroot a hsupport).2
    (root k, k) ⟨k, hk, rfl⟩
  exact FrozenIncidence.tangential_direction_ne_zero T hP h.1 h.2.1 h.2.2.1

/-- Compactness and one common radial interval for the entire original
detector. This supplies the full normalized wide-band support required by
the local normal geometries before any radii or finite selection
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem sectionDetectorDirections_compact_radial {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {O : Set (Euclidean n)} {root : Euclidean n → Euclidean 3}
    (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean n → ℂ) (hsupport : detectorDirectionSupport a ⊆ O) :
    IsCompact (incidentDetectorDirections T (detectorDirectionSupport a)) ∧
      incidentDetectorDirections T (detectorDirectionSupport a) ⊆ sphere 0 1 ∧
      ∃ amin amax : ℝ, 0 < amin ∧ amin ≤ amax ∧
        ∀ k ∈ detectorDirectionSupport a,
          amin ≤ (1 / 2) / ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint k‖ ∧
          2 / ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint k‖ ≤ amax := by
  let e := T.data.adapted.embedding.toContinuousLinearMap.adjoint
  have he (k) (hk : k ∈ detectorDirectionSupport a) : 0 < ‖e k‖ :=
    norm_pos_iff.mpr (sectionDetector_tangential_ne_zero T hP hroot a hsupport hk)
  have hc : ContinuousOn e (detectorDirectionSupport a) := e.continuous.continuousOn
  have hn : ContinuousOn (fun k ↦ NormedSpace.normalize (e k)) (detectorDirectionSupport a) :=
    (hc.norm.inv₀ (fun k hk ↦ (he k hk).ne')).smul hc
  refine ⟨(detectorDirectionSupport_compact a).image_of_continuousOn hn, ?_, ?_⟩
  · rintro θ ⟨k, hk, rfl⟩
    exact mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize
      (norm_pos_iff.mp (he k hk)))
  · obtain ⟨M, hM⟩ := (detectorDirectionSupport_compact a).exists_bound_of_continuousOn hc
    obtain ⟨B, hB⟩ := (detectorDirectionSupport_compact a).exists_bound_of_continuousOn
      (hc.norm.inv₀ (fun k hk ↦ (he k hk).ne'))
    let amin := (1 / 2) / max M 1
    let amax := 2 * max B 1
    have hMpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hamin : 0 < amin := div_pos (by norm_num) hMpos
    have haminone : amin ≤ 1 / 2 := div_le_self (by norm_num) (le_max_right _ _)
    have hamax : 2 ≤ amax := by dsimp [amax]; linarith [le_max_right B 1]
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

/-- Choose the finite carrier/cone cover directly from the original detector
and frozen section, after both analytic cutoff radii are known. Every original
direction is retained at its SAME original root
(`app:ch_waves:thm:sampling`). -/
theorem exists_sectionDetector_joint_cover {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {O : Set (Euclidean n)} {root : Euclidean n → Euclidean 3}
    (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean n → ℂ) (hsupport : detectorDirectionSupport a ⊆ O)
    (r d : sectionDetectorSupport root a → ℝ)
    (hr : ∀ w, 0 < r w) (hd : ∀ w, 0 < d w)
    (ψ : sectionDetectorSupport root a → SeparatedSampling.Point → ℝ)
    (hplateau : ∀ w z, WithLp.toLp 2 z ∈ closedBall w.1.1 (d w) → ψ w z = 1) :
    ∃ labels : Finset (sectionDetectorSupport root a),
      (∀ i : labels, T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2 ≠ 0) ∧
      ∀ k ∈ detectorDirectionSupport a, ∃ i : labels,
        root k ∈ ball i.1.1.1 (d i.1 / 2) ∧
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∈
          ball (NormedSpace.normalize
            (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2))
            (angularWidth (n := n)
              (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2) (r i.1) / 4) ∧
        ψ i.1 (root k).ofLp = 1 := by
  obtain ⟨hW, hspec⟩ := sectionDetectorSupport_spec hP.2.1 hroot a hsupport
  obtain ⟨labels, hη, hcover⟩ := exists_finite_joint_incident_cover T hP hW
    (fun w hw ↦ (hspec w hw).1) (fun w hw ↦ (hspec w hw).2.1)
    (fun w hw ↦ (hspec w hw).2.2.1) r d hr hd ψ hplateau
  exact ⟨labels, hη, fun k hk ↦ hcover (root k, k) ⟨k, hk, rfl⟩⟩

end JanetCartan.Sampling
