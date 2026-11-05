module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.JointWeightedNormals
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.IncidenceScaling

/-!
# Full carrier support of a frozen detector

The section graph selects one incidence root with zero spectators. Sampling
integrates over all three carrier coordinates. The compact set below retains
every incident pair over the original carrier support, including all spectator
values. Its finite cover uses the actual local radii, with no new cutoff of
the original support. The literal frozen input covector identifies which
transverse inputs belong to this set.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric NormedSpace
open scoped ContDiff InnerProductSpace

namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open FullPhaseCharts.ActualPhase ContinuumRow.CanonicalConic SeparatedSampling

/-- All incident detector directions over the ORIGINAL compact carrier
support, rather than only its chosen section (`app:ch_waves:thm:sampling`). -/
def fullDetectorIncidenceSupport {n : ℕ} (P : Patch n)
    (Z : Set (Euclidean 3)) (a : Euclidean n → ℂ) : Set (Euclidean 3 × Euclidean n) :=
  {w | w.1 ∈ Z ∧ w.2 ∈ detectorDirectionSupport a ∧ incidence w.2 (P.toFun w.1) = 0}

/-- The complete incidence support is compact on the fixed carrier set.
Continuity is used only inside the original patch (`app:ch_waves:thm:sampling`). -/
theorem fullDetectorIncidenceSupport_compact {n : ℕ} {P : Patch n}
    {c C : ℝ} (hP : P.IsValid c C) {Z : Set (Euclidean 3)}
    (hZ : IsCompact Z) (hZP : Z ⊆ parameterCube P.radius) (a : Euclidean n → ℂ) :
    IsCompact (fullDetectorIncidenceSupport P Z a) := by
  let K := Z ×ˢ detectorDirectionSupport a
  have hK : IsCompact K := hZ.prod (detectorDirectionSupport_compact a)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun w : K ↦ incidence w.1.2 (P.toFun w.1.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    have hc₀ : ContinuousAt
        (fun q : Euclidean n × Euclidean 3 ↦ incidence q.1 (P.toFun q.2))
        (w.1.2, w.1.1) :=
      (Patch.contDiffAt_joint_incidence hP w.1.2 (hZP w.2.1)).continuousAt
    exact ContinuousAt.comp (f := fun v : K ↦ (v.1.2, v.1.1)) hc₀ (by fun_prop)
  have hclosed : IsClosed {w : K | incidence w.1.2 (P.toFun w.1.1) = 0} :=
    isClosed_eq hc continuous_const
  convert hclosed.isCompact.image continuous_subtype_val using 1
  ext w
  simp only [fullDetectorIncidenceSupport, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨hz, ha, hi⟩
    exact ⟨⟨w, hz, ha⟩, hi, rfl⟩
  · rintro ⟨v, hi, rfl⟩
    exact ⟨v.2.1, v.2.2, hi⟩

/-- The original section's derivative gap holds throughout its carrier cube,
so it gives transversality at EVERY retained incident pair, including nonzero
spectators (`app:ch_seed:prop:seed-phase-charts`). -/
theorem fullDetectorIncidenceSupport_spec {n : ℕ} {P : Patch n}
    {c C : ℝ} (hP : P.IsValid c C) {Z : Set (Euclidean 3)}
    (hZ : IsCompact Z) (hZP : Z ⊆ parameterInterior P.radius)
    {O : Set (Euclidean n)} {root : Euclidean n → Euclidean 3}
    (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean n → ℂ) (ha : detectorDirectionSupport a ⊆ O) :
    IsCompact (fullDetectorIncidenceSupport P Z a) ∧
      ∀ w ∈ fullDetectorIncidenceSupport P Z a,
        w.1 ∈ parameterInterior P.radius ∧ w.2 ≠ 0 ∧
        incidence w.2 (P.toFun w.1) = 0 ∧
        fderiv ℝ (fun z ↦ incidence w.2 (P.toFun z)) w.1
          (EuclideanSpace.single 0 1) ≠ 0 := by
  refine ⟨fullDetectorIncidenceSupport_compact hP hZ
    (fun z hz i ↦ (hZP hz i).le) a, ?_⟩
  intro w hw
  have hz := hZP hw.1
  have hk : w.2 ≠ 0 := by
    have hn : ‖w.2‖ = 1 := mem_sphere_zero_iff_norm.mp hw.2.1.1
    exact norm_ne_zero_iff.mp (by rw [hn]; norm_num)
  exact ⟨hz, hk, hw.2.2,
    abs_pos.mp (hP.2.1.trans_le (hroot.2.2 w.2 (ha hw.2.1) w.1
      (fun i ↦ (hz i).le)))⟩

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The physical covector of the literal frozen full chart at an arbitrary
carrier point and transverse input (`app:ch_seed:prop:seed-phase-charts`). -/
def frozenInputCovector (z : Euclidean 3) (η : Euclidean (n - 1)) : Euclidean n :=
  ⟪gradient (dispersion T) (T.reference.spatialPatch z), η⟫_ℝ •
    T.data.adapted.normal + T.data.adapted.embedding η

/-- The literal adapted projection recovers the complete input exactly;
no new existential coordinate map is selected (`app:ch_waves:thm:sampling`). -/
@[simp] theorem frozenInputCovector_adjoint (z : Euclidean 3) (η : Euclidean (n - 1)) :
    T.data.adapted.embedding.toContinuousLinearMap.adjoint (frozenInputCovector T z η) = η := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪frozenInputCovector T z η, T.data.adapted.embedding v⟫_ℝ = ⟪η, v⟫_ℝ
  simp only [frozenInputCovector, inner_add_left, inner_smul_left,
    T.data.adapted.orthogonal, mul_zero, zero_add]
  exact T.data.adapted.embedding.inner_map_map η v

/-- Nonzero transverse inputs give nonzero physical covectors at every
carrier value (`app:ch_waves:thm:sampling`). -/
theorem frozenInputCovector_ne_zero (z : Euclidean 3) {η : Euclidean (n - 1)}
    (hη : η ≠ 0) : frozenInputCovector T z η ≠ 0 := by
  intro h
  have he := frozenInputCovector_adjoint T z η
  rw [h, map_zero] at he
  exact hη he.symm

/-- The actual Hamilton dispersion implies incidence for every input. This
is a conclusion, not an assumed identification with an incidence root
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem frozenInputCovector_incidence {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius) (η : Euclidean (n - 1)) :
    incidence (frozenInputCovector T z η) (P.toFun z) = 0 := by
  have hzC : z ∈ parameterCube P.radius := fun i ↦ (hz i).le
  have hd := FrozenIncidence.determinant_incidence_eq T
    (parameterCube_subset_doubledInterior hP.1 hzC) (frozenInputCovector T z η)
  have hnormal : ⟪T.data.adapted.normal, frozenInputCovector T z η⟫_ℝ =
      ⟪gradient (dispersion T) (T.reference.spatialPatch z), η⟫_ℝ := by
    simp [frozenInputCovector, inner_add_right, inner_smul_right,
      T.data.adapted.orthogonal, T.data.adapted.normal_unit]
  rw [frozenInputCovector_adjoint, hnormal, sub_self, mul_zero,
    CubeCarrier.determinant_differential (hP.2.2.2.2.1 z hzC).1
      (hP.2.2.2.2.1 z hzC).2.1] at hd
  exact (mul_eq_zero.mp hd).resolve_left
    (CubeCarrier.determinant_normal_multiplier_ne_zero
      (hP.2.2.2.2.1 z hzC).1 (hP.2.2.2.2.1 z hzC).2.1)

/-- Normalizing the physical covector preserves the transverse direction
exactly, with its original positive radial scale (`app:ch_waves:thm:sampling`). -/
theorem normalize_adjoint_frozenInputCovector (z : Euclidean 3)
    {η : Euclidean (n - 1)} (hη : η ≠ 0) :
    normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint
      (normalize (frozenInputCovector T z η))) = normalize η := by
  change normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint
    (‖frozenInputCovector T z η‖⁻¹ • frozenInputCovector T z η)) = _
  rw [map_smul, frozenInputCovector_adjoint]
  exact normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr
    (frozenInputCovector_ne_zero T z hη))) η

/-- The frozen input covector retains the original radial scaling
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem frozenInputCovector_smul (z : Euclidean 3) (t : ℝ) (η : Euclidean (n - 1)) :
    frozenInputCovector T z (t • η) = t • frozenInputCovector T z η := by
  simp [frozenInputCovector, inner_smul_right, smul_add, smul_smul]

/-- On the whole incidence support the literal frozen input map is inverse
to the SAME adapted projection, with no choice of a new chart
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem frozenInputCovector_of_incidence {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z) = 0) :
    frozenInputCovector T z (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) = k := by
  unfold frozenInputCovector
  rw [← FrozenIncidence.dispersion_incidence T hP hz hinc]
  exact T.data.adapted.covector_decomposition k

/-- The entire closed directional input support in the ORIGINAL carrier
coordinates. The detector is evaluated on the explicit physical frozen
covector; this definition does not identify it with an unrelated transverse
mask (`app:ch_waves:thm:sampling`). -/
def fullDetectorInputSupport (Z : Set (Euclidean 3)) (a : Euclidean n → ℂ) :
    Set (Euclidean 3 × Euclidean (n - 1)) :=
  {q | q.1 ∈ Z ∧ q.2 ∈ sphere 0 1 ∧
    normalize (frozenInputCovector T q.1 q.2) ∈ detectorDirectionSupport a}

/-- The full carrier/direction support is exactly the image of ALL incident
detector pairs. This is an equality of the actual maps, including nonzero
spectators; the chosen section graph is not used
(`app:ch_waves:thm:sampling`). -/
theorem image_fullDetectorIncidenceSupport {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZP : Z ⊆ parameterInterior P.radius)
    (a : Euclidean n → ℂ) :
    (fun w : Euclidean 3 × Euclidean n ↦
      (w.1, normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2))) ''
        fullDetectorIncidenceSupport P Z a = fullDetectorInputSupport T Z a := by
  ext q
  constructor
  · rintro ⟨⟨z, k⟩, ⟨hz, hk, hinc⟩, rfl⟩
    have hkn : ‖k‖ = 1 := mem_sphere_zero_iff_norm.mp hk.1
    have hk₀ : k ≠ 0 := norm_ne_zero_iff.mp (by rw [hkn]; norm_num)
    have he := FrozenIncidence.tangential_direction_ne_zero T hP (hZP hz) hk₀ hinc
    refine ⟨hz, mem_sphere_zero_iff_norm.mpr (norm_normalize he), ?_⟩
    change normalize (frozenInputCovector T z
      (‖T.data.adapted.embedding.toContinuousLinearMap.adjoint k‖⁻¹ •
        T.data.adapted.embedding.toContinuousLinearMap.adjoint k)) ∈ _
    rw [frozenInputCovector_smul, frozenInputCovector_of_incidence T hP (hZP hz) hinc,
      normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr he))]
    simpa only [NormedSpace.normalize, hkn, inv_one, one_smul] using hk
  · rintro ⟨hz, hθ, ha⟩
    have hn : ‖q.2‖ = 1 := mem_sphere_zero_iff_norm.mp hθ
    have hθ₀ : q.2 ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    refine ⟨(q.1, normalize (frozenInputCovector T q.1 q.2)), ⟨hz, ha, ?_⟩, ?_⟩
    · rw [NormedSpace.normalize, incidence_smul_direction,
        frozenInputCovector_incidence T hP (hZP hz), mul_zero]
    · dsimp only
      rw [normalize_adjoint_frozenInputCovector T q.1 hθ₀]
      simp only [NormedSpace.normalize, hn, inv_one, one_smul]

/-- Compactness of the full input support follows from the literal
incidence correspondence and the proved nonzero adapted projection
(`app:ch_waves:thm:sampling`). -/
theorem fullDetectorInputSupport_compact {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZ : IsCompact Z)
    (hZP : Z ⊆ parameterInterior P.radius) (a : Euclidean n → ℂ) :
    IsCompact (fullDetectorInputSupport T Z a) := by
  rw [← image_fullDetectorIncidenceSupport T hP hZP a]
  apply (fullDetectorIncidenceSupport_compact hP hZ
    (fun z hz i ↦ (hZP hz i).le) a).image_of_continuousOn
  have he (w) (hw : w ∈ fullDetectorIncidenceSupport P Z a) :
      T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2 ≠ 0 := by
    have hn : ‖w.2‖ = 1 := mem_sphere_zero_iff_norm.mp hw.2.1.1
    exact FrozenIncidence.tangential_direction_ne_zero T hP (hZP hw.1)
      (norm_ne_zero_iff.mp (by rw [hn]; norm_num)) hw.2.2
  have hc : ContinuousOn (fun w : Euclidean 3 × Euclidean n ↦
      T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2)
      (fullDetectorIncidenceSupport P Z a) := by fun_prop
  exact continuousOn_fst.prodMk
    ((hc.norm.inv₀ (fun w hw ↦ norm_ne_zero_iff.mpr (he w hw))).smul hc)

/-- Every nonzero value of the ORIGINAL homogeneous physical detector lies
in this full input support. The scale and carrier coordinates remain literal
(`app:ch_waves:thm:sampling`). -/
theorem mem_fullDetectorInputSupport_of_nonzero
    {Z : Set (Euclidean 3)} (a : Euclidean n → ℂ)
    (ha : ∀ t : ℝ, 0 < t → ∀ k, a (t • k) = a k)
    {z : Euclidean 3} (hz : z ∈ Z) {η : Euclidean (n - 1)} (hη : η ≠ 0)
    (haη : a (frozenInputCovector T z η) ≠ 0) :
    (z, normalize η) ∈ fullDetectorInputSupport T Z a := by
  refine ⟨hz, mem_sphere_zero_iff_norm.mpr (norm_normalize hη), ?_⟩
  change normalize (frozenInputCovector T z (‖η‖⁻¹ • η)) ∈ _
  rw [frozenInputCovector_smul, normalize_smul_of_pos
    (inv_pos.mpr (norm_pos_iff.mpr hη))]
  exact normalize_mem_detectorDirectionSupport a ha
    (frozenInputCovector_ne_zero T z hη) haη

/-- One common positive radial interval covers the original normalized wide
band on the ENTIRE incidence support. The choice precedes the local analytic
radii, the finite subcover, and all current fields and frequencies
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_fullDetector_radial_bounds {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZ : IsCompact Z)
    (hZP : Z ⊆ parameterInterior P.radius) (a : Euclidean n → ℂ) :
    ∃ amin amax : ℝ, 0 < amin ∧ amin ≤ amax ∧
      ∀ w ∈ fullDetectorIncidenceSupport P Z a,
        amin ≤ (1 / 2) / ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2‖ ∧
        2 / ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2‖ ≤ amax := by
  let e := fun w : Euclidean 3 × Euclidean n ↦
    T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2
  have hc : ContinuousOn e (fullDetectorIncidenceSupport P Z a) := by fun_prop
  have he (w) (hw : w ∈ fullDetectorIncidenceSupport P Z a) : 0 < ‖e w‖ := by
    have hn : ‖w.2‖ = 1 := mem_sphere_zero_iff_norm.mp hw.2.1.1
    exact norm_pos_iff.mpr (FrozenIncidence.tangential_direction_ne_zero T hP (hZP hw.1)
      (norm_ne_zero_iff.mp (by rw [hn]; norm_num)) hw.2.2)
  have hW := fullDetectorIncidenceSupport_compact hP hZ (fun z hz i ↦ (hZP hz i).le) a
  obtain ⟨M, hM⟩ := hW.exists_bound_of_continuousOn hc
  obtain ⟨B, hB⟩ := hW.exists_bound_of_continuousOn
    (hc.norm.inv₀ (fun w hw ↦ (he w hw).ne'))
  let amin := (1 / 2) / max M 1
  let amax := 2 * max B 1
  have hMpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hamin : 0 < amin := div_pos (by norm_num) hMpos
  have haminone : amin ≤ 1 / 2 := div_le_self (by norm_num) (le_max_right _ _)
  have hamax : 2 ≤ amax := by dsimp [amax]; linarith [le_max_right B 1]
  refine ⟨amin, amax, hamin, by linarith, ?_⟩
  intro w hw
  constructor
  · exact div_le_div_of_nonneg_left (by norm_num) (he w hw)
      ((hM w hw).trans (le_max_left _ _))
  · have hb : ‖e w‖⁻¹ ≤ max B 1 := by
      have hb' := (hB w hw).trans (le_max_left B 1)
      change ‖‖e w‖⁻¹‖ ≤ max B 1 at hb'
      simpa only [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using hb'
    change 2 / ‖e w‖ ≤ 2 * max B 1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)

end JanetCartan.Sampling
