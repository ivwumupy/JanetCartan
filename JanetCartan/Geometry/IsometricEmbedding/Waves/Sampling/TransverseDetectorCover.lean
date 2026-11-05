module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullDetectorMasks

/-!
# The original transverse detector on the full carrier support

The raw kernels use a detector on the transverse input, not on physical
covectors. Map its entire closed directional support through the explicit
frozen covector at EVERY original carrier point. The adapted projection
recovers the original directions exactly. Compactness then selects a cover
using the returned local radii without changing the detector or high-pass.

The primitive chart-admissibility condition is stated on these explicit
covectors in the original frozen incidence domain. Its later instantiation
must use the original buffered cutoffs, not a newly shrunken input support.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric NormedSpace
open scoped ContDiff Classical InnerProductSpace

namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open FullPhaseCharts.ActualPhase ContinuumRow.CanonicalConic SeparatedSampling

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The full incidence support of the ORIGINAL transverse detector, retaining
every point of its original carrier support (`app:ch_waves:thm:sampling`). -/
def transverseDetectorIncidenceSupport (Z : Set (Euclidean 3))
    (a : Euclidean (n - 1) → ℂ) : Set (Euclidean 3 × Euclidean n) :=
  (fun q : Euclidean 3 × Euclidean (n - 1) ↦
    (q.1, normalize (frozenInputCovector T q.1 q.2))) ''
      (Z ×ˢ detectorDirectionSupport a)

/-- The complete original input support is recovered exactly after the
literal adapted projection. In particular the construction keeps all carrier
and angular pairs, not just one incidence section
(`app:ch_waves:thm:sampling`). -/
theorem image_transverseDetectorIncidenceSupport
    (Z : Set (Euclidean 3)) (a : Euclidean (n - 1) → ℂ) :
    (fun w : Euclidean 3 × Euclidean n ↦
      (w.1, normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2))) ''
        transverseDetectorIncidenceSupport T Z a = Z ×ˢ detectorDirectionSupport a := by
  rw [transverseDetectorIncidenceSupport, Set.image_image]
  trans id '' (Z ×ˢ detectorDirectionSupport a)
  · apply Set.image_congr
    intro q hq
    have hn : ‖q.2‖ = 1 := mem_sphere_zero_iff_norm.mp hq.2.1
    have hne : q.2 ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    dsimp only [Function.comp_apply]
    rw [normalize_adjoint_frozenInputCovector T q.1 hne]
    simp only [NormedSpace.normalize, hn, inv_one, one_smul, id_eq]
  · exact Set.image_id _

/-- Smoothness of the original dispersion makes the full transverse support
compact; normalization is legal by the exact adjoint identity
(`app:ch_waves:thm:sampling`). -/
theorem transverseDetectorIncidenceSupport_compact {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZ : IsCompact Z)
    (hZP : Z ⊆ parameterInterior P.radius) (a : Euclidean (n - 1) → ℂ) :
    IsCompact (transverseDetectorIncidenceSupport T Z a) := by
  have hg : ContinuousOn (fun z ↦ gradient (dispersion T) (T.reference.spatialPatch z)) Z :=
    (FrozenIncidence.patch_gradient_smooth T hP).continuousOn.mono
      (fun z hz ↦ parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hZP hz i).le))
  have hc : ContinuousOn
      (fun q : Euclidean 3 × Euclidean (n - 1) ↦ frozenInputCovector T q.1 q.2)
      (Z ×ˢ detectorDirectionSupport a) := by
    have hgf : ContinuousOn (fun q : Euclidean 3 × Euclidean (n - 1) ↦
        gradient (dispersion T) (T.reference.spatialPatch q.1))
        (Z ×ˢ detectorDirectionSupport a) :=
      hg.comp continuousOn_fst (fun _ h ↦ h.1)
    unfold frozenInputCovector
    exact ((hgf.inner (𝕜 := ℝ) continuousOn_snd).smul continuousOn_const).add
        (T.data.adapted.embedding.continuous.continuousOn.comp continuousOn_snd (fun _ _ ↦ mem_univ _))
  have hn (q) (hq : q ∈ Z ×ˢ detectorDirectionSupport a) :
      frozenInputCovector T q.1 q.2 ≠ 0 := by
    have hn : ‖q.2‖ = 1 := mem_sphere_zero_iff_norm.mp hq.2.1
    exact frozenInputCovector_ne_zero T q.1
      (norm_ne_zero_iff.mp (by rw [hn]; norm_num))
  exact (hZ.prod (detectorDirectionSupport_compact a)).image_of_continuousOn
    (continuousOn_fst.prodMk ((hc.norm.inv₀
      (fun q hq ↦ norm_ne_zero_iff.mpr (hn q hq))).smul hc))

/-- The original frozen chart's derivative gap supplies every primitive
incidence input on the complete transverse support. `hchart` says only that
the prescribed buffered cutoffs lie in that original chart domain; incidence
and nonvanishing are proved for the literal covectors
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverseDetectorIncidenceSupport_spec {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZ : IsCompact Z)
    (hZP : Z ⊆ parameterInterior P.radius)
    {O : Set (Euclidean n)} {root : Euclidean n → Euclidean 3}
    (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean (n - 1) → ℂ)
    (hchart : ∀ z ∈ Z, ∀ θ ∈ detectorDirectionSupport a,
      normalize (frozenInputCovector T z θ) ∈ O) :
    IsCompact (transverseDetectorIncidenceSupport T Z a) ∧
      ∀ w ∈ transverseDetectorIncidenceSupport T Z a,
        w.1 ∈ parameterInterior P.radius ∧ w.2 ≠ 0 ∧
        incidence w.2 (P.toFun w.1) = 0 ∧
        fderiv ℝ (fun z ↦ incidence w.2 (P.toFun z)) w.1
          (EuclideanSpace.single 0 1) ≠ 0 := by
  refine ⟨transverseDetectorIncidenceSupport_compact T hP hZ hZP a, ?_⟩
  rintro w ⟨⟨z, θ⟩, ⟨hz, hθ⟩, rfl⟩
  have hn : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.mp hθ.1
  have hk := frozenInputCovector_ne_zero T z
    (norm_ne_zero_iff.mp (by rw [hn]; norm_num))
  refine ⟨hZP hz, norm_ne_zero_iff.mp (by rw [norm_normalize hk]; norm_num), ?_, ?_⟩
  · change incidence (normalize (frozenInputCovector T z θ)) (P.toFun z) = 0
    rw [NormedSpace.normalize, incidence_smul_direction,
      frozenInputCovector_incidence T hP (hZP hz), mul_zero]
  · exact abs_pos.mp (hP.2.1.trans_le (hroot.2.2 _ (hchart z hz θ hθ) z
      (fun i ↦ (hZP hz i).le)))

/-- The full transverse support lies in the compact unit incidence locus.
The constant physical detector here is only a bounding set; it does not
replace the original input mask (`app:ch_waves:thm:sampling`). -/
theorem transverseDetectorIncidenceSupport_subset_unit_incidence
    {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZP : Z ⊆ parameterInterior P.radius)
    (a : Euclidean (n - 1) → ℂ) :
    transverseDetectorIncidenceSupport T Z a ⊆
      fullDetectorIncidenceSupport P Z (fun _ ↦ (1 : ℂ)) := by
  rintro w ⟨⟨z, θ⟩, ⟨hz, hθ⟩, rfl⟩
  have hn : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.mp hθ.1
  have hk := frozenInputCovector_ne_zero T z
    (norm_ne_zero_iff.mp (by rw [hn]; norm_num))
  refine ⟨hz, ⟨mem_sphere_zero_iff_norm.mpr (norm_normalize hk), ?_⟩, ?_⟩
  · apply subset_tsupport (fun _ : Euclidean n ↦ (1 : ℂ))
    exact one_ne_zero
  · change incidence (normalize (frozenInputCovector T z θ)) (P.toFun z) = 0
    rw [NormedSpace.normalize, incidence_smul_direction,
      frozenInputCovector_incidence T hP (hZP hz), mul_zero]

/-- Choose common radial bounds for all original transverse directions and
carrier values before the local normal constructors return their radii.
No chart-domain inclusion or successful normal bound is needed for this
choice (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_transverseDetector_radial_bounds {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZ : IsCompact Z)
    (hZP : Z ⊆ parameterInterior P.radius) (a : Euclidean (n - 1) → ℂ) :
    ∃ amin amax : ℝ, 0 < amin ∧ amin ≤ amax ∧
      ∀ w ∈ transverseDetectorIncidenceSupport T Z a,
        amin ≤ (1 / 2) / ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2‖ ∧
        2 / ‖T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2‖ ≤ amax := by
  obtain ⟨amin, amax, hamin, hamax, hradial⟩ :=
    exists_fullDetector_radial_bounds T hP hZ hZP (fun _ ↦ (1 : ℂ))
  exact ⟨amin, amax, hamin, hamax, fun w hw ↦ hradial w
    (transverseDetectorIncidenceSupport_subset_unit_incidence T hP hZP a hw)⟩

/-- Choose actual carrier/cone masks covering EVERY nonzero original
transverse detector value over the complete original carrier support. The
same selected label supplies the carrier plateau and the angular ball.
The high-pass and the raw kernel need no modification
(`app:ch_waves:thm:sampling`). -/
theorem exists_transverseDetector_carrier_cover {c C : ℝ} (hP : P.IsValid c C)
    {Z : Set (Euclidean 3)} (hZ : IsCompact Z)
    (hZP : Z ⊆ parameterInterior P.radius)
    {O : Set (Euclidean n)} {root : Euclidean n → Euclidean 3}
    (hroot : P.IsIncidenceSection O root c)
    (a : Euclidean (n - 1) → ℂ)
    (hchart : ∀ z ∈ Z, ∀ θ ∈ detectorDirectionSupport a,
      normalize (frozenInputCovector T z θ) ∈ O)
    (ha : ∀ t : ℝ, 0 < t → ∀ η, a (t • η) = a η)
    (r d : transverseDetectorIncidenceSupport T Z a → ℝ)
    (hr : ∀ w, 0 < r w) (hd : ∀ w, 0 < d w)
    (localWeight : transverseDetectorIncidenceSupport T Z a → Point → ℝ)
    (hplateau : ∀ w z, WithLp.toLp 2 z ∈ closedBall w.1.1 (d w) → localWeight w z = 1) :
    ∃ labels : Finset (transverseDetectorIncidenceSupport T Z a),
      (∀ i : labels, T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2 ≠ 0) ∧
    ∃ b : labels → Point → ℝ,
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i)) ∧
      (∀ i z, b i z ∈ Icc (0 : ℝ) 1) ∧
      (∀ i z, b i z ≠ 0 → localWeight i.1 z = 1) ∧
      ∀ z ∈ Z, ∀ η : Euclidean (n - 1), η ≠ 0 → a η ≠ 0 → ∃ i : labels,
        b i z.ofLp = 1 ∧ normalize η ∈
          ball (normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2))
            (angularWidth (n := n)
              (T.data.adapted.embedding.toContinuousLinearMap.adjoint i.1.1.2) (r i.1) / 4) := by
  classical
  obtain ⟨hW, hspec⟩ := transverseDetectorIncidenceSupport_spec T hP hZ hZP hroot a hchart
  obtain ⟨labels, hηb, hcover⟩ := exists_finite_joint_incident_cover T hP hW
    (fun w hw ↦ (hspec w hw).1) (fun w hw ↦ (hspec w hw).2.1)
    (fun w hw ↦ (hspec w hw).2.2.1) r d hr hd localWeight hplateau
  obtain ⟨_B, _hB, b, hbs, hbc, hbb, hbone, _hbsupp, hbplateau⟩ :=
    exists_joint_cover_carrier_weights (fun i : labels ↦ i.1.1.1)
      (fun i ↦ d i.1) (fun i ↦ hd i.1) (fun i ↦ localWeight i.1) (fun i ↦ hplateau i.1)
  refine ⟨labels, hηb, b, fun i ↦ ⟨hbs i, hbc i⟩,
    fun i z ↦ ⟨(hbb i).nonneg z, (hbb i).le_bound z⟩, hbplateau, ?_⟩
  intro z hz η hη haη
  have hi : (z, normalize η) ∈ Z ×ˢ detectorDirectionSupport a :=
    ⟨hz, normalize_mem_detectorDirectionSupport a ha hη haη⟩
  rw [← image_transverseDetectorIncidenceSupport T Z a] at hi
  obtain ⟨w, hw, he⟩ := hi
  obtain ⟨i, hz', hdir, _hlocal⟩ := hcover w hw
  have hzeq : w.1 = z := congrArg Prod.fst he
  have hηeq : normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint w.2) =
      normalize η := congrArg Prod.snd he
  rw [hzeq] at hz'
  rw [hηeq] at hdir
  exact ⟨i, hbone i z.ofLp (ball_subset_closedBall hz'), hdir⟩

end JanetCartan.Sampling
