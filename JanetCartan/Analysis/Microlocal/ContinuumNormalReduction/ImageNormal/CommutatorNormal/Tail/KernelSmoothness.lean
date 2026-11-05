module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Tail.SectionJets

/-!
# Smoothness of the genuine noncompact intermediate integral

For `app:ch_background:prop:bg-frame`, Step 1, translate the second Bessel
factor to a fixed integrable density. All spatial derivatives then fall on
the separated section. Its proved primitive jet bounds justify every
interchange of derivative and integral over the full Euclidean space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Translation puts the singular second Bessel factor in a fixed L¹
density, retaining the entire intermediate domain
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageCommutatorTailKernel_eq_translate_integral (χ β : E → ℝ) (p : E × E) :
    imageCommutatorTailKernel χ β p = ∫ z, imageBesselKernel z *
      imageCommutatorTailSection χ β (p + (0, z)) := by
  unfold imageCommutatorTailKernel
  rw [← integral_add_right_eq_self (fun z ↦
    imageCommutatorTailSection χ β (p.1, z) * imageBesselKernel (z - p.2)) p.2]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [add_sub_cancel_right]
  rw [add_comm z p.2, mul_comm]
  congr 2
  ext <;> simp

private theorem bessel_translate_integral_smooth
    (F : E × E → ℝ) (hF : ContDiff ℝ ∞ F)
    (hbound : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p, ‖iteratedFDeriv ℝ n F p‖ ≤ C) :
    ContDiff ℝ ∞ (fun p ↦ ∫ z : E, imageBesselKernel z * F (p + (0, z))) ∧
    ∀ n : ℕ, ∀ p : E × E,
      iteratedFDeriv ℝ n (fun q ↦ ∫ z : E, imageBesselKernel z * F (q + (0, z))) p =
        ∫ z : E, imageBesselKernel z • iteratedFDeriv ℝ n F (p + (0, z)) := by
  choose C hC bC using hbound
  let A : E → E × E → ℝ := fun z p ↦ imageBesselKernel z • F (p + (0, z))
  have hA (z : E) : ContDiff ℝ ∞ (A z) :=
    (hF.comp (contDiff_id.add contDiff_const)).const_smul _
  have he (n : ℕ) (z : E) (p : E × E) :
      iteratedFDeriv ℝ n (A z) p = imageBesselKernel z •
        iteratedFDeriv ℝ n F (p + (0, z)) := by
    rw [show A z = fun p ↦ imageBesselKernel z • F (p + (0, z)) from rfl,
      iteratedFDeriv_const_smul_apply' (f := fun p : E × E ↦ F (p + (0, z))) ((hF.comp (contDiff_id.add contDiff_const)).contDiffAt.of_le (by simp)),
      iteratedFDeriv_comp_add_right]
  have hm (n : ℕ) (p : E × E) : AEStronglyMeasurable
      (fun z ↦ iteratedFDeriv ℝ n (A z) p) volume := by
    simp_rw [he]
    exact measurable_imageBesselKernel.aestronglyMeasurable.smul
      (((hF.continuous_iteratedFDeriv (by simp)).comp
        (continuous_const.add (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
  have hb (n : ℕ) (z : E) (p : E × E) :
      ‖iteratedFDeriv ℝ n (A z) p‖ ≤ imageBesselKernel z * C n := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (imageBesselKernel_nonneg z)]
    exact mul_le_mul_of_nonneg_left (bC n _) (imageBesselKernel_nonneg z)
  have hint (n : ℕ) (p : E × E) : Integrable (fun z ↦ iteratedFDeriv ℝ n (A z) p) :=
    (integrable_imageBesselKernel.mul_const (C n)).mono' (hm n p) (ae_of_all _ fun z ↦ hb n z p)
  have hid (n : ℕ) (p : E × E) :
      iteratedFDeriv ℝ n (fun q ↦ ∫ z, A z q) p = ∫ z, iteratedFDeriv ℝ n (A z) p := by
    exact MeasureEnvelopes.iteratedFDeriv_integral_of_dominated (r := n)
      (b := fun j z ↦ imageBesselKernel z * C j) isOpen_univ
      (ae_of_all _ fun z q _ ↦ (hA z).contDiffAt.of_le (by simp))
      (fun j _ q _ ↦ hm j q) (fun j _ ↦ integrable_imageBesselKernel.mul_const (C j))
      (fun j _ ↦ ae_of_all _ fun z q _ ↦ hb j z q) le_rfl (mem_univ p)
  have hd (n : ℕ) (p : E × E) : HasFDerivAt
      (fun q ↦ ∫ z, iteratedFDeriv ℝ n (A z) q)
      (∫ z, fderiv ℝ (iteratedFDeriv ℝ n (A z)) p) p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun q z ↦ fderiv ℝ (iteratedFDeriv ℝ n (A z)) q)
      (s := univ) (bound := fun z ↦ imageBesselKernel z * C (n + 1)) (univ_mem : univ ∈ 𝓝 p)
    · exact Eventually.of_forall (hm n)
    · exact hint n p
    · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E × E) ℝ).continuous.comp_aestronglyMeasurable (hm (n + 1) p)
    · exact ae_of_all _ fun z q _ ↦ by
        simpa only [norm_fderiv_iteratedFDeriv] using hb (n + 1) z q
    · exact integrable_imageBesselKernel.mul_const (C (n + 1))
    · exact ae_of_all _ fun z q _ ↦
        ((hA z).contDiffAt.differentiableAt_iteratedFDeriv
          (m := n) (by exact_mod_cast ENat.natCast_lt_top n)).hasFDerivAt
  refine ⟨?_, fun n p ↦ (hid n p).trans (by simp_rw [he])⟩
  rw [← contDiffOn_univ]
  apply contDiffOn_of_differentiableOn
  intro n _ p _
  have hdf : Differentiable ℝ (fun q ↦ ∫ z, iteratedFDeriv ℝ n (A z) q) :=
    fun q ↦ (hd n q).differentiableAt
  have heq : (fun q ↦ iteratedFDerivWithin ℝ n (fun p ↦ ∫ z, A z p) univ q) =
      fun q ↦ ∫ z, iteratedFDeriv ℝ n (A z) q := by
    funext q
    rw [iteratedFDerivWithin_univ, hid]
  change DifferentiableWithinAt ℝ
    (fun q ↦ iteratedFDerivWithin ℝ n (fun p ↦ ∫ z, A z p) univ q) univ p
  rw [heq]
  exact (hdf p).differentiableWithinAt

/-- The actual scalar tail kernel is jointly smooth. All domination
hypotheses are discharged by the Bessel mass and the proved primitive
section bounds (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_imageCommutatorTailKernel
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) :
    ContDiff ℝ ∞ (imageCommutatorTailKernel χ β) := by
  have hb (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p,
      ‖iteratedFDeriv ℝ n (imageCommutatorTailSection χ β) p‖ ≤ C := by
    obtain ⟨C, hC, hb⟩ := exists_imageCommutatorTailSection_jet_bound χ β hχ hχc hβ hβc hδ hplateau n
    exact ⟨C, hC, hb n le_rfl⟩
  simpa only [funext (imageCommutatorTailKernel_eq_translate_integral χ β)] using
    (bessel_translate_integral_smooth _
      (contDiff_imageCommutatorTailSection χ β hχ hβ hδ hplateau) hb).1

/-- Every joint derivative passes through the full intermediate integral;
the derivatives act on both cutoffs and the first Bessel factor
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem iteratedFDeriv_imageCommutatorTailKernel
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)
    (n : ℕ) (p : E × E) :
    iteratedFDeriv ℝ n (imageCommutatorTailKernel χ β) p =
      ∫ z, imageBesselKernel z •
        iteratedFDeriv ℝ n (imageCommutatorTailSection χ β) (p + (0, z)) := by
  have hb (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p,
      ‖iteratedFDeriv ℝ n (imageCommutatorTailSection χ β) p‖ ≤ C := by
    obtain ⟨C, hC, hb⟩ := exists_imageCommutatorTailSection_jet_bound χ β hχ hχc hβ hβc hδ hplateau n
    exact ⟨C, hC, hb n le_rfl⟩
  rw [funext (imageCommutatorTailKernel_eq_translate_integral χ β)]
  exact (bessel_translate_integral_smooth _
    (contDiff_imageCommutatorTailSection χ β hχ hβ hδ hplateau) hb).2 n p

/-- The unit Bessel mass transfers each section budget to the literal
kernel without increasing the constant (`app:ch_background:prop:bg-frame`,
Step 1). Combined with the primitive section estimate, this is a finite
kernel-jet estimate derived from the cutoff jets and positive gap. -/
theorem norm_iteratedFDeriv_imageCommutatorTailKernel_le
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)
    (n : ℕ) (C : ℝ)
    (hb : ∀ p, ‖iteratedFDeriv ℝ n (imageCommutatorTailSection χ β) p‖ ≤ C)
    (p : E × E) : ‖iteratedFDeriv ℝ n (imageCommutatorTailKernel χ β) p‖ ≤ C := by
  rw [iteratedFDeriv_imageCommutatorTailKernel χ β hχ hχc hβ hβc hδ hplateau]
  calc
    _ ≤ ∫ z : E, imageBesselKernel z * C := by
      apply norm_integral_le_of_norm_le (integrable_imageBesselKernel.mul_const C)
      exact ae_of_all _ fun z ↦ by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (imageBesselKernel_nonneg z)]
        exact mul_le_mul_of_nonneg_left (hb _) (imageBesselKernel_nonneg z)
    _ = C := by rw [integral_mul_const, integral_imageBesselKernel, one_mul]

/-- Joint smoothness of the source-localized kernel that will be placed
between the two actual differential factors
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_localizedImageCommutatorTailKernel
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) :
    ContDiff ℝ ∞ (localizedImageCommutatorTailKernel χ β) :=
  (contDiff_imageCommutatorTailKernel χ β hχ hχc hβ hβc hδ hplateau).mul
    (hβ.comp contDiff_snd)

/-- Joint compact support comes only from the two outer cutoffs; the
intermediate factor remains noncompact
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasCompactSupport_localizedImageCommutatorTailKernel
    (χ β : E → ℝ) (hχc : HasCompactSupport χ) (hβc : HasCompactSupport β) :
    HasCompactSupport (localizedImageCommutatorTailKernel χ β) := by
  apply HasCompactSupport.intro (hχc.prod hβc)
  intro p hp
  by_cases hx : p.1 ∈ tsupport χ
  · have hy : p.2 ∉ tsupport β := fun hy ↦ hp ⟨hx, hy⟩
    simp [localizedImageCommutatorTailKernel, image_eq_zero_of_notMem_tsupport hy]
  · have hx0 := image_eq_zero_of_notMem_tsupport hx
    simp [localizedImageCommutatorTailKernel, imageCommutatorTailKernel,
      imageCommutatorTailSection, hx0]

end JanetCartan.ContinuumNormalReduction.ImageNormal
