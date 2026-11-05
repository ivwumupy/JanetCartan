module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.TestOperator
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.EuclideanKernel
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.HeatJets

/-!
# The literal intermediate-localization kernel

For `app:ch_background:prop:bg-frame`, Step 1, the scalar part of the tail is
`χ² J (1-β) J`. The section below keeps the noncompact multiplier `1-β`.
Its positive separation from the source-square cutoff removes the singularity
of the first Bessel kernel. The second Bessel kernel is integrated against it,
using its proved Lebesgue integrability and unit mass.

The consumer is the differentiated matrix kernel for
`coefficientSourceCommutatorTailSchwartz`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ContDiff Topology SchwartzMap
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The separated first Bessel factor, including the entire exterior
multiplier (`app:ch_background:prop:bg-frame`, Step 1). -/
def imageCommutatorTailSection (χ β : E → ℝ) (p : E × E) : ℝ :=
  χ p.1 ^ 2 * (1 - β p.2) * imageBesselKernel (p.1 - p.2)

/-- The actual scalar kernel of `χ² J (1-β) J`, before the two differential
factors (`app:ch_background:prop:bg-frame`, Step 1). -/
def imageCommutatorTailKernel (χ β : E → ℝ) (p : E × E) : ℝ :=
  ∫ z, imageCommutatorTailSection χ β (p.1, z) * imageBesselKernel (z - p.2)

/-- A compact source localization of the literal scalar kernel. The source
factor `P* μ` is unchanged by this localization when `β=1` near `tsupport μ`
(`app:ch_background:prop:bg-frame`, Step 1). -/
def localizedImageCommutatorTailKernel (χ β : E → ℝ) (p : E × E) : ℝ :=
  imageCommutatorTailKernel χ β p * β p.2

/-- Inside the positive separation gap the whole section vanishes on a
neighborhood, so every derivative vanishes there as well
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageCommutatorTailSection_eventuallyEq_zero
    (χ β : E → ℝ) {δ : ℝ}
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)
    (p : E × E) (hp : dist p.1 p.2 < δ) :
    imageCommutatorTailSection χ β =ᶠ[𝓝 p] 0 := by
  by_cases hx : p.1 ∈ tsupport χ
  · have hn : ∀ᶠ q : E × E in 𝓝 p, dist p.1 q.2 < δ :=
      (isOpen_lt (continuous_const.dist continuous_snd) continuous_const).mem_nhds hp
    filter_upwards [hn] with q hq
    simp [imageCommutatorTailSection, hplateau p.1 hx q.2 hq]
  · have hn := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
      (continuous_fst.tendsto p)
    filter_upwards [hn] with q hq
    simp only [Function.comp_apply, Pi.zero_apply] at hq
    simp [imageCommutatorTailSection, hq]

/-- The singularity of the first Bessel kernel is removed by the actual
plateau, without truncating the exterior multiplier
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_imageCommutatorTailSection
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) :
    ContDiff ℝ ∞ (imageCommutatorTailSection χ β) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 - p.2 = 0
  · apply contDiffAt_const.congr_of_eventuallyEq
    exact imageCommutatorTailSection_eventuallyEq_zero χ β hplateau p
      (by simpa [dist_eq_norm, hp] using hδ)
  · have hK : ContDiffAt ℝ ∞ (imageBesselKernel (d := d)) (p.1 - p.2) :=
      contDiffOn_imageBesselKernel_offDiagonal.contDiffAt (isOpen_ne.mem_nhds hp)
    have hdK : ContDiffAt ℝ ∞
        (fun q : E × E ↦ imageBesselKernel (q.1 - q.2)) p :=
      hK.comp (f := fun q : E × E ↦ q.1 - q.2) p (contDiffAt_fst.sub contDiffAt_snd)
    exact (((hχ.comp contDiff_fst).pow 2).contDiffAt.mul
      (contDiffAt_const.sub (hβ.comp contDiff_snd).contDiffAt)).mul hdK

/-- A finite bound for the separated section follows from the primitive
cutoff bounds and the actual Bessel gap estimate
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem exists_bound_imageCommutatorTailSection
    (χ β : E → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hβ : Continuous β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, ‖imageCommutatorTailSection χ β p‖ ≤ C := by
  obtain ⟨Bχ, hbχ⟩ := hχc.exists_bound_of_continuous hχ
  obtain ⟨Bβ, hbβ⟩ := hβc.exists_bound_of_continuous hβ
  have hBχ : 0 ≤ Bχ := (norm_nonneg (χ 0)).trans (hbχ 0)
  have hBβ : 0 ≤ Bβ := (norm_nonneg (β 0)).trans (hbβ 0)
  obtain ⟨C, hC, hb⟩ := exists_imageBesselKernel_offDiagonal_jet_decay (d := d) δ hδ 0 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hb
  refine ⟨Bχ ^ 2 * (1 + Bβ) * C, by positivity, fun p ↦ ?_⟩
  by_cases hp : dist p.1 p.2 < δ
  · have hz := (imageCommutatorTailSection_eventuallyEq_zero χ β hplateau p hp).eq_of_nhds
    simpa only [hz, Pi.zero_apply, norm_zero] using
      (show 0 ≤ Bχ ^ 2 * (1 + Bβ) * C by positivity)
  · have hg : δ ≤ ‖p.1 - p.2‖ := by simpa only [dist_eq_norm] using le_of_not_gt hp
    have hm : ‖1 - β p.2‖ ≤ 1 + Bβ :=
      (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add_right (hbβ p.2) 1)
    simp only [imageCommutatorTailSection, norm_mul, norm_pow]
    exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hbχ p.1) 2)
      hm (norm_nonneg _) (by positivity)) (hb _ hg) (norm_nonneg _) (by positivity)

/-- Every intermediate integral defining the scalar tail converges
absolutely. No compactness of `1-β` is used
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrable_imageCommutatorTailSection_mul_bessel
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)
    (x y : E) : Integrable (fun z ↦
      imageCommutatorTailSection χ β (x, z) * imageBesselKernel (z - y)) := by
  obtain ⟨C, _, hC⟩ := exists_bound_imageCommutatorTailSection χ β hχ.continuous hχc
    hβ.continuous hβc hδ hplateau
  exact (integrable_imageBesselKernel.comp_sub_right y).bdd_mul
    (((contDiff_imageCommutatorTailSection χ β hχ hβ hδ hplateau).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z ↦ hC (x, z)))

end JanetCartan.ContinuumNormalReduction.ImageNormal
