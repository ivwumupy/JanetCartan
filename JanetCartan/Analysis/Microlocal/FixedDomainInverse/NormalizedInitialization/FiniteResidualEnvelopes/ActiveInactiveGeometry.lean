module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.Conic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# A fixed active parameter cutoff and the complementary angular gap

The supplied final incidence domain already captures every frozen source
meeting the actual conic mask. Its captured parameter set is compact. A smooth
cutoff inside that same domain leaves a uniformly separated inactive set.
The mask's full closed support, including every radial shoulder, is used.

Consumer: the inactive source-shell application in the finite residual-word
proof of `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes

open RegularSector.FiniteMasks CompatibleResponse NormedSpace

variable {n : ℕ}
local notation "E" => Euclidean n

private theorem conicMask_normalized_section (a : E → ℝ) {ξ : E} (hξ : ξ ≠ 0) :
    conicMask a ((3 : ℝ) • normalize ξ) = radialSourceCutoff a ξ := by
  rw [conicMask_eq_radial (by norm_num [norm_smul, norm_normalize hξ] :
    2 ≤ ‖(3 : ℝ) • normalize ξ‖)]
  simp only [radialSourceCutoff, normalize_smul_of_pos (by norm_num : (0 : ℝ) < 3),
    normalize_normalize]

/-- Every point of the actual conic support has its radius-three angular
section in that same closed support. This avoids replacing the mask by a
larger angular support, whose boundary need not be captured by the final
incidence theorem (`app:ch_response:eq:response-whole-source-partition`). -/
theorem conicMask_normalized_section_mem_tsupport
    (a : E → ℝ) {ξ : E} (hξ : ξ ∈ tsupport (conicMask a)) :
    (3 : ℝ) • normalize ξ ∈ tsupport (conicMask a) := by
  have hnonzero : ξ ≠ 0 := by
    intro hzero
    have hh := (conicMask_tsupport_subset a hξ).1
    simp only [hzero, norm_zero] at hh
    norm_num at hh
  have hnormalize : ContinuousAt (fun η : E ↦ normalize η) ξ :=
    (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hnonzero)).smul continuousAt_id
  by_contra hnot
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
    (hnormalize.const_smul (3 : ℝ)).tendsto
  have hn : ∀ᶠ η : E in 𝓝 ξ, η ≠ 0 :=
    (isOpen_ne.preimage continuous_id).mem_nhds hnonzero
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hξ
  filter_upwards [hz,hn] with η hη hηzero
  change conicMask a ((3 : ℝ) • normalize η) = 0 at hη
  rw [conicMask_normalized_section a hηzero] at hη
  simp only [conicMask,hη,mul_zero,Pi.zero_apply]

/-- A smooth cutoff is selected inside the supplied incident parameter
domain. Outside its plateau, every current normalized covector sufficiently
close to the frozen one has a uniform angular distance from the entire conic
mask. The frozen map may be either sign of the original source covector;
the appropriate actual incidence capture is the sole sign-dependent input
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_incidence_parameter_cutoff_and_gap
    {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
    [FiniteDimensional ℝ Par]
    {Csrc V : Set Par} (hCsrc : IsCompact Csrc) (hV : IsOpen V)
    (frozen : Par → E) (hfrozen : ContinuousOn frozen Csrc)
    (hne : ∀ c ∈ Csrc, frozen c ≠ 0) (mask : E → ℝ)
    (hcapture : ∀ c ∈ Csrc,
      (3 : ℝ) • normalize (frozen c) ∈ tsupport (conicMask mask) → c ∈ V) :
    ∃ χ : Par → ℝ, ContDiff ℝ ∞ χ ∧ (∀ c, χ c ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ V ∧
      (∀ c ∈ Csrc, (3 : ℝ) • normalize (frozen c) ∈ tsupport (conicMask mask) →
        c ∈ interior {c | χ c = 1}) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ c ∈ Csrc,
      c ∈ tsupport (fun c ↦ 1 - χ c) → ∀ g : E,
      dist (normalize g) (normalize (frozen c)) < δ →
      ∀ η ∈ tsupport (conicMask mask),
        δ ≤ dist (normalize g) (normalize η) := by
  let F : Par → E := fun c ↦ (3 : ℝ) • normalize (frozen c)
  have hF : ContinuousOn F Csrc := by
    intro c hc
    exact (((hfrozen.norm c hc).inv₀ (norm_ne_zero_iff.mpr (hne c hc))).smul
      (hfrozen c hc)).const_smul (3 : ℝ)
  let C : Set Par := Csrc ∩ F ⁻¹' tsupport (conicMask mask)
  have hC : IsCompact C := hCsrc.of_isClosed_subset
    (hF.preimage_isClosed_of_isClosed hCsrc.isClosed (isClosed_tsupport _)) inter_subset_left
  have hCV : C ⊆ V := fun c hc ↦ hcapture c hc.1 hc.2
  obtain ⟨χ,hχ,hrange,hcompact,hsχ,hplateau⟩ := exists_compact_family_cutoff hC hV hCV
  let N : Set Par := Csrc ∩ tsupport (fun c ↦ 1 - χ c)
  have hN : IsCompact N := hCsrc.inter_right (isClosed_tsupport _)
  have hdisjoint : Disjoint (F '' N) (tsupport (conicMask mask)) := by
    apply disjoint_left.mpr
    rintro y ⟨c,hc,rfl⟩ hy
    have hp := hplateau (show c ∈ C from ⟨hc.1,hy⟩)
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hc.2
    filter_upwards [isOpen_interior.mem_nhds hp] with b hb
    have he : b ∈ {c | χ c = 1} := interior_subset hb
    change χ b = 1 at he
    simp only [he,sub_self,Pi.zero_apply]
  obtain ⟨gap,hgap,hseparated⟩ := exists_uniform_source_gap
    (hN.image_of_continuousOn (hF.mono inter_subset_left)) (isClosed_tsupport _) hdisjoint
  let δ : ℝ := gap / 6
  have hδ : 0 < δ := div_pos hgap (by norm_num)
  refine ⟨χ,hχ,hrange,hcompact,hsχ,fun c hc hmask ↦ hplateau ⟨hc,hmask⟩,
    δ,hδ,?_⟩
  intro c hc hn g hg η hη
  have hsection := conicMask_normalized_section_mem_tsupport mask hη
  have hdist := hseparated (F c) (mem_image_of_mem F ⟨hc,hn⟩) _ hsection
  have hscale : dist (F c) ((3 : ℝ) • normalize η) =
      3 * dist (normalize (frozen c)) (normalize η) := by
    simp only [F,dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos
      (by norm_num : (0 : ℝ) < 3)]
  rw [hscale] at hdist
  have htriangle := dist_triangle (normalize (frozen c)) (normalize g) (normalize η)
  rw [dist_comm (normalize (frozen c)) (normalize g)] at htriangle
  dsimp only [δ] at hg ⊢
  linarith

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
