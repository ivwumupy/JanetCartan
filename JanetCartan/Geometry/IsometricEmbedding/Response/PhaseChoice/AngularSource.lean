module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.EuclideanPhase
public import Mathlib.Analysis.Normed.Module.Normalize
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.ForwardGap

/-!
# Full angular source gaps, including the closed shoulders

The source partition in `app:ch_response:eq:response-whole-source-partition`
is lifted to all positive radii. Compact separation then gives the full
`ρ + ‖η‖` gap used by the inactive Fourier source factors in
`app:ch_response:thm:response-literal-transfer`. Zero and bounded covectors
are included. This is canonical source geometry, not an operator estimate.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.CompatibleResponse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closed source supports of degree-zero cutoffs retain positive scaling,
including their boundary (`app:ch_response:eq:response-whole-source-partition`). -/
theorem tsupport_smul_of_degree_zero {b : E → ℝ}
    (hb : ∀ x, ∀ ρ : ℝ, 0 < ρ → b (ρ • x) = b x)
    {x : E} (hx : x ∈ tsupport b) {ρ : ℝ} (hρ : 0 < ρ) :
    ρ • x ∈ tsupport b := by
  have hm : MapsTo (fun y : E ↦ ρ • y) (Function.support b) (Function.support b) := by
    intro y hy
    simpa only [Function.mem_support, hb y ρ hρ] using hy
  exact hm.closure (continuous_const.smul continuous_id) hx

/-- Compact protected covectors and a closed conic inactive source give the
complete radial gap, with a small additive source-frequency perturbation.
The geometric inputs are instantiated below for the actual angular partition
(`app:ch_response:thm:response-literal-transfer`, complete complement). -/
theorem exists_full_conic_source_gap {n : ℕ} {K S : Set (Euclidean n)}
    (hK : IsCompact K) (hS : IsClosed S) (hdis : Disjoint K S)
    (hcone : ∀ η ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ • η ∈ S) :
    ∃ d > 0, ∃ ε > 0, ∀ ζ ∈ K, ∀ η ∈ S, ∀ ρ : ℝ, 0 < ρ →
      ∀ θ : Euclidean n, ‖θ‖ ≤ ε * ρ → d * (ρ + ‖η‖) ≤ ‖η - ρ • ζ + θ‖ := by
  obtain ⟨a, ha, hgap⟩ := exists_uniform_source_gap hK hS hdis
  obtain ⟨B, hB, hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨ResponseTransfer.LowEnvelope.forwardGapConstant a B,
    ResponseTransfer.LowEnvelope.forwardGapConstant_pos ha hB.le, a / 2, half_pos ha, ?_⟩
  intro ζ hζ η hη ρ hρ θ hθ
  have hd := (hgap ζ hζ (ρ⁻¹ • η) (hcone η hη ρ⁻¹ (inv_pos.mpr hρ))).le
  have hscale : a * ρ ≤ ‖η - ρ • ζ‖ := by
    have hh := mul_le_mul_of_nonneg_left hd hρ.le
    rw [dist_eq_norm, ← norm_smul_of_nonneg hρ.le, smul_sub,
      smul_inv_smul₀ hρ.ne', norm_sub_rev] at hh
    simpa only [mul_comm] using hh
  simpa only [sub_neg_eq_add] using ResponseTransfer.LowEnvelope.forward_frequency_gap
    ha hρ.le (hbound ζ hζ) hscale
    (θ := -θ) (by simpa only [norm_neg, div_mul_eq_mul_div] using hθ)

/-- The degree-zero lift of a cutoff on unit directions, used for the actual
two-sector source partition (`app:ch_response:eq:response-whole-source-partition`). -/
def radialSourceCutoff (a : E → ℝ) (η : E) : ℝ := a (NormedSpace.normalize η)

/-- Every radial shoulder is retained by the degree-zero lift
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem radialSourceCutoff_smul (a : E → ℝ) (η : E) {ρ : ℝ} (hρ : 0 < ρ) :
    radialSourceCutoff a (ρ • η) = radialSourceCutoff a η := by
  simp only [radialSourceCutoff, NormedSpace.normalize_smul_of_pos hρ]

/-- The actual radial angular factor is smooth away from zero. The bounded
frequency piece is retained separately by the response consumer
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem radialSourceCutoff_contDiffOn {n : ℕ} {a : Euclidean n → ℝ}
    (ha : ContDiff ℝ ∞ a) :
    ContDiffOn ℝ ∞ (radialSourceCutoff a) {η | η ≠ 0} := by
  intro η hη
  exact (ha.contDiffAt.comp η
    (((contDiffAt_id.norm ℝ hη).inv (norm_ne_zero_iff.mpr hη)).smul
      contDiffAt_id)).contDiffWithinAt

/-- At nonzero covectors the entire closed support of the lifted cutoff
comes from the original closed angular support, including its shoulders
(`app:ch_response:thm:response-compatible-choice`). -/
theorem normalize_mem_tsupport_of_radialSourceCutoff {a : E → ℝ} {η : E}
    (hη : η ≠ 0) (hs : η ∈ tsupport (radialSourceCutoff a)) :
    NormedSpace.normalize η ∈ tsupport a := by
  by_contra hn
  have hc : ContinuousAt (NormedSpace.normalize : E → E) η :=
    (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hη)).smul continuousAt_id
  have he := hc.eventually (notMem_tsupport_iff_eventuallyEq.mp hn)
  exact (notMem_tsupport_iff_eventuallyEq.mpr he) hs

end JanetCartan.CompatibleResponse

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

set_option maxHeartbeats 1000000 in
/-- Construct both angular source factors from the actual whole primary
compact. The inactive difference and opposite factor have a full source gap
at every radius, including zero, bounded frequencies, and closed shoulders.
The supplied cone containment is the proved output of
`exists_selected_primary_source_gaps`, not a source-gap hypothesis
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_euclidean_primary_angular_gaps {c C : ℝ} (hP : P.IsValid c C)
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hKD : T.primaryCanonicalCompact ⊆ T.sectionEnergyCone ℓ r) :
    ∃ (a : Euclidean n → ℝ) (d ε : ℝ),
      0 < d ∧ 0 < ε ∧ ContDiff ℝ ∞ a ∧ HasCompactSupport a ∧
      (∀ η, a η ∈ Icc (0 : ℝ) 1) ∧ tsupport a ⊆ T.euclideanSectionEnergyCone ℓ r ∧
      T.euclideanPrimaryCompact ⊆ interior {η | radialSourceCutoff a η = 1} ∧
      (∀ η, η ≠ 0 → η ∈ tsupport (radialSourceCutoff a) →
        η ∈ T.euclideanSectionEnergyCone ℓ r) ∧
      (∀ ζ ∈ T.euclideanPrimaryCompact,
        ∀ η ∈ tsupport (antipodalCutoff (radialSourceCutoff a)) ∪
          tsupport (fun η ↦ radialSourceCutoff a η - 1),
        ∀ ρ : ℝ, 0 < ρ → ∀ θ : Euclidean n, ‖θ‖ ≤ ε * ρ →
          d * (ρ + ‖η‖) ≤ ‖η - ρ • ζ + θ‖) ∧
      (∀ ζ ∈ Neg.neg ⁻¹' T.euclideanPrimaryCompact,
        ∀ η ∈ tsupport (radialSourceCutoff a) ∪
          tsupport (fun η ↦ antipodalCutoff (radialSourceCutoff a) η - 1),
        ∀ ρ : ℝ, 0 < ρ → ∀ θ : Euclidean n, ‖θ‖ ≤ ε * ρ →
          d * (ρ + ‖η‖) ≤ ‖η - ρ • ζ + θ‖) := by
  have hK := T.euclideanPrimaryCompact_compact_nonzero hP
  have hKD' : T.euclideanPrimaryCompact ⊆ T.euclideanSectionEnergyCone ℓ r :=
    image_mono hKD
  let N := NormedSpace.normalize '' T.euclideanPrimaryCompact
  have hN : IsCompact N := hK.1.image_of_continuousOn (fun η hη ↦
    ((continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr (hK.2 η hη))).smul
      continuousAt_id).continuousWithinAt)
  have hND : N ⊆ T.euclideanSectionEnergyCone ℓ r := by
    rintro _ ⟨η, hη, rfl⟩
    exact T.euclideanSectionEnergyCone_smul ℓ r (hKD' hη)
      (inv_pos.mpr (norm_pos_iff.mpr (hK.2 η hη)))
  have hdis : Disjoint (T.euclideanSectionEnergyCone ℓ r)
      (Neg.neg ⁻¹' T.euclideanSectionEnergyCone ℓ r) := by
    apply disjoint_left.mpr
    intro η hη hnη
    have h₁ := (T.mem_euclideanSectionEnergyCone ℓ r η).mp hη
    have h₂ := (T.mem_euclideanSectionEnergyCone ℓ r (-η)).mp hnη
    exact disjoint_left.mp (T.sectionEnergyCone_disjoint_antipode ℓ r) h₁
      (by simpa only [mem_preimage, map_neg] using h₂)
  obtain ⟨a, _d, _hd, ha, harange, hac, has, hap, _hpair, _hgap⟩ :=
    exists_conjugate_cutoff_source_gap hN (T.euclideanSectionEnergyCone_open_convex ℓ r).1 hND hdis
  let b := radialSourceCutoff a
  have hb : ∀ η, ∀ ρ : ℝ, 0 < ρ → b (ρ • η) = b η :=
    fun η _ hρ ↦ radialSourceCutoff_smul a η hρ
  have hbD (η : Euclidean n) (hη : η ≠ 0) (hs : η ∈ tsupport b) :
      η ∈ T.euclideanSectionEnergyCone ℓ r := by
    have hn := has (normalize_mem_tsupport_of_radialSourceCutoff hη hs)
    simpa only [NormedSpace.norm_smul_normalize] using
      T.euclideanSectionEnergyCone_smul ℓ r hn (norm_pos_iff.mpr hη)
  have hplateau : T.euclideanPrimaryCompact ⊆ interior {η | b η = 1} := by
    intro η hη
    have hc : ContinuousAt (NormedSpace.normalize : Euclidean n → Euclidean n) η :=
      (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr (hK.2 η hη))).smul continuousAt_id
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hc.eventually (isOpen_interior.mem_nhds (hap ⟨η, hη, rfl⟩))] with v hv
    exact (interior_subset (s := {ξ | a ξ = 1})) hv
  have hopposite : Disjoint T.euclideanPrimaryCompact (tsupport (antipodalCutoff b)) := by
    apply disjoint_left.mpr
    intro η hη hs
    rw [tsupport_antipodalCutoff] at hs
    have hn := hbD (-η) (neg_ne_zero.mpr (hK.2 η hη)) hs
    exact disjoint_left.mp hdis (hKD' hη) hn
  let S := tsupport (antipodalCutoff b) ∪ tsupport (fun η ↦ b η - 1)
  have hcone : ∀ η ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ • η ∈ S := by
    intro η hη ρ hρ
    rcases hη with hη | hη
    · exact Or.inl (tsupport_smul_of_degree_zero (fun x t ht ↦ by
        simp only [antipodalCutoff, ← smul_neg, hb (-x) t ht]) hη hρ)
    · exact Or.inr (tsupport_smul_of_degree_zero (fun x t ht ↦ by rw [hb x t ht]) hη hρ)
  obtain ⟨d, hd, ε, hε, hfull⟩ := exists_full_conic_source_gap hK.1
    ((isClosed_tsupport _).union (isClosed_tsupport _))
    (disjoint_union_right.mpr ⟨hopposite, disjoint_inactive_tsupport hplateau⟩) hcone
  refine ⟨a, d, ε, hd, hε, ha, hac, harange, has, hplateau, hbD, hfull, ?_⟩
  intro ζ hζ η hη ρ hρ θ hθ
  have hnη : -η ∈ S := by
    rcases hη with hη | hη
    · exact Or.inl (by simpa only [tsupport_antipodalCutoff, mem_preimage, neg_neg] using hη)
    · exact Or.inr (tsupport_comp_subset_preimage (fun η ↦ b η - 1) continuous_neg hη)
  have hh := hfull (-ζ) hζ (-η) hnη ρ hρ (-θ) (by simpa only [norm_neg] using hθ)
  have he : -η - ρ • (-ζ) + -θ = -(η - ρ • ζ + θ) := by
    simp only [smul_neg]
    abel
  simpa only [norm_neg, he] using hh

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
