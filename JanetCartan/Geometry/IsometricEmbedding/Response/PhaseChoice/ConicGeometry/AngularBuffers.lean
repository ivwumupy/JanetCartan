module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.Phase

/-!
# Normalized angular support buffers for the selected cone

The protected compact in `app:ch_response:thm:response-compatible-choice` is
normalized using the very slice that retains every primary ray. The cutoff
gaps below concern closed supports, and therefore include every shoulder of
the opposite piece and the inactive difference. Their conic lifts remain
inside the full cone on which the quantitative phase estimates hold.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The whole normalized primary family on the selected linear slice
(`app:ch_response:thm:response-compatible-choice`). -/
def normalizedPrimaryCanonicalCompact (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) :
    Set (ℝ × Euclidean (n - 1)) :=
  (fun η ↦ (ℓ η)⁻¹ • η) '' T.primaryCanonicalCompact

/-- Compactness survives normalization of the entire protected family
(`app:ch_response:thm:response-compatible-choice`). -/
theorem normalizedPrimaryCanonicalCompact_isCompact {c C : ℝ} (hP : P.IsValid c C)
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hK : T.primaryCanonicalCompact ⊆ T.sectionEnergyCone ℓ r) :
    IsCompact (T.normalizedPrimaryCanonicalCompact ℓ) := by
  apply (T.primaryCanonicalCompact_isCompact hP).image_of_continuousOn
  intro η hη
  exact ((ℓ.continuous.continuousAt.inv₀ (hK hη).1.ne').smul
    continuousAt_id).continuousWithinAt

/-- Normalized primary covectors lie in the same active cone and on the
normalization slice (`app:ch_response:thm:response-compatible-choice`). -/
theorem normalizedPrimaryCanonicalCompact_subset
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hK : T.primaryCanonicalCompact ⊆ T.sectionEnergyCone ℓ r) :
    T.normalizedPrimaryCanonicalCompact ℓ ⊆
      T.sectionEnergyCone ℓ r ∩ {η | ℓ η = 1} := by
  rintro _ ⟨η, hη, rfl⟩
  exact ⟨T.sectionEnergyCone_smul ℓ r (hK hη) (inv_pos.mpr (hK hη).1),
    by simp [(hK hη).1.ne']⟩

/-- Nested normalized buffers and a conjugate cutoff pair with both complete
source gaps. Conic lifts of their full closed supports stay in the active
cones, including all shoulders. `hK` is produced by
`exists_primary_conic_normalization`
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem exists_normalized_primary_cutoffs {c C : ℝ} (hP : P.IsValid c C)
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hK : T.primaryCanonicalCompact ⊆ T.sectionEnergyCone ℓ r) :
    ∃ (Vin Vout : Set (ℝ × Euclidean (n - 1)))
      (a : (ℝ × Euclidean (n - 1)) → ℝ) (d : ℝ),
      IsOpen Vin ∧ IsOpen Vout ∧ T.normalizedPrimaryCanonicalCompact ℓ ⊆ Vin ∧
      closure Vin ⊆ Vout ∧ closure Vout ⊆ T.sectionEnergyCone ℓ r ∧
      IsCompact (closure Vin) ∧ IsCompact (closure Vout) ∧
      0 < d ∧ ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ (antipodalCutoff a) ∧
      (∀ η, a η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport a ∧ tsupport a ⊆ Vout ∧
      T.normalizedPrimaryCanonicalCompact ℓ ⊆ interior {η | a η = 1} ∧
      Disjoint (tsupport a) (tsupport (antipodalCutoff a)) ∧
      (∀ ζ ∈ T.normalizedPrimaryCanonicalCompact ℓ,
        ∀ η ∈ tsupport (antipodalCutoff a) ∪ tsupport (fun η ↦ a η - 1),
          d < dist ζ η) ∧
      (∀ ζ ∈ Neg.neg ⁻¹' T.normalizedPrimaryCanonicalCompact ℓ,
        ∀ η ∈ tsupport a ∪ tsupport (fun η ↦ antipodalCutoff a η - 1),
          d < dist ζ η) ∧
      (∀ η, 0 < ℓ η → (ℓ η)⁻¹ • η ∈ tsupport a → η ∈ T.sectionEnergyCone ℓ r) ∧
      (∀ η, 0 < -ℓ η → (-ℓ η)⁻¹ • η ∈ tsupport (antipodalCutoff a) →
        -η ∈ T.sectionEnergyCone ℓ r) := by
  have hcomp := T.normalizedPrimaryCanonicalCompact_isCompact hP ℓ hK
  have hsub := (T.normalizedPrimaryCanonicalCompact_subset ℓ hK).trans inter_subset_left
  obtain ⟨Vout, ho, hKo, hoD, hco⟩ := exists_open_between_and_isCompact_closure
    hcomp (T.sectionEnergyCone_isOpen ℓ r) hsub
  obtain ⟨Vin, hi, hKi, hio, hci⟩ := exists_open_between_and_isCompact_closure hcomp ho hKo
  have hdis := (T.sectionEnergyCone_disjoint_antipode ℓ r).mono hsub (preimage_mono hsub)
  obtain ⟨a, d, hd, ha, han, harange, hac, has, hap, had, hgap, hgapn⟩ :=
    exists_two_sign_cutoff_gaps hcomp ho hKo hdis
  have hsupport : tsupport a ⊆ T.sectionEnergyCone ℓ r := has.trans (subset_closure.trans hoD)
  have hlift (η : ℝ × Euclidean (n - 1)) (hη : 0 < ℓ η)
      (hs : (ℓ η)⁻¹ • η ∈ tsupport a) : η ∈ T.sectionEnergyCone ℓ r := by
    simpa only [smul_inv_smul₀ hη.ne'] using
      T.sectionEnergyCone_smul ℓ r (hsupport hs) hη
  refine ⟨Vin, Vout, a, d, hi, ho, hKi, hio, hoD, hci, hco,
    hd, ha, han, harange, hac, has, hap, had, hgap, hgapn, hlift, ?_⟩
  intro η hη hs
  rw [tsupport_antipodalCutoff] at hs
  apply hlift (-η) (by simpa using hη)
  simpa only [map_neg, smul_neg, mem_preimage] using hs

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
