module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.SectionEnergy
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Buffered sectors of the actual section-energy chart

The canonical support construction in
`app:ch_response:thm:response-compatible-choice`. All sets below use the same
primary chart as the constructed carriers. The support gaps include the closed
shoulders of the opposite piece and the inactive difference. These are canonical
covector distances; the reverse graph's physical source-gradient estimate is a
separate obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The entire compact canonical primary family, before shifted carriers are
sampled (`app:ch_response:thm:response-compatible-choice`). -/
def primaryCanonicalCompact : Set (ℝ × Euclidean (n - 1)) :=
  T.primaryCanonical '' parameterCube P.radius

/-- Compactness of the actual canonical primary family
(`app:ch_response:thm:response-compatible-choice`). -/
theorem primaryCanonicalCompact_isCompact {c C : ℝ} (hP : P.IsValid c C) :
    IsCompact T.primaryCanonicalCompact := by
  apply (isCompact_parameterCube P.radius).image_of_continuousOn
  exact continuousOn_const.prodMk
    ((T.reference.spatialPatch_smooth hP).continuousOn.mono
      (parameterCube_subset_doubledInterior hP.1))

/-- The whole compact family lies in the one energy buffer
(`app:ch_response:thm:response-compatible-choice`). -/
theorem primaryCanonicalCompact_subset {c C : ℝ} (hP : P.IsValid c C) :
    T.primaryCanonicalCompact ⊆ T.sectionEnergyDomain := by
  rintro _ ⟨z, hz, rfl⟩
  exact T.primaryCanonical_mem (fun i ↦ (hz i).trans (by linarith [hP.1]))

/-- The actual energy buffer is disjoint from its antipode. Convexity and the
proved exclusion of zero discharge the pointedness premise of the cutoff
construction (`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergyDomain_disjoint_antipode :
    Disjoint T.sectionEnergyDomain (Neg.neg ⁻¹' T.sectionEnergyDomain) := by
  apply disjoint_left.mpr
  intro η hη hnη
  have hc : Convex ℝ T.sectionEnergyDomain := convex_ball _ _
  have hm := hc hη hnη (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_neg, add_neg_cancel] at hm
  exact T.zero_notMem_sectionEnergyDomain hm

/-- Actual nested inner/outer buffers, with compact closures, chosen once
around every primary covector. Reflection supplies the negative buffers
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_buffered_sectionEnergy_sectors {c C : ℝ} (hP : P.IsValid c C) :
    ∃ Vin Vout : Set (ℝ × Euclidean (n - 1)),
      IsOpen Vin ∧ IsOpen Vout ∧ T.primaryCanonicalCompact ⊆ Vin ∧
      closure Vin ⊆ Vout ∧ closure Vout ⊆ T.sectionEnergyDomain ∧
      IsCompact (closure Vin) ∧ IsCompact (closure Vout) ∧
      Disjoint (closure Vout) (Neg.neg ⁻¹' closure Vout) := by
  obtain ⟨Vout, ho, hKo, hoD, hco⟩ := exists_open_between_and_isCompact_closure
    (T.primaryCanonicalCompact_isCompact hP) isOpen_ball
    (T.primaryCanonicalCompact_subset hP)
  obtain ⟨Vin, hi, hKi, hio, hci⟩ := exists_open_between_and_isCompact_closure
    (T.primaryCanonicalCompact_isCompact hP) ho hKo
  exact ⟨Vin, Vout, hi, ho, hKi, hio, hoD, hci, hco,
    T.sectionEnergyDomain_disjoint_antipode.mono hoD (preimage_mono hoD)⟩

/-- Construct the conjugate cutoffs on the actual energy buffer. Both inactive
differences and every shoulder have a uniform canonical source gap, chosen
before the current frame and frequency
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem exists_sectionEnergy_cutoffs {c C : ℝ} (hP : P.IsValid c C) :
    ∃ (a : (ℝ × Euclidean (n - 1)) → ℝ) (δ : ℝ),
      0 < δ ∧ ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ (antipodalCutoff a) ∧
      (∀ η, a η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport a ∧
      tsupport a ⊆ T.sectionEnergyDomain ∧
      T.primaryCanonicalCompact ⊆ interior {η | a η = 1} ∧
      Disjoint (tsupport a) (tsupport (antipodalCutoff a)) ∧
      (∀ ζ ∈ T.primaryCanonicalCompact,
        ∀ η ∈ tsupport (antipodalCutoff a) ∪ tsupport (fun η ↦ a η - 1),
          δ < dist ζ η) ∧
      (∀ ζ ∈ Neg.neg ⁻¹' T.primaryCanonicalCompact,
        ∀ η ∈ tsupport a ∪ tsupport (fun η ↦ antipodalCutoff a η - 1),
          δ < dist ζ η) := by
  apply exists_two_sign_cutoff_gaps (T.primaryCanonicalCompact_isCompact hP)
    isOpen_ball (T.primaryCanonicalCompact_subset hP)
  exact T.sectionEnergyDomain_disjoint_antipode.mono
    (T.primaryCanonicalCompact_subset hP) (preimage_mono (T.primaryCanonicalCompact_subset hP))

/-- The transverse covector is nonzero on the doubled closed primary patch.
The zero-energy slice of the actual energy chart cannot contain zero
(`app:ch_response:thm:response-compatible-choice`). -/
theorem primary_transverse_ne_zero {z : Euclidean 3}
    (hz : z ∈ parameterCube (2 * P.radius)) : T.reference.spatialPatch z ≠ 0 := by
  intro he
  have hm := T.primaryCanonical_mem hz
  apply T.zero_notMem_sectionEnergyDomain
  simpa only [primaryCanonical, he, ← Prod.zero_eq_mk] using hm

/-- A uniform positive transverse-covector bound on the whole compact primary
patch, derived from the selected energy chart
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_primary_transverse_gap {c C : ℝ} (hP : P.IsValid c C) :
    ∃ d > (0 : ℝ), ∀ z ∈ parameterCube P.radius,
      d ≤ ‖T.reference.spatialPatch z‖ := by
  apply exists_uniform_positive_bound (isCompact_parameterCube P.radius)
    (((T.reference.spatialPatch_smooth hP).continuousOn.mono
      (parameterCube_subset_doubledInterior hP.1)).norm)
  intro z hz
  exact norm_pos_iff.mpr (T.primary_transverse_ne_zero
    (fun i ↦ (hz i).trans (by linarith [hP.1])))

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
