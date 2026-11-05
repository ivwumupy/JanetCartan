module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.Reflection

/-!
# Uniform even physical cutoffs

Apply covector symmetry at the compact cutoff construction, before the
current coefficient or finite history is chosen. The common finite cutoff
menu from `ProtectedMasks.Uniformity.Cutoffs` supplies all derivative orders.
Consumer: the symmetric buffered reachable sets used for the masks in
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks FiniteChain.Graph

variable {d : ℕ}
local notation "P" => Euclidean (d + 1) × Euclidean (d + 1)

/-- A fixed compact envelope and shoulder width determine all derivative
bounds before the symmetric compact varies. The cutoff is even in its
physical covector, with the SAME plateau/support shoulders and derivative
sequence as the unsymmetrized cutoff menu. No symmetry of the selected chart
relation is assumed (`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_even_physicalLocalizer_cutoffs
    {B : Set P} (hB : IsCompact B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ H : ℕ → ℝ, (∀ k, 0 ≤ H k) ∧
      ∀ K : Set P, IsCompact K → K ⊆ B →
        (∀ p ∈ K, physicalCovectorReflection p ∈ K) →
        ∃ m : LocalizerSymbol (d + 1),
          ContDiff ℝ ∞ m ∧ (∀ p, m p ∈ Icc (0 : ℝ) 1) ∧
          HasCompactSupport m ∧ (∀ y ξ, m (y, -ξ) = m (y, ξ)) ∧
          cthickening (δ / 4) K ⊆ interior {p | m p = 1} ∧
          tsupport m ⊆ cthickening δ K ∧
          ∀ k p, ‖iteratedFDeriv ℝ k m p‖ ≤ H k := by
  obtain ⟨H, hH, hcut⟩ := exists_uniform_physicalLocalizer_cutoffs hB hδ
  refine ⟨H, hH, ?_⟩
  intro K hK hKB hKsym
  obtain ⟨b, hb, hrange, hcompact, hplateau, hsupp, hjet⟩ := hcut K hK hKB
  let br : LocalizerSymbol (d + 1) := b ∘ physicalCovectorReflection
  let m : LocalizerSymbol (d + 1) := (1 / 2 : ℝ) • (b + br)
  have hbr : ContDiff ℝ ∞ br := hb.comp physicalCovectorReflection.contDiff
  have hsuppR : tsupport br ⊆ cthickening δ K := by
    rw [show tsupport br = physicalCovectorReflection ⁻¹' tsupport b from
      tsupport_comp_eq_preimage b physicalCovectorReflection.toHomeomorph]
    intro p hp
    simpa only [physicalCovectorReflection_involutive] using
      physicalCovectorReflection_mem_cthickening hK hKsym hδ.le (hsupp hp)
  refine ⟨m, (hb.add hbr).const_smul (1 / 2 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    obtain ⟨hl, hu⟩ := hrange p
    obtain ⟨hrl, hru⟩ := hrange (physicalCovectorReflection p)
    change 0 ≤ (1 / 2 : ℝ) * (b p + b (physicalCovectorReflection p)) ∧
      (1 / 2 : ℝ) * (b p + b (physicalCovectorReflection p)) ≤ 1
    constructor <;> linarith
  · exact (hcompact.add (hcompact.comp_homeomorph
      physicalCovectorReflection.toHomeomorph)).smul_left
  · intro y ξ
    change (1 / 2 : ℝ) * (b (y, -ξ) + b (y, - -ξ)) =
      (1 / 2 : ℝ) * (b (y, ξ) + b (y, -ξ))
    rw [neg_neg, add_comm]
  · intro p hp
    have hrp := physicalCovectorReflection_mem_cthickening hK hKsym
      (by positivity : 0 ≤ δ / 4) hp
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [isOpen_interior.mem_nhds (hplateau hp),
      physicalCovectorReflection.continuous.continuousAt.eventually
        (isOpen_interior.mem_nhds (hplateau hrp))] with q hq hrq
    have hq' : b q = 1 := interior_subset (s := {p | b p = 1}) hq
    have hrq' : b (physicalCovectorReflection q) = 1 :=
      interior_subset (s := {p | b p = 1}) hrq
    change (1 / 2 : ℝ) * (b q + b (physicalCovectorReflection q)) = 1
    rw [hq', hrq']
    norm_num
  · exact (tsupport_smul_subset_right (fun _ : P ↦ (1 / 2 : ℝ)) (b + br)).trans
      ((tsupport_add b br).trans (union_subset hsupp hsuppR))
  · intro k p
    have hb' : ContDiff ℝ k b := hb.of_le (by exact_mod_cast le_top)
    have hbr' : ContDiff ℝ k br := hbr.of_le (by exact_mod_cast le_top)
    have hreflection : ‖iteratedFDeriv ℝ k br p‖ =
        ‖iteratedFDeriv ℝ k b (physicalCovectorReflection p)‖ :=
      physicalCovectorReflection.norm_iteratedFDeriv_comp_right b p k
    change ‖iteratedFDeriv ℝ k ((1 / 2 : ℝ) • (b + br)) p‖ ≤ H k
    rw [iteratedFDeriv_const_smul_apply (a := (1 / 2 : ℝ))
      (f := b + br) (hb'.add hbr').contDiffAt,
      iteratedFDeriv_add_apply hb'.contDiffAt hbr'.contDiffAt, norm_smul]
    have ht := norm_add_le (iteratedFDeriv ℝ k b p) (iteratedFDeriv ℝ k br p)
    rw [hreflection] at ht
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [hjet k p, hjet k (physicalCovectorReflection p)]

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
