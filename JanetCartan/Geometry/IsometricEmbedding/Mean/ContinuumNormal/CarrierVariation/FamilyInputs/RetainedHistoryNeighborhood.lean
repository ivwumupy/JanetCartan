module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.HistoryCarrierBudget

/-!
# Actual histories enter every retained normal-comparison neighborhood

The finite immersion tolerances are those supplied by the fixed-reference
full-amplitude comparison. One initial-frequency threshold puts every
admissible history in all these neighborhoods, using the original carrier
low order and the unchanged iteration exponents.
-/

@[expose] public noncomputable section
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumRow CanonicalCarrier

/-- Discharge the finite family of immersion-smallness inputs of
`exists_retained_cell_normal_comparison` at the PDO reserve `2 * (n + 1)`.
The initial-frequency threshold precedes the varying history and all compact
domains. The positive tolerances are fixed by the retained reference before
this theorem is applied. The original `canonicalCarrierLowOrder` suffices;
no replacement of the coherent `Scales` exponents is used. Sources:
`main:eq:displacement-budget`, `app:ch_background:prop:bg-frame`,
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_initialScale_for_retained_normal_comparison_neighborhood
    {n N : ℕ} {ι : Type*} [Fintype ι]
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) {kMin : ℕ}
    (horder : displacementLoss n +
      bandExponent * ((canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (G : Euclidean n → Euclidean N) (K : ι → Set (Euclidean n)),
      (∀ i, IsCompact (K i)) →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean N) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell → ∀ i,
        cNorm (K i) (max 8 (max 1 (2 * (n + 1)) + 6))
          (finiteHistoryMap G u - G) < δ i := by
  obtain ⟨ε, hε, hεδ⟩ := Pi.exists_forall_pos_add_lt hδ
  obtain ⟨S, hS, hnear⟩ :=
    FiniteHistoryBounds.exists_initialScale_for_prefix_neighborhood
      (F := Euclidean N) (canonicalCarrierLowOrder n) horder hε
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ G K hK j u ell hu i
  have hclose := hnear R₀ hR₀ (K i) G j u (fun l ↦ (ell l : ℝ)) (hK i)
    (fun l ↦ (hu l).2.1) (fun l ↦ (hu l).2.2.1)
    (fun l ↦ (hu l).2.2.2) (fun l ↦ Nat.cast_le.mpr (hu l).1)
  change cNorm (K i) (canonicalCarrierLowOrder n) (finiteHistoryMap G u - G) < ε / 2 at hclose
  have hreserve : max 8 (max 1 (2 * (n + 1)) + 6) ≤ canonicalCarrierLowOrder n := by
    unfold canonicalCarrierLowOrder
    omega
  exact ((cNorm_mono_order hreserve).trans_lt hclose).trans
    ((half_lt_self hε).trans (by simpa only [zero_add] using hεδ i))

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
