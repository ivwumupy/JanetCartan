module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.Cutoffs

/-!
# Even nested masks on the explicitly reflected proof relation

Use compactness and symmetry of the actual buffered images at each cutoff
selection. The complete relation is enlarged only for choosing proof masks.
The remaining physical propagation construction must supply the common
protected carrier for this enlarged relation; this lemma does not assert that
angular protection follows from protection of the original relation alone.
Consumer: `SelectedSectorProtection` and the real residual factor estimate in
`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks ProtectedFlow FiniteChain.Graph

variable {d : ℕ}
local notation "P" => Euclidean (d + 1) × Euclidean (d + 1)

/-- All-order grades precede the actual relation and source. At every depth
the even mask protects the closed buffered image of the original relation
AND its reflected relation. The original width is retained on both sides of
each step, including every diagonal branch (`app:ch_regular:lem:finite-chain`).

The compact carrier input is the explicit remaining obligation of physical
propagation for `reflectedProofRelation R`; it is not inferred from a carrier
bound for `R`. This is the cutoff deduction, not the actual selected-family
existence theorem. -/
theorem exists_uniform_even_bufferedReachableAt_localizers
    {B : Set P} (hB : IsCompact B) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∃ H : ℕ → ℝ, (∀ k, 0 ≤ H k) ∧
      ∀ (R : P → P → Prop) (S : Set P),
        IsCompact {pq : P × P | R pq.1 pq.2} → IsCompact S →
        (∀ p ∈ S, physicalCovectorReflection p ∈ S) →
        (∀ n ≤ N, bufferedReachableAt (reflectedProofRelation R) S δ n ⊆ B) →
        ∃ m : Fin (N + 1) → LocalizerSymbol (d + 1),
          (∀ j, ContDiff ℝ ∞ (m j)) ∧
          (∀ j p, m j p ∈ Icc (0 : ℝ) 1) ∧
          (∀ j, HasCompactSupport (m j)) ∧
          (∀ j y ξ, m j (y, -ξ) = m j (y, ξ)) ∧
          (∀ j, cthickening (δ / 8)
            (bufferedReachableAt (reflectedProofRelation R) S δ j.val) ⊆
              interior {p | m j p = 1}) ∧
          (∀ j, tsupport (m j) ⊆ cthickening (δ / 2)
            (bufferedReachableAt (reflectedProofRelation R) S δ j.val)) ∧
          (∀ j, cthickening (δ / 8) (tsupport (m j)) ⊆ cthickening δ
            (bufferedReachableAt (reflectedProofRelation R) S δ j.val)) ∧
          (∀ j k p, ‖iteratedFDeriv ℝ k (m j) p‖ ≤ H k) ∧
          (∀ j : Fin N, ∀ p ∈ cthickening (δ / 8) (tsupport (m j.castSucc)),
            ∀ q, p = q ∨ reflectedProofRelation R p q →
              closedBall q (δ / 8) ⊆ interior {p | m j.succ p = 1}) := by
  obtain ⟨H, hH, hcut⟩ := exists_uniform_even_physicalLocalizer_cutoffs hB
    (show 0 < δ / 2 by positivity)
  refine ⟨H, hH, ?_⟩
  intro R S hR hS hSsym hcarrier
  have hchoose (j : Fin (N + 1)) :=
    hcut (bufferedReachableAt (reflectedProofRelation R) S δ j.val)
      (isCompact_bufferedReachableAt (isCompact_reflectedProofRelation hR) hS δ j.val)
      (hcarrier j.val (by omega))
      (bufferedReachableAt_reflectedProofRelation_symmetric hR hS hSsym hδ.le j.val)
  choose m hsmooth hrange hcompact heven hplateau hsupp hjet using hchoose
  have hplateau' j : cthickening (δ / 8)
      (bufferedReachableAt (reflectedProofRelation R) S δ j.val) ⊆
        interior {p | m j p = 1} := by
    simpa only [div_div, show (2 : ℝ) * 4 = 8 from by norm_num] using hplateau j
  have hshoulder j : cthickening (δ / 8) (tsupport (m j)) ⊆
      cthickening δ (bufferedReachableAt (reflectedProofRelation R) S δ j.val) :=
    (cthickening_subset_of_subset _ (hsupp j)).trans
      ((cthickening_cthickening_subset (by positivity) (by positivity) _).trans
        (cthickening_mono (by linarith) _))
  refine ⟨m, hsmooth, hrange, hcompact, heven, hplateau', hsupp, hshoulder, hjet, ?_⟩
  intro j p hp q hpq v hv
  exact hplateau' j.succ (closedBall_subset_cthickening
    (mem_bufferedReachableAt_succ_of_step (hshoulder j.castSucc hp) hpq) _ hv)

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
