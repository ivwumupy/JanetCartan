module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.Nested

/-!
# Even proof masks inside the same prescribed terminal plateau

The quantitative geometric producer is
`exists_uniform_reflected_prescribed_terminal_shoulders`. This leaf applies the
existing uniform even cutoff menu to its output, with the compact support of the
prescribed terminal mask as the common carrier. It does not replace that mask
by an independent existential choice, or identify quantization with a projection.
The closed support shoulder is the geometric input for the final localization
factor in `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection

open ProtectedMasks SelectedEvenProofMasks FiniteChain.Graph

variable {d : ℕ}
local notation "P" => Euclidean (d+1) × Euclidean (d+1)

/-- From the proved reflected shoulders, construct finite EVEN nested proof
masks whose entire closed support shoulders lie in the SAME prescribed final
plateau. All derivative constants precede the relation and source. The last
closed-ball inclusion is an actual geometric extension to the prescribed mask;
it asserts no idempotence or equality of independently chosen masks
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_uniform_even_masks_inside_prescribed_terminal
    (mi : LocalizerSymbol (d+1)) (hmi : HasCompactSupport mi)
    {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∃ H : ℕ → ℝ, (∀ k, 0 ≤ H k) ∧
      ∀ (R : P → P → Prop) (S : Set P),
        IsCompact {pq : P × P | R pq.1 pq.2} → IsCompact S →
        (∀ p ∈ S, physicalCovectorReflection p ∈ S) →
        (∀ n ≤ N, cthickening δ
          (bufferedReachableAt (reflectedProofRelation R) S δ n) ⊆
            interior {p | mi p = 1}) →
        ∃ m : Fin (N+1) → LocalizerSymbol (d+1),
          (∀ j, ContDiff ℝ ∞ (m j)) ∧
          (∀ j p, m j p ∈ Icc (0 : ℝ) 1) ∧
          (∀ j, HasCompactSupport (m j)) ∧
          (∀ j y ξ, m j (y, -ξ) = m j (y, ξ)) ∧
          (∀ j, cthickening (δ/8)
            (bufferedReachableAt (reflectedProofRelation R) S δ j.val) ⊆
              interior {p | m j p = 1}) ∧
          (∀ j, tsupport (m j) ⊆ cthickening (δ/2)
            (bufferedReachableAt (reflectedProofRelation R) S δ j.val)) ∧
          (∀ j, cthickening (δ/8) (tsupport (m j)) ⊆
            cthickening δ (bufferedReachableAt (reflectedProofRelation R) S δ j.val)) ∧
          (∀ j, cthickening (δ/8) (tsupport (m j)) ⊆ interior {p | mi p = 1}) ∧
          (∀ j k p, ‖iteratedFDeriv ℝ k (m j) p‖ ≤ H k) ∧
          (∀ j : Fin N, ∀ p ∈ cthickening (δ/8) (tsupport (m j.castSucc)),
            ∀ q, p = q ∨ reflectedProofRelation R p q →
              closedBall q (δ/8) ⊆ interior {p | m j.succ p = 1}) ∧
          (∀ j p, p ∈ tsupport (m j) →
            closedBall p (δ/8) ⊆ interior {p | mi p = 1}) := by
  obtain ⟨H, hH, hcut⟩ :=
    exists_uniform_even_bufferedReachableAt_localizers hmi.isCompact hδ N
  refine ⟨H, hH, ?_⟩
  intro R S hR hS hsym hprop
  have hcarrier : ∀ n ≤ N, bufferedReachableAt (reflectedProofRelation R) S δ n ⊆
      tsupport mi := by
    intro n hn p hp
    apply subset_tsupport mi
    have hone : mi p = 1 := interior_subset (s := {p | mi p = 1})
      (hprop n hn (self_subset_cthickening _ hp))
    change mi p ≠ 0
    rw [hone]
    exact one_ne_zero
  obtain ⟨m, hsmooth, hrange, hcompact, heven, hplateau, hsupp, hshoulder, hjet, hnest⟩ :=
    hcut R S hR hS hsym hcarrier
  have hterminal (j : Fin (N+1)) : cthickening (δ/8) (tsupport (m j)) ⊆
      interior {p | mi p = 1} := (hshoulder j).trans (hprop j.val (by omega))
  exact ⟨m, hsmooth, hrange, hcompact, heven, hplateau, hsupp, hshoulder,
    hterminal, hjet, hnest, fun j p hp ↦ (closedBall_subset_cthickening hp _).trans
      (hterminal j)⟩

/-- Append the prescribed common mask as the literal last localizer, with
an identity step after the original word. The original even masks and their
ordering are unchanged. The terminal step uses the proved closed shoulder,
and the derivative bound is the maximum of the two already fixed profiles.
This geometric extension supplies the final mask for `hBnear`; it does not
assert that either right quantization is idempotent or that the appended
mask is even (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:resolved-angular-tail`). -/
theorem prescribed_terminal_identity_extension {N : ℕ}
    (m : Fin (N+1) → LocalizerSymbol (d+1)) (mi : LocalizerSymbol (d+1))
    {θ : ℝ} (hθ : 0 < θ) (R : P → P → Prop)
    (heven : ∀ k y ξ, m k (y, -ξ) = m k (y, ξ))
    (hstep : ∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
      p = q ∨ R p q → closedBall q θ ⊆ interior {p | m k.succ p = 1})
    (hterminal : cthickening θ (tsupport (m (Fin.last N))) ⊆ interior {p | mi p = 1})
    (H Djet : ℕ → ℝ)
    (hjet : ∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ H l)
    (hjetTerminal : ∀ l p, ‖iteratedFDeriv ℝ l mi p‖ ≤ Djet l) :
    let μ : Fin (N+2) → LocalizerSymbol (d+1) := Fin.snoc m mi
    μ (Fin.last (N+1)) = mi ∧
    (∀ k : Fin (N+1), μ k.castSucc = m k) ∧
    (∀ (k : Fin (N+1)) y ξ, μ k.castSucc (y, -ξ) = μ k.castSucc (y, ξ)) ∧
    (∀ k l p, ‖iteratedFDeriv ℝ l (μ k) p‖ ≤ max (H l) (Djet l)) ∧
    ∀ k : Fin (N+1), ∀ p ∈ cthickening (θ/2) (tsupport (μ k.castSucc)), ∀ q,
      p = q ∨ (k.val < N ∧ R p q) →
        closedBall q (θ/2) ⊆ interior {p | μ k.succ p = 1} := by
  intro μ
  refine ⟨Fin.snoc_last _ _, fun k ↦ Fin.snoc_castSucc _ _ k, ?_, ?_, ?_⟩
  · simpa only [μ, Fin.snoc_castSucc] using heven
  · intro k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · intro l p
      simpa only [μ, Fin.snoc_last] using
        (hjetTerminal l p).trans (le_max_right (H l) (Djet l))
    · intro l p
      simpa only [μ, Fin.snoc_castSucc] using
        (hjet j l p).trans (le_max_left (H l) (Djet l))
  · intro k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · intro p hp q hpq
      have hpq' : p = q := hpq.elim id (fun h ↦ (Nat.lt_irrefl N h.1).elim)
      subst q
      have hp' : p ∈ cthickening (θ/2) (tsupport (m (Fin.last N))) := by
        simpa only [μ, Fin.snoc_castSucc] using hp
      have hb : closedBall p (θ/2) ⊆ interior {p | mi p = 1} := by
        apply (closedBall_subset_cthickening hp' (θ/2)).trans
        apply (cthickening_cthickening_subset (by positivity) (by positivity) _).trans
        have heq : θ/2 + θ/2 = θ := by ring
        simpa only [heq] using hterminal
      simpa only [μ, Fin.succ_last, Fin.snoc_last] using hb
    · intro p hp q hpq
      have hp' : p ∈ cthickening θ (tsupport (m j.castSucc)) :=
        cthickening_mono (δ₁ := θ/2) (δ₂ := θ) (by linarith) _ (by
          simpa only [μ, Fin.snoc_castSucc] using hp)
      have hb := (closedBall_subset_closedBall (show θ/2 ≤ θ by linarith)).trans
        (hstep j p hp' q (hpq.imp_right And.right))
      simpa only [μ, ← Fin.castSucc_succ, Fin.snoc_castSucc] using hb

end JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection
