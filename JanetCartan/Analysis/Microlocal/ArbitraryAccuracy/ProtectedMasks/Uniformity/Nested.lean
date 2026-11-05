module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Cutoffs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Shoulders

/-!
# Uniform nested cutoffs on the explicit buffered images

The physical propagation theorem supplies the compact envelope and shoulder
width used here. The finite cutoff menu then supplies all derivative bounds
before the relation varies. Extra room on both sides of each relation step is
retained for the quantitative localization gaps in `app:ch_regular:eq:chain-tail`.
This deduction is instantiated for the actual physical relation in `Masks`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open ProtectedFlow FiniteChain.Graph

variable {d : ℕ}

/-- The original complete chain lies in its explicit enlarged image, including
all diagonal steps (`app:ch_regular:lem:finite-chain`). -/
theorem reachableAt_subset_bufferedReachableAt
    (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) (δ : ℝ) (n : ℕ) :
    reachableAt R S n ⊆ bufferedReachableAt R S δ n := by
  have hchain {p q} {n} (hc : PositiveConicChain R p q n) :
      ∀ k, p ∈ bufferedReachableAt R S δ k →
        q ∈ bufferedReachableAt R S δ (k + n) := by
    induction hc with
    | refl p => intro k hp; simpa using hp
    | @tail p q z n hpq hc ih =>
      intro k hp
      have hq := mem_bufferedReachableAt_succ_of_step
        (self_subset_cthickening (δ := δ) _ hp) hpq
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih (k + 1) hq
  rintro q ⟨p, hp, hc⟩
  simpa using hchain hc 0 hp

/-- From the explicit common closed-shoulder carrier choose nested physical
cutoffs with a common derivative sequence. The conclusion protects the entire
closed `δ / 8` input shoulder and a closed `δ / 8` output ball. The compactness
and carrier inputs are produced by `Propagation.Physical`; they are discharged
in `Masks.exists_uniform_nested_physicalDirectLocalizers`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_uniform_bufferedReachableAt_localizers
    {B : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hB : IsCompact B)
    {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∃ H : ℕ → ℝ, (∀ k, 0 ≤ H k) ∧
      ∀ (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
        (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
        (S : Set (Euclidean (d + 1) × Euclidean (d + 1))),
        IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
          (Euclidean (d + 1) × Euclidean (d + 1)) | R pq.1 pq.2} →
        IsCompact S →
        (∀ n ≤ N, bufferedReachableAt R S δ n ⊆ B) →
        ∃ m : Fin (N + 1) → LocalizerSymbol (d + 1),
          (∀ j, ContDiff ℝ ∞ (m j)) ∧
          (∀ j p, m j p ∈ Icc (0 : ℝ) 1) ∧
          (∀ j, HasCompactSupport (m j)) ∧
          (∀ j, cthickening (δ / 8) (bufferedReachableAt R S δ j.val) ⊆
            interior {p | m j p = 1}) ∧
          (∀ j, tsupport (m j) ⊆
            cthickening (δ / 2) (bufferedReachableAt R S δ j.val)) ∧
          (∀ j, cthickening (δ / 8) (tsupport (m j)) ⊆
            cthickening δ (bufferedReachableAt R S δ j.val)) ∧
          (∀ j k p, ‖iteratedFDeriv ℝ k (m j) p‖ ≤ H k) ∧
          (∀ j : Fin N, ∀ p ∈ cthickening (δ / 8) (tsupport (m j.castSucc)),
            ∀ q, p = q ∨ R p q → closedBall q (δ / 8) ⊆
              interior {p | m j.succ p = 1}) := by
  obtain ⟨H, hH, hcut⟩ := exists_uniform_physicalLocalizer_cutoffs hB
    (show 0 < δ / 2 by positivity)
  refine ⟨H, hH, ?_⟩
  intro R S hR hS hcarrier
  have hchoose (j : Fin (N + 1)) := hcut (bufferedReachableAt R S δ j.val)
    (isCompact_bufferedReachableAt hR hS δ j.val) (hcarrier j.val (by omega))
  choose m hsmooth hrange hcompact hplateau hsupp hjet using hchoose
  have hplateau' j : cthickening (δ / 8) (bufferedReachableAt R S δ j.val) ⊆
      interior {p | m j p = 1} := by
    simpa only [div_div, show (2 : ℝ) * 4 = 8 from by norm_num] using hplateau j
  have hshoulder j : cthickening (δ / 8) (tsupport (m j)) ⊆
      cthickening δ (bufferedReachableAt R S δ j.val) :=
    (cthickening_subset_of_subset _ (hsupp j)).trans
      ((cthickening_cthickening_subset (by positivity) (by positivity) _).trans
        (cthickening_mono (by linarith) _))
  refine ⟨m, hsmooth, hrange, hcompact, hplateau', hsupp, hshoulder, hjet, ?_⟩
  intro j p hp q hpq v hv
  exact hplateau' j.succ (closedBall_subset_cthickening
    (mem_bufferedReachableAt_succ_of_step (hshoulder j.castSucc hp) hpq) _ hv)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
