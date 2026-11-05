module

public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.Iteration.BandHistory.Geometric

/-!
# Persistence of the reference neighborhood for finite histories

Section 9, `main:eq:displacement-budget`. Only bounds on the already constructed
prefix are required. The increment bounds remain explicit inputs; this module
does not construct the corrections or the reference neighborhood.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open Filter

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:eq:displacement-budget`: the actual compact derivative seminorm of a
finite history is bounded independently of its length. No information about
increments after stage `J` is needed. -/
theorem cNorm_finiteHistory_le_historyBound {s : Set E} {r J : ℕ}
    {u : ℕ → E → F} {C R v μ : ℝ}
    (hs : IsCompact s) (hu : ∀ i < J, ContDiff ℝ r (u i))
    (hR : 1 < R) (hv : 1 < v) (hμ : 0 < μ) (hC : 0 ≤ C)
    (hbound : ∀ i < J, cNorm s r (u i) ≤ C * historyScale R v i ^ (-μ)) :
    cNorm s r (fun x ↦ ∑ i ∈ Finset.range J, u i x) ≤ historyBound C R v μ := by
  have hnonneg (i : ℕ) : 0 ≤ C * historyScale R v i ^ (-μ) :=
    mul_nonneg hC (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)
  have hsum : Summable (fun i ↦ C * historyScale R v i ^ (-μ)) :=
    summable_of_history_bound hR hv hμ hC hnonneg (fun _ ↦ le_rfl)
  calc
    _ ≤ ∑ i ∈ Finset.range J, cNorm s r (u i) :=
      cNorm_sum_le _ hs (fun i hi ↦ hu i (Finset.mem_range.mp hi))
    _ ≤ ∑ i ∈ Finset.range J, C * historyScale R v i ^ (-μ) :=
      Finset.sum_le_sum (fun i hi ↦ hbound i (Finset.mem_range.mp hi))
    _ ≤ ∑' i, C * historyScale R v i ^ (-μ) :=
      hsum.sum_le_tsum _ (fun i _ ↦ hnonneg i)
    _ ≤ _ := tsum_le_historyBound hR hv hμ hC hnonneg (fun _ ↦ le_rfl)

/-- `main:eq:displacement-budget`: one initial-scale threshold controls every
finite history in the same reference ball. The threshold is chosen before the
increments and depends only on their prospective decay constants. -/
theorem exists_initialScale_for_finiteHistory {v μ ε : ℝ} (C : ℝ)
    (hC : 0 ≤ C) (hv : 1 < v) (hμ : 0 < μ) (hε : 0 < ε) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R : ℝ, T ≤ R →
      ∀ (s : Set E) (r J : ℕ) (G : E → F) (u : ℕ → E → F),
        IsCompact s → (∀ i < J, ContDiff ℝ r (u i)) →
        (∀ i < J, cNorm s r (u i) ≤ C * historyScale R v i ^ (-μ)) →
        cNorm s r ((fun x ↦ G x + ∑ i ∈ Finset.range J, u i x) - G) < ε / 2 := by
  have hevent : ∀ᶠ R : ℝ in atTop, historyBound C R v μ < ε / 2 :=
    (tendsto_historyBound C hv hμ).eventually (gt_mem_nhds (by linarith))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨max 2 T, le_max_left _ _, ?_⟩
  intro R hR s r J G u hs hu hbound
  have hR₂ : 2 ≤ R := (le_max_left _ _).trans hR
  have heq : ((fun x ↦ G x + ∑ i ∈ Finset.range J, u i x) - G) =
      fun x ↦ ∑ i ∈ Finset.range J, u i x := by
    funext x
    simp only [Pi.sub_apply, add_sub_cancel_left]
  rw [heq]
  exact (cNorm_finiteHistory_le_historyBound hs hu (by linarith) hv hμ hC hbound).trans_lt
    (hT R ((le_max_right _ _).trans hR))

end JanetCartan
