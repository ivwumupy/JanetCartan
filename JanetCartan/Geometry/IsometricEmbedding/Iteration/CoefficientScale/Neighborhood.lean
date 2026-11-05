module

public import JanetCartan.Analysis.Iteration.BandHistory.Geometric
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# A single low-order neighborhood for every finite history

The neighborhood step of `main:prop:current-scale`, from the low-order increment
decay in `main:eq:history-bernstein`. The inputs are bounds for the actual
derivative seminorms. Proving these bounds from Fourier support is a separate
analytic step, owned by `BandHistory` and the Bernstein modules.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped ContDiff

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:history`: the actual finite history, before any coefficient construction. -/
def currentHistoryMap (f₀ : E → F) (u : ℕ → E → F) (j : ℕ) : E → F :=
  fun x ↦ f₀ x + ∑ i ∈ Finset.range j, u i x

/-- `main:eq:total-small`, `main:prop:current-scale`: every partial displacement
has the same explicit bound, for actual smooth increments on a compact set. -/
theorem cNorm_history_displacement_le
    {s : Set E} (hs : IsCompact s) (r : ℕ) {C R v μ : ℝ}
    (hR : 1 < R) (hv : 1 < v) (hμ : 0 < μ) (hC : 0 ≤ C)
    (u : ℕ → E → F) (hu : ∀ i, ContDiff ℝ r (u i))
    (hbound : ∀ i, cNorm s r (u i) ≤ C * historyScale R v i ^ (-μ))
    (f₀ : E → F) (j : ℕ) :
    cNorm s r (currentHistoryMap f₀ u j - f₀) ≤
      historyBound C R v μ := by
  change cNorm s r (fun x ↦ (f₀ x + ∑ i ∈ Finset.range j, u i x) - f₀ x) ≤ _
  simp only [add_sub_cancel_left]
  have hnonneg := fun i ↦ cNorm_nonneg s r (u i)
  exact (cNorm_sum_le (Finset.range j) hs (fun i _ ↦ hu i)).trans
    (((summable_of_history_bound hR hv hμ hC hnonneg hbound).sum_le_tsum
      (Finset.range j) (fun i _ ↦ hnonneg i)).trans
        (tsum_le_historyBound hR hv hμ hC hnonneg hbound))

/-- `main:prop:current-scale`: one scale threshold puts every finite history
in a prescribed `C^r` neighborhood of its initial map. The threshold precedes
the increments, the initial map and the stage, so it also works uniformly for
families and for all requested high derivative orders and accuracies. -/
theorem exists_uniform_history_neighborhood
    {s : Set E} (hs : IsCompact s) (r : ℕ) {C v μ ε : ℝ}
    (hv : 1 < v) (hμ : 0 < μ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ R ≥ Rmin, ∀ u : ℕ → E → F,
      (∀ i, ContDiff ℝ r (u i)) →
      (∀ i, cNorm s r (u i) ≤ C * historyScale R v i ^ (-μ)) →
      ∀ (f₀ : E → F) (j : ℕ),
        cNorm s r (currentHistoryMap f₀ u j - f₀) < ε := by
  obtain ⟨S, hS⟩ := eventually_atTop.1
    ((tendsto_historyBound C hv hμ).eventually (gt_mem_nhds hε))
  refine ⟨max 2 S, le_max_left _ _, ?_⟩
  intro R hR u hu hbound f₀ j
  have hRtwo : 2 ≤ R := (le_max_left _ _).trans hR
  exact (cNorm_history_displacement_le hs r (by linarith) hv hμ hC u hu hbound f₀ j).trans_lt
    (hS R ((le_max_right _ _).trans hR))

end JanetCartan
