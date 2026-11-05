module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Finite minima for the actual carrier buffers

The elementary finite choice used by `exists_finite_carrierPhase_assembly`
(`app:ch_seed:prop:seed-actual-menu`, Step 1). Including one default entry handles
an empty menu without imposing a spurious nonempty-patch hypothesis.
-/

@[expose] public noncomputable section

namespace JanetCartan.ActualCarriers

/-- Actual finite minima of local radii and thresholds, and a finite maximum of
comparison constants (`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). The radii
`r`, `2*r`, `3*r` provide inner, outer and construction buffers inside the unit
ball. This also applies when the patch index type is empty. -/
theorem exists_common_phase_buffers {I : Type*} [Fintype I]
    (radius threshold coefficient : I → ℝ)
    (hradius : ∀ i, 0 < radius i) (hthreshold : ∀ i, 0 < threshold i) :
    ∃ r δ K : ℝ, 0 < r ∧ 3 * r < 1 ∧ 0 < δ ∧ 0 < K ∧
      ∀ i, 3 * r < radius i ∧ δ ≤ threshold i ∧ coefficient i ≤ K := by
  classical
  let s : Finset (Option I) := Finset.univ
  have hs : s.Nonempty := ⟨none, Finset.mem_univ _⟩
  let R : Option I → ℝ := fun i ↦ i.elim 1 radius
  let T : Option I → ℝ := fun i ↦ i.elim 1 threshold
  let A : Option I → ℝ := fun i ↦ i.elim 1 coefficient
  let m := s.inf' hs R
  let δ := s.inf' hs T
  let K := s.sup' hs A
  have hm : 0 < m := (Finset.lt_inf'_iff hs).mpr (by
    intro i _; cases i with
    | none => norm_num [R]
    | some i => exact hradius i)
  have hδ : 0 < δ := (Finset.lt_inf'_iff hs).mpr (by
    intro i _; cases i with
    | none => norm_num [T]
    | some i => exact hthreshold i)
  have hm1 : m ≤ 1 := Finset.inf'_le R (Finset.mem_univ (none : Option I))
  have hK : 1 ≤ K := Finset.le_sup' A (Finset.mem_univ (none : Option I))
  refine ⟨m / 4, δ, K, by positivity, by linarith, hδ, by linarith, ?_⟩
  intro i
  have hmi : m ≤ radius i := Finset.inf'_le R (Finset.mem_univ (some i))
  exact ⟨by linarith, Finset.inf'_le T (Finset.mem_univ (some i)),
    Finset.le_sup' A (Finset.mem_univ (some i))⟩

/-- The radii chosen by finite phase assembly give actual compact containments
inside the unit physical ball (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem common_phase_buffer_containment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {r : ℝ} (hr : 0 < r) (hr1 : 3 * r < 1) :
    IsCompact (closure (Metric.ball (0 : E) r)) ∧
    closure (Metric.ball (0 : E) r) ⊆ Metric.ball 0 (2 * r) ∧
    IsCompact (closure (Metric.ball (0 : E) (2 * r))) ∧
    closure (Metric.ball (0 : E) (2 * r)) ⊆ Metric.ball 0 (3 * r) ∧
    Metric.closedBall (0 : E) (3 * r) ⊆ Metric.ball 0 1 := by
  exact ⟨(isCompact_closedBall (0 : E) r).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall,
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith)),
    (isCompact_closedBall (0 : E) (2 * r)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall,
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith)),
    Metric.closedBall_subset_ball hr1⟩

end JanetCartan.ActualCarriers
