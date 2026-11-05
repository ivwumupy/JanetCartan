module

public import JanetCartan.Analysis.Fourier.Periodic.Calculus
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.Neighborhood

/-!
# Seminorms of actual finite histories

The passage from periodic increment norms to the map on the physical chart in
`main:lem:history`. The shared `currentHistoryMap` comes from the independent
neighborhood leaf; no coefficient estimate is used here.
-/

@[expose] public noncomputable section

namespace JanetCartan
namespace BandHistory

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:history`: joint continuity of the derivatives on the compact
parameter and coordinate sets gives one initial seminorm bound for the family.
No regularity away from those sets is required. -/
theorem exists_cNorm_bound_on_compact_family
    {P : Type*} [TopologicalSpace P] {S : Set P} (hS : IsCompact S)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {f : P → EuclideanSpace ℝ (Fin n) → F} (r : ℕ)
    (hf : ∀ d ≤ r, ContinuousOn (fun px : P × EuclideanSpace ℝ (Fin n) ↦
      iteratedFDeriv ℝ d (f px.1) px.2) (S ×ˢ K)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ S, cNorm K r (f p) ≤ A := by
  have hb : ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (_ : d ≤ r) (p : P), p ∈ S →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ d (f p) x‖ ≤ C := by
    intro d
    by_cases hd : d ≤ r
    · obtain ⟨C, hC⟩ := (hS.prod hK).exists_bound_of_continuousOn (hf d hd)
      exact ⟨max 0 C, le_max_left _ _, fun _ p hp x hx ↦
        (hC (p, x) ⟨hp, hx⟩).trans (le_max_right _ _)⟩
    · exact ⟨0, le_rfl, fun hd' ↦ (hd hd').elim⟩
  choose C hC hb using hb
  refine ⟨∑ d ∈ Finset.range (r + 1), C d,
    Finset.sum_nonneg (fun d _ ↦ hC d), ?_⟩
  intro p hp
  exact cNorm_le_sum_of_bounds (fun d _ ↦ hC d) (fun d hd ↦ hb d hd p hp)

/-- `main:lem:history`: the cell seminorm bounds a periodic lift on any set,
with no order-dependent loss. -/
theorem cNorm_periodicLift_le_cell (s : Set (EuclideanSpace ℝ (Fin n)))
    (r : ℕ) {f : Torus n → F} (hf : IsSmoothPeriodic f) :
    cNorm s r (periodicLift f) ≤ cNorm (fundamentalCell n) r (periodicLift f) := by
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ sSup_norm_iteratedFDeriv_nonneg (fundamentalCell n) j (periodicLift f))
  intro j hj x _
  apply norm_iteratedFDeriv_periodicLift_le f j _ x
  intro y hy
  exact le_csSup (bddAbove_norm_iteratedFDeriv (isCompact_fundamentalCell n)
    (hf.2.of_le (by simp)) hj) (Set.mem_image_of_mem _ hy)

/-- `main:eq:history-current`: the actual history on a compact set is bounded
by its initial seminorm and the sum of periodic increment seminorms. -/
theorem cNorm_currentHistoryMap_le {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : IsCompact s) (r : ℕ) {f₀ : EuclideanSpace ℝ (Fin n) → F}
    (hf₀ : ∀ x ∈ s, ContDiffAt ℝ r f₀ x) {u : ℕ → Torus n → F}
    (hu : ∀ i, IsSmoothPeriodic (u i)) (j : ℕ) :
    cNorm s r (currentHistoryMap f₀ (fun i ↦ periodicLift (u i)) j) ≤
      cNorm s r f₀ + ∑ i ∈ Finset.range j,
        cNorm (fundamentalCell n) r (periodicLift (u i)) := by
  apply (cNorm_add_le_of_contDiffAt hs hf₀
    (fun x _ ↦ ContDiffAt.sum (fun i _ ↦
      ((hu i).2.of_le (by simp)).contDiffAt))).trans
  apply add_le_add_right
  exact (cNorm_sum_le (Finset.range j) hs
    (fun i _ ↦ (hu i).2.of_le (by simp))).trans
      (Finset.sum_le_sum (fun i _ ↦ cNorm_periodicLift_le_cell s r (hu i)))

end BandHistory
end JanetCartan
