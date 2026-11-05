module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.Assembly

/-!
# Reindexing the original finite terminal masks for observed chains

Even masks are right input localizers and odd masks are left output
localizers. One additional terminal-mask edge retains the estimate at the
last even mask, including the depth-zero case.
-/

@[expose] public noncomputable section

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization

variable {ι α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reindex the original terminal producer's `2*n+2` masks into the six
localizer inputs of `ObservedChains.measuredResidual_hchain_of_individual_estimates`.
The terminal producer is invoked at `N = 2*n+1`: its terminal estimate only
covers `k : Fin N`, so this extra edge is needed for the final even mask.
The supplied factor estimate comes from
`exists_retained_prescribed_complete_residual_leakage_constants`; the low,
cross and terminal estimates come from the same retained masks in
`exists_selected_terminal_even_masks_with_localizer_estimates`. The source
input is the original primary or signed first-mask estimate. No word decay
is assumed (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_observedChain_localizers_of_finite_terminal_masks
    (G : GradedScale E) (n : ℕ) (T : α → ι → E →ₗ[ℝ] E)
    (source : ι → E) (ρ slowScale A : ι → ℝ)
    (terminal : ι → E →ₗ[ℝ] E)
    (Rfin Lfin : Fin (2*n+2) → ι → E →ₗ[ℝ] E)
    (hsource : ∀ s, RapidDecayAt G s ρ A
      (fun i ↦ source i - Rfin 0 i (source i)))
    (hnear : ∀ k a, ∃ C c : ℝ, 0 ≤ C ∧ ∀ i v,
      ‖T a i (Rfin k i v)‖ ≤ C*(ρ i)^c*‖v‖)
    (hleft : ∀ k, ∃ C c : ℝ, 0 ≤ C ∧ ∀ i v,
      ‖Lfin k i v‖ ≤ C*(ρ i)^c*‖v‖)
    (hfactor : ∀ (k : Fin (2*n+1)) a s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-Lfin k.succ i) (T a i (Rfin k.castSucc i v)) ∈ G.level s ∧
        G.gradeNorm s ((1-Lfin k.succ i) (T a i (Rfin k.castSucc i v))) ≤
          C*(ρ i)^c*slowScale i^b*(slowScale i/ρ i)^q*‖v‖)
    (hcross : ∀ (k : Fin (2*n+1)) s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-Rfin k.succ i) (Lfin k.castSucc i v) ∈ G.level s ∧
        G.gradeNorm s ((1-Rfin k.succ i) (Lfin k.castSucc i v)) ≤
          C*(ρ i)^c*slowScale i^b*(slowScale i/ρ i)^q*‖v‖)
    (hterminal : ∀ (k : Fin (2*n+1)) s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-terminal i) (Rfin k.castSucc i v) ∈ G.level s ∧
        G.gradeNorm s ((1-terminal i) (Rfin k.castSucc i v)) ≤
          C*(ρ i)^c*slowScale i^b*(slowScale i/ρ i)^q*‖v‖) :
    ∃ right left : ℕ → ι → E →ₗ[ℝ] E,
      (∀ s, RapidDecayAt G s ρ A (fun i ↦ source i-right 0 i (source i))) ∧
      (∀ j < n, ∀ a, ∃ C c : ℝ, 0 ≤ C ∧ ∀ i v,
        ‖T a i (right j i v)‖ ≤ C*(ρ i)^c*‖v‖) ∧
      (∀ j < n, ∃ C c : ℝ, 0 ≤ C ∧ ∀ i v,
        ‖left j i v‖ ≤ C*(ρ i)^c*‖v‖) ∧
      (∀ j < n, ∀ a s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
          (1-left j i) (T a i (right j i v)) ∈ G.level s ∧
          G.gradeNorm s ((1-left j i) (T a i (right j i v))) ≤
            C*(ρ i)^c*slowScale i^b*(slowScale i/ρ i)^q*‖v‖) ∧
      (∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
          (1-right (j+1) i) (left j i v) ∈ G.level s ∧
          G.gradeNorm s ((1-right (j+1) i) (left j i v)) ≤
            C*(ρ i)^c*slowScale i^b*(slowScale i/ρ i)^q*‖v‖) ∧
      (∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
          (1-terminal i) (right n i v) ∈ G.level s ∧
          G.gradeNorm s ((1-terminal i) (right n i v)) ≤
            C*(ρ i)^c*slowScale i^b*(slowScale i/ρ i)^q*‖v‖) := by
  let right (j : ℕ) : ι → E →ₗ[ℝ] E :=
    if hj : j ≤ n then Rfin ⟨2*j, by omega⟩ else 0
  let left (j : ℕ) : ι → E →ₗ[ℝ] E :=
    if hj : j < n then Lfin ⟨2*j+1, by omega⟩ else 0
  have hr (j : ℕ) (hj : j ≤ n) : right j = Rfin ⟨2*j, by omega⟩ := dite_eq_left hj
  have hl (j : ℕ) (hj : j < n) : left j = Lfin ⟨2*j+1, by omega⟩ := dite_eq_left hj
  refine ⟨right, left, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hr 0 (Nat.zero_le n)]
    exact hsource s
  · intro j hj a
    rw [hr j (Nat.le_of_lt hj)]
    exact hnear ⟨2*j, by omega⟩ a
  · intro j hj
    rw [hl j hj]
    exact hleft ⟨2*j+1, by omega⟩
  · intro j hj a s
    rw [hr j (Nat.le_of_lt hj), hl j hj]
    exact hfactor ⟨2*j, by omega⟩ a s
  · intro j hj s
    rw [hr (j+1) (by omega), hl j hj]
    have hindex : (⟨2*(j+1), by omega⟩ : Fin (2*n+2)) =
        (⟨2*j+1, by omega⟩ : Fin (2*n+1)).succ := by
      apply Fin.ext
      dsimp
      omega
    rw [hindex]
    exact hcross ⟨2*j+1, by omega⟩ s
  · intro s
    rw [hr n le_rfl]
    exact hterminal ⟨2*n, by omega⟩ s

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
