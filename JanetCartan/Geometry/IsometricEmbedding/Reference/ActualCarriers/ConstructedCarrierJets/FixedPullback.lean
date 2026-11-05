module

public import JanetCartan.Analysis.ContDiff.Norm.Composition
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Fixed pullbacks of carrier jets

Composition with the fixed patch restriction or incidence coordinate map is
linear in the varying outer jet. These estimates supply Steps 2–3 of
`app:ch_seed:prop:seed-actual-menu`; their constants contain only fixed maps.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ActualCarriers.ConstructedCarrierJets

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A fixed smooth restriction has a linear outer-jet budget. The inner
budgets follow from compactness, rather than being analytic inputs
(`app:ch_seed:eq:seed-phase-tame`, Steps 2–3). -/
theorem exists_cNorm_fixed_pullback_le_jet_bound {K : Set E} (hK : IsCompact K)
    {ψ : E → F} (hψ : ∀ x ∈ K, ContDiffAt ℝ ∞ ψ x) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f : F → G) (A : ℝ), 0 ≤ A →
      (∀ x ∈ K, ContDiffAt ℝ m f (ψ x)) →
      (∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f (ψ x)‖ ≤ A) →
      cNorm K m (f ∘ ψ) ≤ C * A := by
  let D := compositionMultiplicity m * (1 + cNorm K m ψ) ^ m
  have hD : 0 ≤ D := by
    have hm : 0 ≤ compositionMultiplicity m :=
      Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
    exact mul_nonneg hm (pow_nonneg (by linarith [cNorm_nonneg K m ψ]) _)
  refine ⟨D + 1, by positivity, fun f A hA hf hb ↦ ?_⟩
  have h := cNorm_comp_le_polynomial
    (fun x hx ↦ (hψ x hx).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) hf
    (fun j hj ↦ bddAbove_norm_iteratedFDeriv_of_contDiffAt hK
      (fun x hx ↦ (hψ x hx).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) hj) hA hb
  calc
    _ ≤ D * A := h.trans_eq (by dsimp [D]; ring)
    _ ≤ (D + 1) * A := mul_le_mul_of_nonneg_right (by linarith) hA

/-- Compact target seminorms supply the outer jets for the literal fixed
restriction, without derivative loss (`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_cNorm_fixed_pullback_le {K : Set E} {L : Set F}
    (hK : IsCompact K) (hL : IsCompact L) {ψ : E → F}
    (hψ : ∀ x ∈ K, ContDiffAt ℝ ∞ ψ x) (hψL : MapsTo ψ K L) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ (f : F → G),
      (∀ x ∈ L, ContDiffAt ℝ ∞ f x) →
      ∀ m, cNorm K m (f ∘ ψ) ≤ C m * cNorm L m f := by
  choose C hC hb using fun m ↦ exists_cNorm_fixed_pullback_le_jet_bound
    (G := G) hK hψ m
  refine ⟨C, hC, fun f hf m ↦ hb m f _ (cNorm_nonneg ..)
    (fun x hx ↦ (hf _ (hψL hx)).of_le (by simp)) ?_⟩
  intro j hj x hx
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
    (fun y hy ↦ (hf y hy).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) (hψL hx) hj

end JanetCartan.ActualCarriers.ConstructedCarrierJets
