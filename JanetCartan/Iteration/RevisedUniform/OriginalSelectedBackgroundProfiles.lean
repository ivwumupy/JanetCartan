module

public import JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistory
public import JanetCartan.Iteration.PhysicalHistory

/-!
# The actual selected history's fixed first-derivative bound

Specialize the genuine physical-history profile to the already selected final
compact core and the SAME dimension-only reference, band, history reserve and
minimum order. The coefficient precedes every target, approximation order,
initial scale and finite prefix. No containment in a different reference core
is assumed. Consumer: `RevisedStage.increment_estimates_of_physicalSobolev_profiles`
(the background derivative clause), hence `UniformHistoryCorrection.correction`
(`main:eq:history-current`, `main:thm:step`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles
open OriginalSelectedPrehistory
open PhysicalMean.OriginalCanonicalStaticReach

/-- The actual compact core and actual reference supply the fixed C¹ budget;
only admissibility of the original physical prefix is a history premise. -/
theorem exists_CF (d : ℕ) (hn : 5 ≤ d+1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R₀ : ℝ, 2 ≤ R₀ →
      ∀ (j : ℕ)
        (u : Fin j → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1))))
        (ell : Fin j → ℕ),
      RevisedGlobal.IsAdmissibleHistory historyBand R₀ (kMin d) u ell →
      ∀ x ∈ D d hn, ‖fderiv ℝ (RevisedGlobal.finiteMap (Gmap d hn) u) x‖ ≤ C := by
  have hG : ContDiff ℝ ∞ (Gmap d hn) := (Gref d hn).contDiff
  obtain ⟨A, hA, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (D_isCompact d hn) (fun x _ ↦ hG.contDiffAt)
    one_le_historyBand (kMin_history d)
  refine ⟨A 1, hA 1, ?_⟩
  intro R₀ hR₀ j u ell hu x hx
  have hF : ContDiff ℝ ∞ (RevisedGlobal.finiteMap (Gmap d hn) u) :=
    hG.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  have hpoint := norm_iteratedFDeriv_le_cNorm
    (s := D d hn) (r := 1) (j := 1)
    (f := RevisedGlobal.finiteMap (Gmap d hn) u)
    (D_isCompact d hn) (hF.of_le (by simp)) hx (by norm_num)
  have hbound := hprofile R₀ hR₀ j u ell hu (D d hn) (Set.Subset.refl _) 1
  have horder : 1 - rStar d = 0 := Nat.sub_eq_zero_of_le (by have := rStar_ge_eight d; omega)
  rw [horder, pow_zero, mul_one] at hbound
  simpa only [norm_iteratedFDeriv_one] using hpoint.trans hbound

/-- One dimension-only background coefficient, not a target/history choice. -/
def CF (d : ℕ) (hn : 5 ≤ d+1) : ℝ := (exists_CF d hn).choose

/-- Nonnegativity of the same early background coefficient. -/
theorem CF_nonneg (d : ℕ) (hn : 5 ≤ d+1) : 0 ≤ CF d hn :=
  (exists_CF d hn).choose_spec.1

/-- The literal current finiteMap obeys the early background budget on the
unchanged final core, for every admissible physical prefix. -/
theorem current_first_derivative (d : ℕ) (hn : 5 ≤ d+1)
    (R₀ : ℝ) (hR₀ : 2 ≤ R₀) (j : ℕ)
    (u : Fin j → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1))))
    (ell : Fin j → ℕ)
    (hu : RevisedGlobal.IsAdmissibleHistory historyBand R₀ (kMin d) u ell)
    (x : Euclidean (d+1)) (hx : x ∈ D d hn) :
    ‖fderiv ℝ (RevisedGlobal.finiteMap (Gmap d hn) u) x‖ ≤ CF d hn :=
  (exists_CF d hn).choose_spec.2 R₀ hR₀ j u ell hu x hx

end JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles
end
#print axioms JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles.exists_CF
#print axioms JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles.CF
#print axioms JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles.CF_nonneg
#print axioms JanetCartan.RevisedUniform.OriginalSelectedBackgroundProfiles.current_first_derivative
