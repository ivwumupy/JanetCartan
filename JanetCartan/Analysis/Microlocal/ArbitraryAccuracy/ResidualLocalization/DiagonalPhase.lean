module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades.Coordinates
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.PhaseExtension

/-!
# Fixed phase grades for the complete residual's canonical PDO branches

The physical PDO phase is the exact diagonal phase. Its packed phase grades
are fixed compact seminorms, with no assumptions on a varying phase or on a
successful kernel estimate. Consumer: `exists_directPDO_fourier_bound`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open FourierIntegral FourierIntegral.FullAmplitudePrimitiveBudget FiniteChain.Graph
open EvolutionLocalization.PrimitiveGrades
variable {n : ℕ}
local notation "E" => Euclidean n

private theorem contDiff_diagonalJointPhase (backward : Bool) :
    ContDiff ℝ ∞ (fun p : E × E × JointVariables E ↦
      jointPhase backward (fun u ξ ↦ inner ℝ u ξ) p.1 p.2.1 p.2.2) := by
  cases backward <;>
    simp only [jointPhase, Bool.false_eq_true, ite_false, ite_true, forwardPhase, reversePhase]
  all_goals
    apply ContDiff.add
    · apply ContDiff.add
      · exact (ContDiff.inner ℝ (by fun_prop) (by fun_prop)).sub
          (ContDiff.inner ℝ (by fun_prop) (by fun_prop))
      · exact ContDiff.inner ℝ (by fun_prop) (by fun_prop)
    · exact ContDiff.inner ℝ (by fun_prop) (by fun_prop)

/-- All packed diagonal phase grades, uniformly over the actual compact
physical carriers, for either literal orientation. The constants precede
`L`, and the higher derivative cost is `L^k`. Thus diagonal factors require
no phase-budget premise in the residual localization theorem
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_diagonal_jointPhase_grades (backward : Bool)
    {X Y : Set E} {K : Set (JointVariables E)}
    (hX : IsCompact X) (hY : IsCompact Y) (hK : IsCompact K) :
    ∃ (G : ℝ) (P : ℕ → ℝ), (∀ k, 0 ≤ P k) ∧
      ∀ L : ℝ, 1 ≤ L →
      (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ K,
        ‖fderiv ℝ (jointPhase backward (fun u ξ ↦ inner ℝ u ξ) x y) p‖ ≤ G) ∧
      (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ K, ∀ k, 1 ≤ k →
        ‖iteratedFDeriv ℝ (k + 1)
          (jointPhase backward (fun u ξ ↦ inner ℝ u ξ) x y) p‖ ≤ P k * L ^ k) := by
  let F := fun p : E × E × JointVariables E ↦
    jointPhase backward (fun u ξ ↦ inner ℝ u ξ) p.1 p.2.1 p.2.2
  let B := fun k ↦ cNorm (X ×ˢ Y ×ˢ K) k F
  have hF : ContDiff ℝ ∞ F := contDiff_diagonalJointPhase backward
  have hB k : 0 ≤ B k := cNorm_nonneg _ _ _
  have hb (x : E) (hx : x ∈ X) (y : E) (hy : y ∈ Y)
      (p : JointVariables E) (hp : p ∈ K) (k : ℕ) :
      ‖iteratedFDeriv ℝ k (jointPhase backward (fun u ξ ↦ inner ℝ u ξ) x y) p‖ ≤ B k := by
    let l : JointVariables E →L[ℝ] E × E × JointVariables E :=
      (0 : JointVariables E →L[ℝ] E).prod
        ((0 : JointVariables E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ _))
    have hl : ‖l‖ ≤ 1 := by
      apply l.opNorm_le_bound zero_le_one
      intro p
      simp [l, Prod.norm_def]
    have hc := norm_iteratedFDeriv_affine_contraction_le l hl (x, y, 0)
      isOpen_univ hF.contDiffOn (p := p) (mem_univ _) k
    have hc' : ‖iteratedFDeriv ℝ k
        (jointPhase backward (fun u ξ ↦ inner ℝ u ξ) x y) p‖ ≤
        ‖iteratedFDeriv ℝ k F (x, y, p)‖ := by
      simpa [l, F] using hc
    exact hc'.trans (norm_iteratedFDeriv_le_cNorm (hX.prod (hY.prod hK))
      (hF.of_le (by simp)) ⟨hx, hy, hp⟩ (le_refl k))
  refine ⟨B 1, fun k ↦ B (k + 1), fun k ↦ hB _, fun L hL ↦ ⟨?_, ?_⟩⟩
  · intro x hx y hy p hp
    rw [← norm_iteratedFDeriv_one]
    exact hb x hx y hy p hp 1
  · intro x hx y hy p hp k _
    exact (hb x hx y hy p hp (k + 1)).trans
      (le_mul_of_one_le_right (hB _) (one_le_pow₀ hL))

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
