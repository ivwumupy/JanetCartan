module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CompactRelations.Bounds
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Carriers

/-!
# A common annulus for the original root sections

The whole-segment reflected transport estimate needs a symmetric annulus
before the current roots are chosen. Derive it directly from the fixed section,
transverse ball and root-value constants of the same selected family.
Consumer: `exists_uniform_reflectedProofRelation_comparison_transport`, for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks RegularSector.Characteristic FiniteChain.Graph

variable {d : ℕ}

/-- The original primitive section bounds fix an annulus for every root
state before the roots and coefficient field vary. The annulus also contains
the reflected covectors, since their norms agree
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_rootSection_annular_bounds
    {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (ε G : J → ℝ) (hG : ∀ j, 0 ≤ G j) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∀ (j : J) (i : Fin (d + 1)) (h : RootState (Euclidean d) → ℝ)
        (v : RootState (Euclidean d)),
        v.2.2 ∈ closedBall (η₀ j) (ε j) → (1 / 2 : ℝ) ≤ ℓ j v.2.2 →
        |h v| ≤ ℓ j v.2.2 * G j →
        (physicalPencilRootState (coordinateSplit i) h v).2 ∈
          PhysicalShells.frequencyAnnulus a b := by
  classical
  let := Fintype.ofFinite J
  let lower : Option J → ℝ := fun j ↦ j.elim 1 (fun j ↦ 1 / (2 * (‖ℓ j‖ + 1)))
  let upper : Option J → ℝ := fun j ↦ j.elim 1
    (fun j ↦ (‖ℓ j‖ * (‖η₀ j‖ + ε j)) * G j + (‖η₀ j‖ + ε j))
  let a := Finset.univ.inf' Finset.univ_nonempty lower
  let b₀ := Finset.univ.sup' Finset.univ_nonempty upper
  have ha : 0 < a := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro j _
    cases j <;> dsimp [lower] <;> positivity
  refine ⟨a, max a b₀ + 1, ha, by linarith [le_max_left a b₀], ?_⟩
  intro j i h v hball hsec hval
  obtain ⟨_, hlo, hup, hval'⟩ :=
    rootBuffer_bounds_of_section_and_ball (ℓ j) (η₀ j) (hG j) hball hsec hval
  obtain ⟨hl, hu⟩ := physicalPencilRootState_covector_bounds i h v hlo hup hval'
  have hlow : a ≤ 1 / (2 * (‖ℓ j‖ + 1)) :=
    Finset.inf'_le lower (Finset.mem_univ (some j))
  have hhigh : (‖ℓ j‖ * (‖η₀ j‖ + ε j)) * G j + (‖η₀ j‖ + ε j) ≤ b₀ :=
    Finset.le_sup' upper (Finset.mem_univ (some j))
  exact ⟨hlow.trans hl,
    (hu.trans hhigh).trans ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))⟩

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
