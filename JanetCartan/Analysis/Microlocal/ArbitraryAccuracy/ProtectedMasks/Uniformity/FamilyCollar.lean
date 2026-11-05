module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ElapsedCutoff
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Margins

/-!
# One coefficient-uniform collar for the actual finite family

The individual root-flow budgets give a common positive elapsed collar and a
single smooth cutoff before the current coefficient field. Canonical mask
margins are transported from the physical masks, including the full diagonal.
The estimates are pointwise on the entire closed input shoulder and output
complement and hence retain every point of the actual closed total carrier.
Consumer: the protected-mask assembly for `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph ConicPhase

variable {d : ℕ}

private theorem exists_positive_lower_bound_finite_family {J : Type*} [Finite J]
    (f : J → ℝ) (hf : ∀ j, 0 < f j) : ∃ c > 0, ∀ j, c ≤ f j := by
  classical
  let := Fintype.ofFinite J
  let s := insert 1 (Finset.univ.image f)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs, ?_, fun j ↦ s.min'_le _ ?_⟩
  · apply (Finset.lt_min'_iff _ _).mpr
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · norm_num
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      exact hf j
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

/-- Assemble the literal order-two root-flow estimates using only the full
physical diagonal margin. This form applies to the SAME masks constructed
for a finite radial refinement while retaining the original phase family.
The margin is the diagonal branch of
`exists_uniform_radial_nested_localizers_and_gap`. All constants, the scalar collar cutoff and every
cutoff derivative bound precede `Q`, the flow charts and masks. Each local
coefficient norm is measured on its original physical domain; restriction
from the common original C³ budget is performed by the final assembly.
The analytic producer is `exists_uniform_fieldRoot_conicGeometry`, retaining
the SAME sum from `exists_uniform_fieldRoot_twoTimeHamiltonPhase` at order two
(`app:ch_regular:lem:finite-chain`, half-space collar argument). -/
theorem exists_uniform_finiteFamily_rootFlow_collar_of_diagonal
    {J ι : Type*} [Finite J] [Fintype ι]
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (ℓ : J → Euclidean d →L[ℝ] ℝ) (z : J → RootState (Euclidean d))
    (x₀ : J → Euclidean (d + 1)) (R₀ ρ T σ β γ B a b : J → ℝ)
    {θ M Δ : ℝ} (hθ : 0 < θ) (hM : 0 ≤ M)
    (hγ : ∀ j, 0 < γ j) (hγβ : ∀ j, γ j ≤ β j) (hγσ : ∀ j, γ j ≤ σ j)
    (hB : ∀ j, 0 ≤ B j) (ha : ∀ j, 0 < a j) :
    ∃ (ε δT : ℝ) (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ) (H : ℕ → ℝ),
      0 < ε ∧ 0 < δT ∧ (∀ j, ε ≤ γ j) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ ε / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ ε / 2} ∧
      tsupport (1 - χ) ⊆ {p | ε / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ H k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ H k) ∧
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (i : J → Fin (d + 1))
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : J → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
      (∀ j, cNorm (closedBall (x₀ j) (R₀ j)) 3 Q ≤ M) →
      (∀ j, closedBall ((z j).1, z j) (2 * β j) ⊆ (C j).target) →
      (∀ j, ContDiffOn ℝ ∞ (twoTimePhase (C j)) (C j).target) →
      (∀ j, cNorm (closedBall (z j) ((3 * ρ j) / 4) ×ˢ Icc (-T j / 4) (T j / 4)) 2 (Φ j) +
        (cNorm (closedBall ((z j).1, z j) (σ j)) 2 (twoTimeState (Φ j)) +
          cNorm (closedBall ((z j).1, z j) (σ j)) 2 (twoTimeProjection (Φ j))) +
        (cNorm (closedBall ((z j).1, z j) (2 * β j)) 2 (C j).symm +
          cNorm (closedBall ((z j).1, z j) (2 * β j)) 2 (twoTimePhase (C j))) ≤
            B j * (1 + cNorm (closedBall (x₀ j) (R₀ j)) 3 Q)) →
      (∀ j w, w ∈ ball (z j) (σ j) →
        twoTimePhase (C j) (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (mi mo : LocalizerSymbol (d + 1)),
      (∀ p ∈ cthickening θ (tsupport mi),
        closedBall p θ ⊆ interior {p | mo p = 1}) →
      ∀ (j : J) (backward : Bool) (Rf : ℝ), 0 < Rf →
      ∀ (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1))),
      r ∈ Icc 0 Δ → r ≤ ε →
      p.1.1 0 ∈ closedBall (z j).1 (γ j / 2) →
      spatialPart p.1.1 ∈ closedBall (z j).2.1 (γ j / 2) →
      spatialPart p.2.1 ∈ radialSectionBand (ℓ j) (z j).2.2 (γ j / 2) (a j) (b j) →
      (y, p.2.2.1) ∈ cthickening (θ / 2)
        (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) mi)) →
      (x, p.2.2.2) ∈ tsupport
        (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) mo q) →
      δT ≤ Localization.phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase Rf (curriedPhase (ℓ j) (C j))) x y (r, w)) p := by
  choose ε hε δ hδ hcollar using fun j ↦
    exists_uniform_rootFlow_conic_boundary_collar eT (ℓ j) (z j) (x₀ j)
      (R₀ j) (ρ j) (T j) (σ j) (β j) Δ (hγ j) (hγβ j) (hγσ j)
      hθ (ha j) (hB j) hM (b := b j)
  obtain ⟨ε₀, hε₀, hεle⟩ := exists_positive_lower_bound_finite_family
    (fun j ↦ min (ε j) (γ j)) (fun j ↦ lt_min (hε j) (hγ j))
  obtain ⟨δ₀, hδ₀, hδle⟩ := exists_positive_lower_bound_finite_family δ hδ
  obtain ⟨χ, H, hχ, hone, hsupp, hcomp, hH, hjet⟩ :=
    exists_uniform_elapsed_collar_cutoff (d := d) hε₀
  refine ⟨ε₀, δ₀, χ, H, hε₀, hδ₀,
    fun j ↦ (hεle j).trans (min_le_right _ _), hχ, hone, hsupp, hcomp, hH, hjet, ?_⟩
  intro Q i Φ C hQM htarget hs hbudget hdiag mi mo hmask
    j backward Rf hRf x y r p hr hrε ht hy hη hin hout
  apply (hδle j).trans
  apply hcollar j Q (Φ j) (C j) (hQM j) (htarget j) (hs j) (hbudget j) (hdiag j)
    (canonicalProofLocalizer (coordinateSplit (i j)) mi)
    (canonicalProofLocalizer (coordinateSplit (i j)) mo)
    (fun q hq ↦ canonicalProofLocalizer_closedBall_plateau (i j) hmask q
      (by rwa [cthickening_tsupport_canonicalProofLocalizer] at hq)) {((x, y), (r, p))} ?_ backward Rf hRf
      ((x, y), (r, p)) (mem_singleton _)
      (hrε.trans ((hεle j).trans (min_le_left _ _)))
  intro t ht'
  rcases mem_singleton_iff.mp ht' with rfl
  exact ⟨hr, ht, hy, hη, hin, hout⟩

/-- Assemble the literal order-two root-flow estimates and physical diagonal
margins for a finite family. All constants, the scalar collar cutoff and every
cutoff derivative bound precede `Q`, the flow charts and masks. Each local
coefficient norm is measured on its original physical domain; restriction
from the common original C³ budget is performed by the final assembly.
The analytic producer is `exists_uniform_fieldRoot_conicGeometry`, retaining
the SAME sum from `exists_uniform_fieldRoot_twoTimeHamiltonPhase` at order two
(`app:ch_regular:lem:finite-chain`, half-space collar argument). -/
theorem exists_uniform_finiteFamily_rootFlow_collar
    {J ι : Type*} [Finite J] [Fintype ι]
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (ℓ : J → Euclidean d →L[ℝ] ℝ) (z : J → RootState (Euclidean d))
    (x₀ : J → Euclidean (d + 1)) (R₀ ρ T σ β γ B a b : J → ℝ)
    {θ M Δ : ℝ} (hθ : 0 < θ) (hM : 0 ≤ M)
    (hγ : ∀ j, 0 < γ j) (hγβ : ∀ j, γ j ≤ β j) (hγσ : ∀ j, γ j ≤ σ j)
    (hB : ∀ j, 0 ≤ B j) (ha : ∀ j, 0 < a j) :
    ∃ (ε δT : ℝ) (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ) (H : ℕ → ℝ),
      0 < ε ∧ 0 < δT ∧ (∀ j, ε ≤ γ j) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ ε / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ ε / 2} ∧
      tsupport (1 - χ) ⊆ {p | ε / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ H k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ H k) ∧
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (C : J → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
      (∀ j, cNorm (closedBall (x₀ j) (R₀ j)) 3 Q ≤ M) →
      (∀ j, closedBall ((z j).1, z j) (2 * β j) ⊆ (C j).target) →
      (∀ j, ContDiffOn ℝ ∞ (twoTimePhase (C j)) (C j).target) →
      (∀ j, cNorm (closedBall (z j) ((3 * ρ j) / 4) ×ˢ Icc (-T j / 4) (T j / 4)) 2 (Φ j) +
        (cNorm (closedBall ((z j).1, z j) (σ j)) 2 (twoTimeState (Φ j)) +
          cNorm (closedBall ((z j).1, z j) (σ j)) 2 (twoTimeProjection (Φ j))) +
        (cNorm (closedBall ((z j).1, z j) (2 * β j)) 2 (C j).symm +
          cNorm (closedBall ((z j).1, z j) (2 * β j)) 2 (twoTimePhase (C j))) ≤
            B j * (1 + cNorm (closedBall (x₀ j) (R₀ j)) 3 Q)) →
      (∀ j w, w ∈ ball (z j) (σ j) →
        twoTimePhase (C j) (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (mi mo : LocalizerSymbol (d + 1)),
      (∀ p ∈ cthickening θ (tsupport mi), ∀ q,
        p = q ∨ physicalDirectRelation i h Φ U K W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ p q →
          closedBall q θ ⊆ interior {p | mo p = 1}) →
      ∀ (j : J) (backward : Bool) (Rf : ℝ), 0 < Rf →
      ∀ (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1))),
      r ∈ Icc 0 Δ → r ≤ ε →
      p.1.1 0 ∈ closedBall (z j).1 (γ j / 2) →
      spatialPart p.1.1 ∈ closedBall (z j).2.1 (γ j / 2) →
      spatialPart p.2.1 ∈ radialSectionBand (ℓ j) (z j).2.2 (γ j / 2) (a j) (b j) →
      (y, p.2.2.1) ∈ cthickening (θ / 2)
        (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) mi)) →
      (x, p.2.2.2) ∈ tsupport
        (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) mo q) →
      δT ≤ Localization.phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase Rf (curriedPhase (ℓ j) (C j))) x y (r, w)) p := by
  obtain ⟨ε, δT, χ, H, hε, hδT, hεγ, hχ, hone, hsupp, hcomp, hH, hjet, hgap⟩ :=
    exists_uniform_finiteFamily_rootFlow_collar_of_diagonal eT ℓ z x₀
      R₀ ρ T σ β γ B a b hθ hM hγ hγβ hγσ hB ha (Δ := Δ)
  refine ⟨ε, δT, χ, H, hε, hδT, hεγ, hχ, hone, hsupp, hcomp, hH, hjet, ?_⟩
  intro Q i h Φ U K W C hQM htarget hs hbudget hdiag mi mo hmask
  exact hgap Q i Φ C hQM htarget hs hbudget hdiag mi mo
    (fun p hp ↦ hmask p hp p (Or.inl rfl))

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
