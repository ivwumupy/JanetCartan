module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.BoundaryGap.Conic

/-!
# The common collar from the actual root-flow budget

This is the quantitative boundary input for the coefficient-uniform protected
mask assembly. It consumes the literal order-two sum returned by
`UniformGeometry.exists_uniform_fieldRoot_twoTimeHamiltonPhase`, or the same
retained sum in `exists_uniform_fieldRoot_conicGeometry`. The original C³
bound, target buffer, smaller conic radius and mask margin fix the collar
before `Q`. The full actual total carrier and its original elapsed interval
are parameters of the result, not replaced by a smaller operator.

The parent instantiates the same constructed chart, physical-to-canonical
mask margin, fixed radial bands and carrier restrictions. Smooth scalar
cutoff assembly and transfer to any supported smooth representative are
left to that parent. Source: `app:ch_regular:lem:finite-chain`, half-space
collar argument, and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph ConicPhase

variable {d : ℕ}

/-- A common positive squared tangential gap on the full retained carrier
inside a common elapsed collar, from the actual constructor's C² estimate
and the original C³ coefficient budget. The carrier retains `Icc 0 Δ`, all
three covectors, the entire `cthickening (θ/2)` input shoulder and the full
`tsupport (1-mo)` output complement. There is no characteristic-energy
restriction at the boundary (`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_rootFlow_conic_boundary_collar
    {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    (x₀ : Euclidean (d + 1)) (R₀ ρ T σ β Δ : ℝ)
    {γ θ a b B M : ℝ} (hγ : 0 < γ) (hγβ : γ ≤ β) (hγσ : γ ≤ σ)
    (hθ : 0 < θ) (ha : 0 < a) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
      cNorm (closedBall x₀ R₀) 3 Q ≤ M →
      closedBall (z.1, z) (2 * β) ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (cNorm (closedBall z ((3 * ρ) / 4) ×ˢ Icc (-T / 4) (T / 4)) 2 Φ +
        (cNorm (closedBall (z.1, z) σ) 2 (twoTimeState Φ) +
          cNorm (closedBall (z.1, z) σ) 2 (twoTimeProjection Φ)) +
        (cNorm (closedBall (z.1, z) (2 * β)) 2 C.symm +
          cNorm (closedBall (z.1, z) (2 * β)) 2 (twoTimePhase C)) ≤
            B * (1 + cNorm (closedBall x₀ R₀) 3 Q)) →
      (∀ w ∈ ball z σ, twoTimePhase C (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (mi mo : LocalizerSymbol (d + 1)),
      (∀ q ∈ cthickening θ (tsupport mi), closedBall q θ ⊆ interior {q | mo q = 1}) →
      ∀ (K : Set ((Euclidean (d + 1) × Euclidean (d + 1)) ×
          (ℝ × JointVariables (Euclidean (d + 1))))),
      (∀ t ∈ K,
        t.2.1 ∈ Icc 0 Δ ∧
        t.2.2.1.1 0 ∈ closedBall z.1 (γ / 2) ∧
        spatialPart t.2.2.1.1 ∈ closedBall z.2.1 (γ / 2) ∧
        spatialPart t.2.2.2.1 ∈ radialSectionBand ℓ z.2.2 (γ / 2) a b ∧
        (t.1.2, t.2.2.2.2.1) ∈ cthickening (θ / 2) (tsupport mi) ∧
        (t.1.1, t.2.2.2.2.2) ∈ tsupport (fun q ↦ 1 - mo q)) →
      ∀ (backward : Bool) (R : ℝ), 0 < R → ∀ t ∈ K, t.2.1 ≤ ε →
        δ ≤ Localization.phaseGradientSquare e (fun w ↦ jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase R (curriedPhase ℓ C))
          t.1.1 t.1.2 (t.2.1, w)) t.2.2 := by
  obtain ⟨ε, hε, δ, hδ, hcollar⟩ := exists_uniform_normalizedConic_boundary_collar
    e ℓ z hγ hγσ hθ ha (mul_nonneg hB (by positivity : 0 ≤ 1 + M)) (b := b)
  refine ⟨ε, hε, δ, hδ, ?_⟩
  intro Q Φ C hQM hbuffer hs hbudget hdiag mi mo hmask K hK backward R hR t ht hr
  have hphase := twoTimePhase_secondJet_budget_of_rootFlow z ρ T σ β Φ C x₀ R₀ Q hB hQM hbudget
  have hphase' := twoTimePhase_secondJet_budget_restrict z hγβ C hbuffer hs hphase
  have hbuffer' : closedBall (z.1, z) (2 * γ) ⊆ C.target :=
    (closedBall_subset_closedBall (by linarith)).trans hbuffer
  have hdiag' : ∀ w ∈ ball z.1 σ ×ˢ ball z.2 σ,
      twoTimePhase C (w.1, w) = inner ℝ w.2.1 w.2.2 := by
    intro w hw
    exact hdiag w (by simpa only [mem_ball, Prod.dist_eq, max_lt_iff, mem_prod] using hw)
  obtain ⟨htime, htbase, hybase, hη, hin, hout⟩ := hK t ht
  exact hcollar C hbuffer' hs hphase' hdiag' mi mo hmask backward t.1.1 t.1.2 t.2.2 R hR
    htbase hybase hη hin hout t.2.1 htime.1 hr

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
