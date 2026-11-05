module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets

/-!
# Uniform normal symbols before the conic chart

The quantitative density estimate already chooses its constant before the chart.
Keep that order of choices through the spectator integral and the physical-to-cycles
Fourier normalization. The consumer is the uniform modified-adjoint estimate for
`app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
open ContinuumRow DerivativeKernels DerivativeKernels.ModifiedNormalSymbol FourierIntegral
variable {n : ℕ}

/-- The scalar normal's PDO constant depends only on the fixed geometry budgets,
spectator support, regularizer budget and measurement box. In particular it is
chosen before the conic chart, its rescaling, and the amplitude. This is the normal
symbol input to the uniform scalar-transport endpoint of
`app:ch_background:prop:bg-adjoint`, with the unchanged reserve `2*(n+1)`.
The primitive regularity, support and weighted jet hypotheses are retained. -/
theorem exists_uniform_graphNormalAmplitudeBounds
    (B c : ℝ) (hc : 0 < c) (K : Set (Euclidean 2)) (M R : ℝ) :
    ∃ C ≥ 0, ∀ {g : Chart n} {σ : JetRescaling g} {ρ : ℝ}
      {J : Set (JointVariables n)} {X : Set (Euclidean n)}
      {Z : Set CarrierParameter} {Ω : Set (Euclidean (n-1))},
      PrimitiveJetGeometry g σ (2*(n+1)) ρ B c J K →
      (∀ x ∈ X, ∀ i, |x i| ≤ R) →
      ∀ (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (A : ℝ),
        PrimitiveRegularity g a m →
        PrimitiveAmplitudeReserve g (2*(n+1)) ρ A X K Z Ω J a →
        PrimitiveRegularizerReserve (2*(n+1)) ρ M m →
        GraphNormalAmplitudeBounds (matrixAmplitude g a m) R (C * A^2) := by
  obtain ⟨D, hD, hd⟩ := exists_inverseDensity_joint_jet_bound (n := n) (2*(n+1)) B hc
  refine ⟨graphJetFactor n K * (D * M^2),
    mul_nonneg (graphJetFactor_nonneg K) (mul_nonneg hD (sq_nonneg M)), ?_⟩
  intro g σ ρ J X Z Ω hg hX a m A h ha hm
  have hsection : ∀ j ≤ 2*(n+1), ∀ p : Variables n, ∀ v ∈ K,
      ‖iteratedFDeriv ℝ j (fun q ↦ inverseDensity g a m (q, v)) p‖ ≤
        (D * M^2) * A^2 := by
    intro j hj p v hv
    exact norm_iteratedFDeriv_inverseDensity_section_le h ha.buffered (by positivity)
      (fun q _ hqK ↦ hd hg a m A M h ha hm j hj q hqK) p v hv
  simpa only [mul_assoc] using
    graphNormalAmplitudeBounds_of_densityJets h ha.buffered ha.compact_supports
      (mul_nonneg (mul_nonneg hD (sq_nonneg M)) (sq_nonneg A)) hX hsection

end JanetCartan.ContinuumAdjoint.Canonical.UniformEndpoint
