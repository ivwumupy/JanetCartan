module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.Normalized
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Assembly.CompactJets

/-!
# Conic matrix budgets on the actual buffered section

Use the same compact radial band and both-time box as the phase construction.
Their normalization inclusion is proved by `bufferedJetSet_normalizes`, so
this endpoint has no assumed section-image containment. Consumer:
`app:ch_regular_base:lem:retarded-kernel` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicAmplitude
open AmplitudeBounds
open EvolutionIntegral.SymbolBudgets hiding TwoTimePoint
variable {d n : ℕ}

/-- The actual compact radial band of the phase also supplies the matrix
symbol bound, uniformly over every later shell radius. All image/positivity
premises are discharged geometrically, and the constant precedes the local
matrix (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_buffered_symbol_bound (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    {z : RootState (Euclidean d)} {ε a b : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    {U : Set (TwoTimePoint (Euclidean d))} (hU : IsOpen U)
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ U) (m : ℕ) :
    ∃ A > (0 : ℝ), ∀ f : TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ f U →
      BoundedTwoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z ε a b) m
        (curryCharacteristicMatrix (extend ℓ o f)) ∧
      twoTimeOrderSeminorm o (ConicPhase.bufferedJetSet ℓ z ε a b) m
        (curryCharacteristicMatrix (extend ℓ o f)) ≤
          A * cNorm (closedBall (z.1, z) (2 * ε)) m f := by
  refine ⟨symbolBoundConstant (n := n) ℓ o (ConicPhase.bufferedJetSet ℓ z ε a b) m,
    symbolBoundConstant_pos _ _ _ _, fun f hf ↦
      ⟨boundedTwoTimeOrderSeminorm_curry_extend _ _ _ _ _, ?_⟩⟩
  exact twoTimeOrderSeminorm_curry_extend_le ℓ o
    (ConicPhase.isCompact_bufferedJetSet ℓ z ε a b) (isCompact_closedBall _ _)
    hU hbuffer (ConicPhase.bufferedJetSet_normalizes ℓ hε ha).1
    (ConicPhase.bufferedJetSet_normalizes ℓ hε ha).2 hf m

end JanetCartan.RegularSector.Characteristic.ConicAmplitude
