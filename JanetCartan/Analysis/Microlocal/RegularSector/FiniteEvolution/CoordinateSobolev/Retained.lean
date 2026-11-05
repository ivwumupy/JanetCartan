module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev.Estimates

/-!
# Applying coordinate transport to the existing retained chart bounds

`hT` below is the output of
`PhysicalOperators.exists_selected_chart_physical_operators`, through
`SelectedChartEvolutionAt`, and of `PhysicalCutoff` before chart instantiation.
No new analytic premise or replacement record is introduced. The physical
solver and complete residual consume these estimates; selecting and summing
the actual charts remains with their parent construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteEvolution
open FourierIntegral Characteristic.EvolutionIntegral Characteristic.UniformEvolution Pseudodifferential
variable {d q : ℕ}
local notation "Dom" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q
local notation "Mat" => MetricTensor (d+1)

/-- The actual producer's positive and negative bounds transfer with the
original coefficient profile and fixed reserve, for both orientations.
For `o=0` this is the retarded solver; for `o=1` it is the `PW₁` residual.
Sources: `sector-theorem-solution`, `sector-theorem-residual`,
`measured-adjoint`, and `energy-complete-residual`. -/
theorem physicalOperator_retained_signed_bounds
    (i : Fin (d+1)) (KQ : Set Dom) (Q : Dom → Fin (d+1) → Mat) (B : Dom → Mat)
    (Δ a₀ : ℝ) (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q)
    (χout χsource β : Dom → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (o : ℕ) (A₀ : ℝ) (A : ℕ → ℝ) (T : H →L[ℂ] H)
    (hT : RetainedSignedRetardedBounds KQ Q B Δ a₀ Ψ W χout χsource β hs o A₀ A T) :
    (∀ s : ℕ, ∀ V : H →L[ℂ] H,
      (V = physicalOperator i T ∨ V = (physicalOperator i T).adjoint) → ∀ u,
      MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ A s *
        (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u +
          retardedCoefficientProfile KQ Q B (s+(FullLowBounds.fullLowReserve (d+1)+2)) * ‖u‖)) ∧
    (∀ k : ℕ, ∀ V : H →L[ℂ] H,
      (V = physicalOperator i T ∨ V = (physicalOperator i T).adjoint) → ∀ u,
      MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
      vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤ A (k+o) *
        retardedCoefficientProfile KQ Q B (k+o+(FullLowBounds.fullLowReserve (d+1)+2)) *
        vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u) := by
  exact ⟨physicalOperator_positive_integer_bounds i T o _ A
    (retardedCoefficientProfile KQ Q B) hT.2.2.2.1,
    physicalOperator_negative_integer_bounds i T o _ A
      (retardedCoefficientProfile KQ Q B) hT.2.2.2.2.1⟩

/-- Specializing the actual gain-one producer at negative input order one
gives the physical H⁻¹ → L² endpoint on L² inputs (`finite-gap-theorem`). -/
theorem physicalOperator_retained_HminusOne_to_L2
    (i : Fin (d+1)) (KQ : Set Dom) (Q : Dom → Fin (d+1) → Mat) (B : Dom → Mat)
    (Δ a₀ : ℝ) (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q)
    (χout χsource β : Dom → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (A₀ : ℝ) (A : ℕ → ℝ) (T : H →L[ℂ] H)
    (hT : RetainedSignedRetardedBounds KQ Q B Δ a₀ Ψ W χout χsource β hs 1 A₀ A T)
    (V : H →L[ℂ] H)
    (hV : V = physicalOperator i T ∨ V = (physicalOperator i T).adjoint) (u : H) :
    ‖V u‖ ≤ A 1 * retardedCoefficientProfile KQ Q B
      (1+(FullLowBounds.fullLowReserve (d+1)+2)) * vectorFourierSobolevNorm (-1) u := by
  have h := (physicalOperator_retained_signed_bounds i KQ Q B Δ a₀ Ψ W
    χout χsource β hs 1 A₀ A T hT).2 0 V hV u
  simpa only [Nat.cast_zero, neg_zero, zero_add, Nat.cast_one,
    vectorFourierSobolevNorm_zero] using h.2

end JanetCartan.RegularSector.FiniteEvolution
