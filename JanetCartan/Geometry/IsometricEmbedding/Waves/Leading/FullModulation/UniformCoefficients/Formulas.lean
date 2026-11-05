module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Inputs

/-!
# Exact finite-formula identifications for the full coefficients

These identities let the smoothness and norm proofs use the published algebra
without unfolding the Hamilton construction (`app:ch_waves:eq:joint-tame`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation.UniformCoefficients
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport.CoefficientBounds

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The full null column is the existing polynomial formula
(`app:ch_waves:thm:leading`). -/
theorem nullvector_eq_formula (c : Fin n) :
    nullvector T Q c = right c ∘ fullInput T Q := rfl

/-- The full cofactor row is the existing polynomial formula
(`app:ch_waves:thm:leading`). -/
theorem conullvector_eq_formula (r : Fin n) :
    conullvector T Q r = left r ∘ fullInput T Q := rfl

/-- The original adapted denominator is the same finite formula
(`app:ch_waves:thm:leading`). -/
theorem adaptedDenominator_eq_formula (r c : Fin n) :
    adaptedDenominator T Q r c = denominator T.data.adapted.normal r c ∘ fullInput T Q := rfl

/-- The normalized full direction is the same finite formula
(`app:ch_waves:thm:leading`). -/
theorem transportDirection_eq_formula (r c : Fin n) :
    transportDirection T Q r c = direction T.data.adapted.normal r c ∘ fullInput T Q := rfl

end JanetCartan.LeadingWave.FullModulation.UniformCoefficients
