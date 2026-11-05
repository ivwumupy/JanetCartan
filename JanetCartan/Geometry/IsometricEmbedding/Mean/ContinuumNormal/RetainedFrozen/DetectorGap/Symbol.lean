module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CanonicalData

/-!
# Literal frozen symbols on retained masks

These expressions retain the `RetainedAdjointRow` inner mask and spectator
radius and its distinct outer inverse radii. The consumer is the same-row
spectral estimate in `app:ch_background:prop:bg-frame`, Step 2.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} (r a : ℝ) {r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr' : 0 < r') (ha' : 0 < a')

/-- The literal reflected symbol for the retained row; the inverse uses
`r, 6*a`, the mask uses `r', a'`, and the Lebesgue spectator set has radius
`a'/2` (`app:ch_background:eq:bg-real-symbol`). -/
abbrev retainedFrozenCarrierSymbol (k : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  frozenCarrierSymbol T Q F row col Φ Y initial
    (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
    FixedCutoffs.highFrequency (adaptedSliceCoordinates T)
    (frozenSymbolInverse T Q z₀ ηb r (6 * a))
    (frozenSymbolDomain T Q z₀ ηb r (6 * a))
    (closedBall (spectatorCenter z₀) (a' / 2)) k

/-- Pointwise positive semidefiniteness preserves both reflections and their
factor four, before any integral regularity deduction (`bg-real-symbol`). -/
theorem retainedFrozenCarrierSymbol_posSemidef (k : Euclidean n) :
    (retainedFrozenCarrierSymbol T Q F row col Φ Y initial z₀ r a hηb hr' ha' k).PosSemidef :=
  frozenCarrierSymbol_posSemidef ..

end JanetCartan.ContinuumNormal.RetainedFrozen
