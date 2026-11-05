module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.Detection

/-!
# Annihilation with the literal density's analytic obligations discharged

The unit-initial frozen carrier in `app:ch_background:prop:bg-frame` has
primitive coefficient regularity and Bochner integrability by construction.
This instantiates the analytic inputs of the incidence deduction. Root domain,
root identity and weight positivity are the geometric conclusions of
`exists_constructed_incidence_positive_weights`; the finite spectral assembly
must instantiate them at the same selected roots.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
      (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hcJ : 0 < cJ) (hV : IsOpen V) (hLV : L ⊆ V)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha
  (And.left (angularWidth_spec hηb hr))
local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
  angular₀ FixedCutoffs.highFrequency
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)
local notation "S₀" => closedBall (spectatorCenter z₀) (a / 2)

include hP hηb hr har hcarrier hf hInv htrans hcJ hV hLV

/-- Zero energy of the actual unit-amplitude frozen carrier annihilates its
actual root detector. Integrability and primitive coefficient regularity are
proved here, with the original masks, inverse, reflection and Lebesgue measure.
The remaining root inputs are produced by
`exists_constructed_incidence_positive_weights`
(`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`). -/
theorem canonicalFrozenCarrierSymbol_unit_detector_eq_zero
    {k : Euclidean n} {z : Euclidean 3}
    (hp : ((0, 0, k), spectatorCenter z₀) ∈ Ω₀)
    (hz : parameter ((u₀ ((0, 0, k), spectatorCenter z₀)).1, spectatorCenter z₀) = z)
    (hw : 0 < inputWeight a₀ J₀ (inverseCoordinates u₀ ((0, 0, k), spectatorCenter z₀)))
    (s : Euclidean n)
    (hzero : dotProduct (fun i ↦ s i)
      (canonicalFrozenCarrierSymbol T Q F row col Φ Y (fun _ ↦ 1) z₀ hηb hr ha
        k *ᵥ (fun i ↦ s i)) = 0) :
    ⟪quadratic (Q.1 0) (T.carrierGradient Q 0 z), s⟫_ℝ = 0 := by
  exact canonicalFrozenCarrierSymbol_detector_eq_zero T Q F row col Φ Y (fun _ ↦ 1)
    z₀ hηb hr ha hInv htrans hV hLV
    (frozenPrimitiveRegularity_unit T Q hP hηb hr ha har hcarrier hf hInv htrans hcJ
      F row col Φ Y)
    (frozenExtendedDensity_unit_integrable T Q F row col Φ Y hP hηb hr ha har hcarrier
      hf hInv htrans hcJ hV hLV (0, 0, k)) hp hz hw s hzero

end JanetCartan.ContinuumNormal.FrozenModel
