module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedSupport

/-!
# Primitive regularity on the retained outer cone

The inner angular mask is smooth independently of the inverse radii. The
normal and detector use the existing seed formulas on the outer carrier
buffer; the Jacobian uses the retained buffered inverse. This supplies
`retainedFrozenExtendedDensity_unit_contDiff` and the zero-energy deduction
in `app:ch_background:prop:bg-frame`, Step 2.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : P.IsValid c C)
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har : 6 * a ≤ 3 * r)
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

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) ha'
  (And.left (angularWidth_spec hηb hr'))
local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
  angular₀ FixedCutoffs.highFrequency
local notation "J₀" => transportAbsoluteJacobian (adaptedSliceCoordinates T)
  (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r (6 * a)
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r (6 * a)
local notation "S₀" => closedBall (spectatorCenter z₀) (a' / 2)

include hP hηb hr har hcarrier hf hInv htrans hcJ

/-- All fields of the existing primitive regularity interface are proved
for the literal unit-initial frozen coefficients (`new:lem:scaling`). -/
theorem retainedFrozenPrimitiveRegularity_unit :
    PrimitiveRegularity
      (uncutFrozenCoefficients T Q F row col Φ Y (fun _ ↦ 1)
        (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency) J₀ (frozenInputDomain z₀ ηb r (6 * a)) := by
  have hm := frozenInputDomain_carrier_subset (ηb := ηb) hP hr har hcarrier
  have hn := (frozenSeedNormal_unit_smooth T Q F row col Φ Y hP).comp
    contDiffOn_snd.fst hm
  have hq := (PiLp.contDiff_ofLp.comp_contDiffOn (frozenSeedDetector_smooth T Q hP)).comp
    contDiffOn_snd.fst hm
  exact ⟨contDiffOn_const, contDiffOn_const,
    angularMask_smooth z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1,
    FixedCutoffs.highFrequency_smooth, hn, hn,
    contDiffOn_pi.mp hq, contDiffOn_pi.mp hq,
    frozenJacobian_smooth T Q hP hηb hr har hcarrier hInv htrans hf hcJ,
    fun _ hp ↦ (frozenJacobian_pos T Q hP hηb hr har hcarrier hInv htrans hf hcJ hp).ne',
    fun _ hp ↦ hp.2.2.1⟩


end JanetCartan.ContinuumNormal.RetainedFrozen
