module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Gap

/-!
# Fixed patch data for the finite frozen incidence construction

The data below contain only choices made before the immersion. The analytic
predicates are conclusions of `exists_frozen_incidence_patch`, consumed by the
finite cover construction and ultimately by
`exists_canonicalFrozenMatrixSymbol_unit_gap_of_incidence`
(`app:ch_background:prop:bg-frame`, `app:ch_seed:eq:seed-actual-detection`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

/-- Fixed radii, minor and reference inverse for a single patch in the finite
incidence cover. No current root, inverse estimate or detection assertion is a
field (`app:ch_background:prop:bg-frame`). -/
structure FrozenIncidencePatchData {n : ℕ} {P : Patch n} {U : Set (Euclidean n)}
    {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) where
  r : ℝ
  a : ℝ
  frequencyRadius : ℝ
  rootTolerance : ℝ
  frameThreshold : ℝ
  inverseRadius : ℝ
  cJ : ℝ
  V : Set (ℝ × Euclidean (n - 1))
  L : Set (ℝ × Euclidean (n - 1))
  G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))
  row : Fin n
  col : Fin n
  hr : 0 < r
  ha : 0 < a
  hηb : ηb ≠ 0
  frequencyRadius_pos : 0 < frequencyRadius
  rootTolerance_pos : 0 < rootTolerance
  frameThreshold_pos : 0 < frameThreshold
  inverseRadius_pos : 0 < inverseRadius
  hcJ : 0 < cJ
  hV : IsOpen V
  hVc : IsCompact (closure V)
  hLc : IsCompact L
  hLV : L ⊆ V
  har : 6 * a ≤ r
  haR : 6 * a < T.family.radius
  hphys : 3 * r < T.family.radius / 8
  hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
    carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU} {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}

/-- The exact local geometry required by `Spectral.FiniteFamily`, with the
original conic and spectator balls. It is proved from the immersion by the
patch constructor (`app:ch_background:eq:bg-Psi`, `bg-jacobian`). -/
def FrozenIncidencePatchData.Geometry (d : FrozenIncidencePatchData T z₀ ηb)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
    (physicalParameterSet z₀ (6 * d.a) ×ˢ dataSet z₀ ηb (3 * d.r)) ∧
  (∀ p ∈ physicalParameterSet z₀ (6 * d.a), ∀ u ∈ dataBox z₀ ηb (2 * d.r),
    ‖(d.G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
      (fderiv ℝ (adaptedTransportChart T Q p) u) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
  BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * d.a))
    (dataBox z₀ ηb d.r) (dataSet z₀ ηb (2 * d.r)) (dataBox z₀ ηb (2 * d.r))
    d.V d.L d.inverseRadius d.cJ d.G ∧
  (∀ p ∈ physicalParameterSet z₀ (6 * d.a),
    ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) d.r (angularWidth ηb d.r),
      ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb d.r / 4) * ‖u.2‖)

/-- The literal root-domain identity and positive input weights, including
allowed initial multipliers. This conclusion directly supplies `Gap.hroot`
when the multiplier is one (`app:ch_background:prop:bg-frame`). -/
def FrozenIncidencePatchData.RootAt (d : FrozenIncidencePatchData T z₀ ηb)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (k : Euclidean n) (z : Euclidean 3) : Prop :=
  let out := ((0, 0, k), spectatorCenter z₀)
  let u := frozenSymbolInverse T Q z₀ ηb d.r (6 * d.a)
  out ∈ frozenSymbolDomain T Q z₀ ηb d.r (6 * d.a) ∧
  parameter ((u out).1, out.2) = z ∧
  ∀ (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
    1 / 2 ≤ initial (Y (0, (0, z))) →
    0 < inputWeight
      (uncutFrozenCoefficients T Q F d.row d.col Φ Y initial
        (angularMask z₀ (NormedSpace.normalize ηb) d.ha (angularWidth_spec d.hηb d.hr).1)
        FixedCutoffs.highFrequency)
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0))
      (inverseCoordinates u out)

end JanetCartan.ContinuumNormal.FrozenModel
