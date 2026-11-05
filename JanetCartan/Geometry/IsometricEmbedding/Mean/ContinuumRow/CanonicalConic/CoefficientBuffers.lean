module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.CoefficientBuffers.FiniteDomains
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.CoefficientBuffers.Jacobian

/-!
# Canonical coefficient buffers for the supported carrier constructor

The input center, outer conic chart, smaller masks and actual Jacobian are
those of `exists_actual_refined_supported_geometry`. An arbitrary open
coefficient region fixes a cap before that construction selects its input
radius. Every resulting input ball has finite input and coefficient buffers,
a buffered time interval, the existing primitive norm charts, and positive
frequency and determinant lower bounds, all chosen before `Q`.

The consumer is
`CarrierNormalRealization.exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.
`CanonicalCarrier.exists_canonical_primitive_controls` supplies the primitive
norms on this same field chart. The parent retains the concrete flow-domain
instantiation, refined kernel adapter, and final supported-constructor application.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Finite coefficient geometry for the SAME canonical input ball and smaller
physical/angular masks. The cap precedes the actual choice of `ρ`; every domain,
chart and lower constant precedes `Q`. The analytic premises are precisely the
outer smoothness, buffered inverse and transverse comparison supplied by
`exists_actual_refined_supported_geometry`. The final parent instantiates them
with its retained projected-stress geometry and flow.

Consumer: `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.
Sources: `app:ch_background:eq:bg-Psi`, `bg-jacobian`, `bg-mixed-input`, and
`bg-full-complex-amplitude`. -/
theorem exists_canonical_coefficient_buffers {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ E) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    ∃ cap > (0 : ℝ), ∀ {r a ρ : ℝ}, 0 < r → 0 < ρ → ρ < cap →
      closedBall p₀ ρ ⊆ symbolInputDomain z₀ ηb r (6 * a) →
      ∃ (W K : Set (InputVariables n))
        (Vphase Lphase : Set (Euclidean n × CarrierParameter))
        (I : Set ℝ) (D : CoefficientNormCharts n) (ε : ℝ),
        IsOpen W ∧ IsCompact K ∧ closedBall p₀ ρ ⊆ W ∧ W ⊆ K ∧
        K ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧
        IsOpen Vphase ∧ IsCompact Lphase ∧ Lphase ⊆ Vphase ∧
        IsOpen I ∧ (∃ l u : ℝ, I = Ioo l u) ∧ Icc (0 : ℝ) 1 ⊆ I ∧
        (∀ t ∈ I, MapsTo (transportSegmentInput n t) W Vphase) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W Lphase) ∧
        D.field.carrier = Lphase ∧ D.field.region = Vphase ∧
        Vphase ⊆ E ∩ coefficientDomain z₀ r (6 * a) ∧
        (∀ p ∈ closedBall p₀ ρ, D.Contains p) ∧
        (∀ {a' : ℝ} (ha' : 0 < a'), 4 * a' < ρ →
          tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
            carrierSupport z₀ (r := a') ⊆ D.field.carrier) ∧
        0 < ε ∧ (∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖) ∧
        ∀ {cJ : ℝ}, 0 < cJ → ∃ δ > (0 : ℝ),
        ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
          ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
            (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) →
          ∀ {b : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
            {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))},
          BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
            (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G →
          (∀ p ∈ physicalParameterSet z₀ (6 * a),
            ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
              ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
          EqOn (symbolJacobian T Q)
            (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)) W ∧
          (∀ p ∈ W, symbolJacobian T Q p ≠ 0) ∧
          (∀ p ∈ closedBall p₀ ρ, δ ≤
            transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) p) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨cap, hcap, hbuffers⟩ := exists_coefficient_buffers_cap z₀ ηb hηb E hE hcenter
  refine ⟨cap, hcap, ?_⟩
  intro r a ρ hr hρ hρcap hinput
  obtain ⟨W, K, Vphase, Lphase, I, D, ε, hW, hK, hball, hWK, hKdom,
    hV, hL, hLV, hI, hinterval, hIT, hsegT, hseg, hDcar, hDreg, hDom, hfoot,
    hsupport, hε, hη⟩ := hbuffers hρ hρcap hinput
  refine ⟨W, K, Vphase, Lphase, I, D, ε, hW, hK, hball, hWK, hKdom,
    hV, hL, hLV, hI, hinterval, hIT, hsegT, hseg, hDcar, hDreg, hDom, hfoot,
    hsupport, hε, hη, ?_⟩
  intro cJ hcJ
  exact exists_fixed_coefficient_jacobian_lower_bound T hηb hr hcJ hε
    hball (hWK.trans hKdom) hη

end JanetCartan.ContinuumRow.CanonicalConic
