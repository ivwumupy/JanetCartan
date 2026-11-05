module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedCharts
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.Weights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedBuffers

/-!
# Literal normalized actions with the original density weights

Retain the density at the actual inverse ODE label when identifying the
source carrier with the normalized seed. This is the action-level connection
between the bounded density carriers and the measured normalized adjoints.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal.FrozenModel ContinuumNormal.SourceDensityLimitRealization
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference
open PositiveReference.FlowConstruction NullTransport ActualFlow FlowAmplitude

/-- On the original supported cylinder, every initial multiplier is evaluated
at the SAME current inverse ODE label. The resulting weighted normalized seed
has exactly the current carrier's kernel, forward test integral and adjoint
integral. In particular this retains `sqrt (1 + v)` without freezing its label
or changing the original scalar class. Consumer:
`exists_finite_seed_source_density_carriers` and the measured row's literal
adjoint uniqueness (`app:ch_background:eq:bg-T`, `bg-Nsigma`,
`app:ch_background:prop:bg-normalized`). -/
theorem retained_chart_weighted_normalized_kernel_and_integrals
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc B τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (hsupport : ∀ (x : Torus n) (z : CarrierParameter) (η : Euclidean (n - 1)),
      FixedCutoffs.periodic hr hcell 1 x ≠ 0 → angular z η ≠ 0 →
      densityCoordinates T (AmplitudeBound.centeredTorusRepresentative x, z) ∈
        Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), zCell) (Rc / 32))
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (current : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc B τ row col (sourceDilation F σ))
    (weight : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    let d := data T current.Q (sourceDilation F σ) row col current.forward current.inverse
      (fun q ↦ σ * weight q) hr hcell angular high
    let e := weightNormal
      (normalizedCarrierData T seed.Q F row col seed.forward seed.inverse
        (fun _ ↦ 1) hr hcell angular high σ)
      (fun p ↦ weight (densityFootpoint T current.inverse p))
    carrierKernel d = carrierKernel e ∧
      carrierTestIntegral d = carrierTestIntegral e ∧
      carrierAdjointIntegral d = carrierAdjointIntegral e := by
  intro d e
  obtain ⟨_, _, _, hweight⟩ := retained_chart_normalized_kernel_and_integrals
    T hP hΩ hKΩ hpatch hRc hτ hτR hbuffer hF hrank hphysical seed htrans hflat
    hr hcell angular high hsupport hσ hσ1 current
  have he : carrierKernel d = carrierKernel e := by
    funext x u
    exact (hweight weight x u).trans (carrierKernel_weightNormal
      (normalizedCarrierData T seed.Q F row col seed.forward seed.inverse
        (fun _ ↦ 1) hr hcell angular high σ)
      (fun p ↦ weight (densityFootpoint T current.inverse p)) x u).symm
  refine ⟨he, ?_, ?_⟩
  · funext f x
    simp only [carrierTestIntegral, he]
  · funext w u
    simp only [carrierAdjointIntegral, he]

end JanetCartan.ContinuumRow.NormalizedSelection
