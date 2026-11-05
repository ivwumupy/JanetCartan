module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedWeightBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedSource

/-!
# The literal physical source on retained full-weight buffers

Apply the normalized mean-source construction on the original finite family.
The full-support flow buffer supplies both seed and current domain maps, with
one cap before the measurement radius, current chart family and source scale. The retained chart's physical
mean is identified definitionally with the mean used by `RetainedSource`.
Consequently the all-order bound is for the exact `fixedSourceToL2` supplied to
`SourceInverse`, with the original squared external weights and product measure.

The current charts, common seed and finite cells are still inputs from the
retained normalized-family producers. This closes their source-bound deduction;
it does not construct the uniform bounded row, gap, raw adjoint or inverse.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PositiveBackground
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction ContinuumRow CanonicalCarrier LeadingPrimitive
open NormalizedBackground NormalizedBackground.SourceGeometry HamiltonPhase
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
open ProjectedStressFrame UniformStep.Periodization RetainedAssembly.ExternalWeights
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- One full-weight buffer supplies the literal physical mean's residual and
fixed Sobolev source for EVERY smaller measurement radius and supplied current
chart family. The initializer can choose its radius below this cap at the
original selection point. For each such fixed radius, the positive source cap,
normal-field lower bound and all graded constants precede the varying scale. The seed/current flow-domain
premises of `exists_retained_fixedSource_sobolev_bounds` are discharged by the
original comparison and working-cylinder geometry. Both physical means retain
the SAME external weights, measure, retained maps and initial scalars
(`app:ch_background:eq:bg-Hsigma`, `app:ch_background:eq:bg-affine-mean`,
`app:ch_background:eq:bg-current-raising`, `app:ch_background:prop:bg-normalized`).

Consumer: `SourceInverse.exists_small_uncorrectedDensity_of_normal_estimates_with_exterior`,
whose `hQ`, `hR` and `hsource` are supplied here after restricting to `σ₀`.
Producers of the remaining geometric inputs are the original finite retained
selection and normalized chart family. No mean-error bound, normal lower bound,
source estimate or inverse estimate is assumed. -/
theorem exists_retained_weight_physical_source_bounds
    {n : ℕ} (hn : 5 ≤ n) {A : Type} [Fintype A] (G : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U} (h0U : (0 : Euclidean n) ∈ U)
    (hUG : U ⊆ G.domain.chart n)
    {P : A → Patch n} {cP CP : ℝ} (hP : ∀ a, (P a).IsValid cP CP)
    (T : (a : A) → PatchQuantitativeFamily (P a) U hU)
    {Ω : A → Set (Euclidean n × Euclidean 3)} (hΩ : ∀ a, IsOpen (Ω a))
    {z₀ : A → Euclidean 3} {ρ Rc M τ L rcomp δcomp σcover τfull : A → ℝ}
    {row col : A → Fin n}
    (hKΩ : ∀ a, closedBall ((0 : Euclidean n), z₀ a) (ρ a) ⊆ Ω a)
    (hpatch : ∀ a, Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius))
    (hL : ∀ a, 0 < L a) (hRc : ∀ a, 0 < Rc a) (hτ : ∀ a, 0 < τ a)
    (hτR : ∀ a, τ a ≤ Rc a / 16)
    (hbuffer : ∀ a, MapsTo (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀ a)) (Rc a))
      (closedBall ((0 : Euclidean n), z₀ a) (ρ a)))
    (hphysical : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ U)
    (seed : (a : A) → Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
      ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a) G.map)
    (htrans : ∀ a, ∀ q ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU (seed a).Q.1 (seed a).Q.2.1).hp q,
        (T a).data.adapted.normal⟫_ℝ ≠ 0)
    (hσcover : ∀ a, 0 < σcover a)
    (hcompRadius : ∀ a, 8 * rcomp a ≤ Rc a / 32)
    (E : A → Set (Euclidean n × CarrierParameter)) (hE : ∀ a, IsOpen (E a))
    (hcomp : ∀ a, MapsTo (densityCoordinates (T a)) (E a)
      (Ioo (-δcomp a) (δcomp a) ×ˢ
        ball ((0 : Euclidean (n - 1)), z₀ a) (rcomp a)))
    (hgraph : ∀ a, MapsTo (carrierGraph (T a)) (E a)
      (ball ((0 : Euclidean n), (z₀ a, (T a).reference.spatialPatch (z₀ a))) (σcover a)))
    (hworking : ∀ a,
      closedBall ((0 : Euclidean n), (z₀ a, (T a).reference.spatialPatch (z₀ a)))
        (2 * σcover a) ⊆
      (coordinates (adaptedCoordinates (T a).data.adapted)).symm ''
        (Icc (-τfull a / 2) (τfull a / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)),
            (z₀ a, (T a).reference.spatialPatch (z₀ a))) (L a / 64)))
    (χ : A → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχcompact : ∀ a, HasCompactSupport (χ a))
    (hχE : ∀ a, tsupport (χ a) ⊆ carrierNeighborhood (E a))
    (angular : A → CarrierParameter → Euclidean (n - 1) → ℝ) (high : A → ℝ → ℝ)
    {physicalCap cap : ℝ} (hphysicalCap : 0 < physicalCap)
    (hcap : 0 < cap) (hcap1 : cap ≤ 1) :
    ∃ radiusCap > (0 : ℝ), 4 * radiusCap < 1 / 2 ∧
      12 * radiusCap < physicalCap ∧ 12 * radiusCap < 1 / 2 ∧
      closedBall (0 : Euclidean n) (12 * radiusCap) ⊆ U ∧
    ∃ V : A → Set CarrierParameter,
      (∀ a, IsOpen (V a)) ∧ (∀ a, tsupport (χ a) ⊆ V a) ∧
      (∀ a, closedBall (0 : Euclidean n) (12 * radiusCap) ×ˢ V a ⊆ E a) ∧
    ∀ (r : ℝ) (hr : 0 < r), r ≤ radiusCap →
    ∀ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (a : A) →
      Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
        ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a)
        (sourceDilation G.map σ),
    ∃ hcell : 4 * r < 1 / 2,
    let H₀ := physicalDensityMean (fun a ↦ data (T a) (seed a).Q G.map
      (row a) (col a) (seed a).forward (seed a).inverse (fun _ ↦ 1)
      hr hcell (angular a) (high a)) χ 0 0
    let H := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦
      physicalDensityMean (fun a ↦ data (T a) (current σ hσ a).Q (sourceDilation G.map σ)
        (row a) (col a) (current σ hσ a).forward (current σ hσ a).inverse (fun _ ↦ σ)
        hr hcell (angular a) (high a)) χ 0
    let Q := fun σ ↦ projectedStress (sourceDilation G.map σ)
    let R := fun σ hσ ↦ referenceMeanResidual (sourceDilation G.map σ) H₀ (H σ hσ)
    H₀.PosSemidef ∧
      ∃ hQ : ∀ σ ∈ Ioc (0 : ℝ) cap, ContDiffOn ℝ ∞ (Q σ) (ball 0 (4 * r)),
      ∃ hR : ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), ContDiffOn ℝ ∞ (R σ hσ) (ball 0 (4 * r)),
      ∃ σ₀ > (0 : ℝ), σ₀ ≤ cap ∧ ∃ cNormal > (0 : ℝ),
      ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ → ∀ s,
          (periodicSobolevScale n (Euclidean n)).gradeNorm s
            (fixedSourceToL2 hr hcell (Q σ) (R σ hσ) (hQ σ hσ) (hR σ hσ)) ≤ C s * σ ∧
          cNorm (closedBall 0 (4 * r)) s (fun x ↦ H σ hσ x - H₀) ≤ C s * σ) ∧
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ → ∀ a x,
          x ∈ closedBall 0 (4 * r) → ∀ z ∈ tsupport (χ a),
            cNormal ≤ ‖(current σ hσ a).normal (fun _ ↦ σ) (x, z)‖) ∧
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), EqOn (R σ hσ)
          (fun x ↦ H σ hσ x - H₀) (ball 0 (5 * r))) := by
  obtain ⟨radiusCap, hradiusCap, hcapcell, hrCap, hrhalf, hrU, V, hV, hχV, hproduct, hflow⟩ :=
    exists_retained_weight_flow_buffer h0U T z₀ seed hL hRc hτ hσcover
      hcompRadius E hE hcomp hgraph hworking χ hχcompact hχE hphysicalCap
  refine ⟨radiusCap, hradiusCap, hcapcell, hrCap, hrhalf, hrU, V, hV, hχV, hproduct, ?_⟩
  intro r hr hrr current
  have hcell : 4 * r < 1 / 2 := by linarith
  let W := fun a ↦ ball (0 : Euclidean n) (12 * radiusCap) ×ˢ V a
  have h6U : closedBall (0 : Euclidean n) (6 * r) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hrU
  have h6W (a : A) : closedBall (0 : Euclidean n) (6 * r) ×ˢ V a ⊆ W a :=
    prod_mono (closedBall_subset_ball (by linarith)) Subset.rfl
  have hseed (a : A) : MapsTo (densityCoordinates (T a)) (W a) (seed a).D :=
    (hflow a).2.2.2 G.map (seed a)
  have hcurrent (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (a : A) :
      MapsTo (densityCoordinates (T a)) (W a) (current σ hσ a).D :=
    (hflow a).2.2.2 (sourceDilation G.map σ) (current σ hσ a)
  obtain ⟨hpos, hQ, hR, σ₀, hσ₀, hσcap, cNormal, hcNormal, C, hC,
    _hJ, hbound, hnormal, _hfields, hres⟩ :=
    exists_retained_fixedSource_sobolev_bounds hn G hUG hP hΩ hKΩ hpatch hRc hτ hτR
      hbuffer hphysical χ hχ hχcompact W hr hcell h6U V hV hχV h6W seed hseed
      htrans hcap hcap1 current hcurrent
  refine ⟨hcell, ?_⟩
  simp only [physicalDensityMean_retainedChart_zero]
  exact ⟨hpos, hQ, hR, σ₀, hσ₀, hσcap, cNormal, hcNormal, C, hC,
    fun σ hσ hs s ↦ ⟨(hbound σ hσ hs s).1, (hbound σ hσ hs s).2.1⟩,
    hnormal, hres⟩

end JanetCartan.PositiveBackground
