module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.IncidenceSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.Adjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourceRow

/-!
# Raw and density bounds for the constructed uncorrected incidence inverse

Choose the actual raw-adjoint support caps before the supplied detector masks.
Apply the incidence coercivity/inverse construction to those same masks and
retain its inner exterior. Literal kernel equality transfers the proved raw
estimates to this very inverse. The only inputs are the retained seed and
geometric projections, including the incidence covector and original domains.
The original initializer/selector must still instantiate those projections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace NNReal Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse
open ContinuumNormal ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CommonMeasurement NormalizedSelection
open FrozenModel RetainedFrozen FrozenImageComparison FrozenCoercivity
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.RetainedRowGeometry
open CarrierVariation.FamilyInputs.PositiveReference CarrierVariation.FamilyInputs.WideDensity
open PositiveReference.FlowConstruction NullTransport ActualFlow FlowAmplitude
open NormalizedBackground.SourceGeometry NormalizedNormalLimit SourceDensityLimitRealization
open ProjectedStressFrame LeadingPrimitive RetainedFrozen.UnitRealization
open Pseudodifferential AmplitudeBound PeriodicLocalL2 GeometricProfile

open ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.NormalizedFamily
open ContinuumAdjoint.DensityMultiplier CarrierSobolev

variable {n : ℕ} {cover : CoverData n} {c C : ℝ} {U : Set (Euclidean n)} {hU : IsOpen U}
    (menu : (b : Fin cover.chartCount) → (a : Fin (cover.patchCount b)) →
      PatchQuantitativeFamily (cover.patches b a) U hU)
    (centers : Finset (IncidenceCenter cover))

set_option quotPrecheck false in
local notation "ι" => RetainedIncidenceChannel cover centers
set_option quotPrecheck false in
local notation "family" => retainedIncidenceFamily menu centers
set_option quotPrecheck false in
local notation "roots" => retainedIncidenceCenters centers
set_option quotPrecheck false in
local notation "patches" => (fun i : ι ↦ cover.patches i.1.1.1.1 i.2)

/-- Construct the full augmented raw and both initial-density estimates for
one actual uncorrected incidence inverse. The support caps precede the prescribed
masks; all bounds and the inner exterior precede the source scale and target.
The gap, elliptic bootstrap and raw adjoint are obtained from their concrete
producers, with literal kernel equality preserving the row. No analytic bound
is assumed (`app:ch_background:prop:bg-inverse`, `app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-density-adjoint`). The wider-density normal estimates
remain available in `exists_realized_retained_incidence_inverse_estimates`. -/
theorem exists_retained_incidence_uncorrected_inverse_with_raw_bounds
    (hn₅ : 5 ≤ n) (hDd : cover.IsValid c C) (H : FlatReference n)
    (hUG : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    (Ωflow : ι → Set (Euclidean n × Euclidean 3)) (hΩ : ∀ i, IsOpen (Ωflow i))
    (zCell : ι → Euclidean 3) (ρc Rc B τlead L Mc : ι → ℝ) (row col : ι → Fin n)
    (hKΩ : ∀ i, closedBall ((0 : Euclidean n), zCell i) (ρc i) ⊆ Ωflow i)
    (hΩpatch : ∀ i, Ωflow i ⊆ (U ∩ ball 0 (family i).physicalRadius) ×ˢ
      parameterInterior (3 * (patches i).radius / 2))
    (hRc : ∀ i, 0 < Rc i) (hL : ∀ i, 0 < L i)
    (hbuffer : ∀ i, MapsTo (coordinates (adaptedCoordinates (family i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i))
      (closedBall ((0 : Euclidean n), zCell i) (ρc i)))
    (hphysical : ∀ i, closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius ⊆ U)
    (c₀ : (i : ι) → Chart (family i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i) H.map)
    (htrans : ∀ i q, q ∈ closedBall (0, (family i).data.center) (family i).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (c₀ i).Q.1 (c₀ i).Q.2.1).hp q,
        (family i).data.adapted.normal⟫_ℝ ≠ 0)
    (hBflow : ∀ i, 0 ≤ B i)
    (hτeq : ∀ i, τlead i = existenceTime (Rc i) (liftedLowBound (family i) (B i)) / 4)
    (hΩscale : ∀ i σ, σ ∈ Ioc (0 : ℝ) 1 →
      MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) (Ωflow i) (Ωflow i))
    (hMc : ∀ i, 0 < Mc i)
    (hforward : ∀ i, cNorm (Icc (-τlead i) (τlead i) ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) 1 (c₀ i).forward ≤ Mc i)
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRT : ∀ i, R i ≤ (family i).physicalRadius)
    (hRU : ∀ i, ball (0 : Euclidean n) (R i) ⊆ U)
    (hRtime : ∀ i, R i ≤ L i / (64 * Mc i))
    (V : ι → Set CarrierParameter) (hV : ∀ i, IsOpen (V i))
    (hVP : ∀ i, V i ⊆ parameter ⁻¹' parameterInterior (3 * (patches i).radius / 2))
    (hflow : ∀ i, MapsTo (densityCoordinates (family i)) (ball (0 : Euclidean n) (R i) ×ˢ V i)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τlead i)))
    (hlabel : ∀ i p, p ∈ ball (0 : Euclidean n) (R i) ×ˢ V i →
      (densityCoordinates (family i) p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 64))
    (D : ι → CoefficientNormCharts n)
    (hD : ∀ i, (D i).field.region ⊆ ball (0 : Euclidean n) (R i) ×ˢ V i)
    (ηb : ι → Euclidean (n - 1)) (hηb : ∀ i, ηb i ≠ 0)
    (k : ι → Euclidean n) (hk : ∀ i, k i ≠ 0)
    (hηbk : ∀ i, ηb i = (family i).data.adapted.embedding.toContinuousLinearMap.adjoint (k i))
    (hzRoot : ∀ i, roots i ∈ parameterInterior (patches i).radius)
    (hzV : ∀ i, (roots i 0, spectatorCenter (roots i)) ∈ V i)
    (hinc : ∀ i, incidence (k i) ((patches i).toFun (roots i)) = 0)
    (hd : ∀ i, fderiv ℝ (fun z ↦ incidence (k i) ((patches i).toFun z)) (roots i)
      (EuclideanSpace.single 0 1) ≠ 0) :
    ∃ aMax bMax : ι → ℝ, (∀ i, 0 < aMax i) ∧ (∀ i, 0 < bMax i) ∧
    ∀    (r a r' a' : ι → ℝ) (_hr : ∀ i, 0 < r i) (hr' : ∀ i, 0 < r' i)
    (ha' : ∀ i, 0 < a' i) (hcell : ∀ i, 4 * a' i < 1 / 2)
    (_haRaw : ∀ i, a' i ≤ aMax i)
    (_hbRaw : ∀ i, angularWidth (ηb i) (r' i) ≤ bMax i)
    (_hrr : ∀ i, r' i ≤ r i) (_haa : ∀ i, a' i ≤ a i)
    (_har' : ∀ i, a' i ≤ r' i) (_haR : ∀ i, 6 * a i < (family i).family.radius)
    (_hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (ha' i) 1) ×ˢ
      carrierSupport (roots i) (r := a' i) ⊆ (D i).field.carrier)
    (_houter : ∀ i, coefficientDomain (roots i) (r i) (6 * a i) ⊆
      ball (0 : Euclidean n) (R i) ×ˢ V i)
    (p₀ : ι → InputVariables n) (q₀ : ι → Variables n × Euclidean 2)
    (ρ τ : ι → ℝ) (_hρ : ∀ i, 0 < ρ i) (_hτ : ∀ i, 0 < τ i)
    (W Bi : ι → Set (InputVariables n)) (_hW : ∀ i, IsOpen (W i))
    (_hKiW : ∀ i, closedBall (p₀ i) (ρ i) ⊆ W i)
    (_hBi : ∀ i, IsCompact (Bi i)) (_hWBi : ∀ i, W i ⊆ Bi i)
    (_hBiDom : ∀ i, Bi i ⊆ symbolInputDomain (roots i) (ηb i) (r i) (6 * a i))
    (_hfoot : ∀ i p, p ∈ closedBall (p₀ i) (ρ i) → (D i).Contains p)
    (It : ι → Set ℝ) (_hIt : ∀ i, IsOpen (It i)) (_hIIt : ∀ i, Icc (0 : ℝ) 1 ⊆ It i)
    (_hsegT : ∀ i t, t ∈ It i → MapsTo (transportSegmentInput n t) (W i) (D i).field.region)
    (_hseg : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      MapsTo (transportSegmentInput n t) (W i) (D i).field.carrier)
    (A : ι → InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (ε gap : ι → ℝ) (_hε : ∀ i, 0 < ε i) (_hgap : ∀ i, 0 < gap i)
    (_hfreq : ∀ i p, p ∈ Bi i → ε i ≤ ‖p.2.2‖)
    (Qc Ωsource : ι → Set (Variables n × Euclidean 2))
    (_hQc : ∀ i, IsCompact (Qc i)) (_hΩsource : ∀ i, IsOpen (Ωsource i))
    (_hQcΩ : ∀ i, Qc i ⊆ Ωsource i)
    (_hne : ∀ i q, q ∈ Ωsource i → q.1.2.2 ≠ 0)
    (_hcone : ∀ i t, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ωsource i ↔ q ∈ Ωsource i)
    (δgeometry : ι → ℝ) (_hδgeometry : ∀ i, 0 < δgeometry i)
    (_hgeometry : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (family i).family.threshold,
        cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < (δgeometry i) →
        let QF : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (family i).family.threshold} := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (RetainedSpectralGeometry (family i) QF (roots i) (ηb i) (r i) (a i) ∧
        closedBall (q₀ i) (2 * (τ i)) ⊆ symbolDomain (family i) QF (roots i) (ηb i) (r i) (6 * (a i)) ∧
        MapsTo (inverseCoordinates (symbolInverse (family i) QF (roots i) (ηb i) (r i) (6 * (a i))))
          (closedBall (q₀ i) (2 * (τ i))) (closedBall (p₀ i) (ρ i)) ∧
        (∀ p ∈ closedBall (p₀ i) (ρ i), ‖(A i).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition (family i) QF)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ (Bi i), (gap i) ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (family i))
          (transportPosition (family i) QF) p) ∧
        (closure (augmentedTransportGradient (transportPosition (family i) QF) ''
          conicMaskSupport (roots i) (ηb i) (r' i) (a' i)) ∩ {p | p.1.2.2 ≠ 0} ⊆
            symbolDomain (family i) QF (roots i) (ηb i) (r i) (6 * (a i))) ∧
        (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition (family i) QF) ''
            conicMaskSupport (roots i) (ηb i) (r' i) (a' i)) → (x, v) ∈ closedBall (q₀ i) (τ i)) ∧
        (∀ p ∈ symbolDomain (family i) QF (roots i) (ηb i) (r i) (6 * (a i)),
          ‖(symbolInverse (family i) QF (roots i) (ηb i) (r i) (6 * (a i)) p).2‖ ≤ 2 * ‖p.1.2.2‖)) ∧
      (let u := symbolInverse (family i) QF (roots i) (ηb i) (r i) (6 * (a i))
      (Ωsource i) ⊆ symbolDomain (family i) QF (roots i) (ηb i) (r i) (6 * (a i)) ∧
      ContDiffOn ℝ ∞ u (Ωsource i) ∧ MapsTo (inverseCoordinates u) (Qc i) (closedBall (p₀ i) (ρ i)) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) (Ωsource i) (closedBall (p₀ i) (ρ i)) ∧
      (∀ q ∈ (Ωsource i), transportAveragedGradient (transportPosition (family i) QF)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall (p₀ i) (ρ i)), ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition (family i) QF)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ (Bi i), (gap i) ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (family i))
        (transportPosition (family i) QF) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates (family i))
        (transportPosition (family i) QF)) (W i) ∧
      EqOn (symbolJacobian (family i) QF)
        (transportAbsoluteJacobian (adaptedSliceCoordinates (family i)) (transportPosition (family i) QF)) (W i) ∧
      InjOn (augmentedTransportGradient (transportPosition (family i) QF)) (closedBall (p₀ i) (ρ i)) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport (roots i) (ηb i) (r' i) (a' i),
        scaleInput (‖(ηb i)‖ / ‖p.2.2‖) p ∈ (closedBall (p₀ i) (ρ i)) ∧
        transportAveragedGradient (transportPosition (family i) QF) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition (family i) QF) p) ∈ (Qc i) ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (transportPosition (family i) QF) p‖) p ∈ (closedBall (p₀ i) (ρ i)) ∧
        inverseCoordinates u (augmentedTransportGradient (transportPosition (family i) QF) p) = p) ∧
      (closure (augmentedTransportGradient (transportPosition (family i) QF) ''
        conicMaskSupport (roots i) (ηb i) (r' i) (a' i)) ∩ {q | q.1.2.2 ≠ 0} ⊆ (Ωsource i))) ∧
      (let u := frozenSymbolInverse (family i) QF (roots i) (ηb i) (r i) (6 * (a i))
      (Ωsource i) ⊆ frozenSymbolDomain (family i) QF (roots i) (ηb i) (r i) (6 * (a i)) ∧
      ContDiffOn ℝ ∞ u (Ωsource i) ∧ MapsTo (inverseCoordinates u) (Qc i) (closedBall (p₀ i) (ρ i)) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) (Ωsource i) (closedBall (p₀ i) (ρ i)) ∧
      (∀ q ∈ (Ωsource i), transportAveragedGradient (normalizedTransportPosition (family i) QF 0)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall (p₀ i) (ρ i)), ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition (family i) QF 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ (Bi i), (gap i) ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (family i))
        (normalizedTransportPosition (family i) QF 0) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates (family i))
        (normalizedTransportPosition (family i) QF 0)) (W i) ∧
      EqOn (frozenKernelJacobian (family i) QF)
        (transportAbsoluteJacobian (adaptedSliceCoordinates (family i)) (normalizedTransportPosition (family i) QF 0)) (W i) ∧
      InjOn (augmentedTransportGradient (normalizedTransportPosition (family i) QF 0)) (closedBall (p₀ i) (ρ i)) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport (roots i) (ηb i) (r' i) (a' i),
        scaleInput (‖(ηb i)‖ / ‖p.2.2‖) p ∈ (closedBall (p₀ i) (ρ i)) ∧
        transportAveragedGradient (normalizedTransportPosition (family i) QF 0) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (normalizedTransportPosition (family i) QF 0) p) ∈ (Qc i) ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (normalizedTransportPosition (family i) QF 0) p‖) p ∈ (closedBall (p₀ i) (ρ i)) ∧
        inverseCoordinates u (augmentedTransportGradient (normalizedTransportPosition (family i) QF 0) p) = p) ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition (family i) QF 0) ''
        conicMaskSupport (roots i) (ηb i) (r' i) (a' i)) ∩ {q | q.1.2.2 ≠ 0} ⊆ (Ωsource i))))
    (_hkernel : ∀ i, RetainedSpectralGeometry (family i) (c₀ i).Q (roots i) (ηb i) (r i) (a i))
    (_hcenter : ∀ i, originOutput (q₀ i) = q₀ i)
    (_hQcBall : ∀ i, Qc i ⊆ closedBall (q₀ i) (τ i))
    (εcover : centers → ℝ)
    (_hcover : sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (εcover j))
    (_hdomain : ∀ j : centers, ball j.1.1.2 (εcover j) ⊆ cover.domain j.1.1.1)
    (_hgram : ∀ j : centers, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ s : Euclidean n,
      c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil q) s‖ ^ 2 +
        ∑ l, inner ℝ (CubeCarrier.quadratic ((cover.patches j.1.1.1 l).toFun
          (cover.roots j.1.1.1 l q))) s ^ 2)
    (_hdetector : ∀ j : centers, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ l : Fin (cover.patchCount j.1.1.1),
      let i : ι := ⟨j, l⟩
      let zq := cover.roots j.1.1.1 l q
      (zq 0, spectatorCenter zq) ∈ V i ∧
        angularMask (roots i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1
          (zq 0, spectatorCenter zq) (NormedSpace.normalize
            ((family i).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1)
    {ρgraph τgraph : ι → ℝ} (_hρgraph : ∀ i, 0 < ρgraph i)
    (_hgraph : ∀ i, MapsTo (carrierGraph (family i)) (coefficientDomain (roots i) (r i) (6 * a i))
      (closedBall ((0 : Euclidean n), (zCell i, (family i).reference.spatialPatch (zCell i))) (ρgraph i)))
    (_hworking : ∀ i,
      closedBall ((0 : Euclidean n), (zCell i, (family i).reference.spatialPatch (zCell i))) (2 * ρgraph i) ⊆
        (coordinates (adaptedCoordinates (family i).data.adapted)).symm ''
          (Icc (-τgraph i / 2) (τgraph i / 2) ×ˢ closedBall
            ((0 : Euclidean (n - 1)), zCell i, (family i).reference.spatialPatch (zCell i)) (L i / 64)))
    {μ : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2) (_hμa : ∀ i, 6 * μ < a' i)
    (_houterCell : 6 * μ < 1 / 2)
    (χcoeff : Euclidean n → ℝ) (_hχcoeff : ContDiff ℝ ∞ χcoeff)
    (_hχsupport : tsupport χcoeff ⊆ ball 0 (5 * μ))
    (_hχplateau : closedBall 0 (4 * μ) ⊆ interior {x | χcoeff x = 1})
    (χinitial : ι → ContDiffBump (0 : CarrierVariable n)),
    let angular := fun i ↦ angularMask (roots i) (NormedSpace.normalize (ηb i)) (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1
    let χ := FixedCutoffs.periodic (n := n) hμ hμcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hμ hμcell 2
    ∃ g > (0 : ℝ), ∃ (rInner : ℝ) (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2),
    ∃ M ≥ (0 : ℝ), rInner ≤ μ ∧ 0 < NormalAugmentation.globalGap g M ∧
    ∃ Cell Kraw Cfull Dfull : ℕ → ℝ,
      (∀ s, 0 ≤ Cell s) ∧ (∀ s, 0 ≤ Kraw s) ∧
      (∀ s, 0 ≤ Cfull s) ∧ (∀ s, 0 ≤ Dfull s) ∧
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧
    ∃ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (i : ι) →
      Chart (family i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
        ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i)
        (sourceDilation H.map σ),
      (∀ σ hσ i, ∃ Ψ, ODE.IsSmoothFlowOn (liftedDirection (family i) (current σ hσ i).Q (row i) (col i))
        (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i) (Rc i / 2)
          (existenceTime (Rc i) (liftedLowBound (family i) (B i))) Ψ ∧
        (current σ hσ i).forward = forwardFromLift Ψ ∧ (current σ hσ i).inverse = footpointFromLift Ψ ∧
        EqOn (current σ hσ i).forward (sourceTransportFlow (c₀ i).forward σ)
          (Ioo (-τlead i) (τlead i) ×ˢ ball ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) ∧
        EqOn (current σ hσ i).inverse (sourceTransportFlow (c₀ i).inverse σ) (current σ hσ i).D ∧
        cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
          (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) < δgeometry i / 2 ∧
        MapsTo (densityFootpoint (family i) (current σ hσ i).inverse) (D i).field.region
          (ball ((0 : Euclidean (n - 1)), zCell i) (L i / 16))) ∧
    ∃ coeff : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ σ hσ j x, coeff σ hσ j x = χcoeff (centeredTorusRepresentative x) *
        geometricReducedCoefficients (sourceDilation H.map σ) (centeredTorusRepresentative x) j) ∧
      (∀ σ hσ j, IsSmoothPeriodic (coeff σ hσ j)) ∧
    ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap),
      let e := fun i ↦ data (family i) (current σ hσ i).Q (sourceDilation H.map σ) (row i) (col i)
        (current σ hσ i).forward (current σ hσ i).inverse (fun _ ↦ σ)
        (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency
      let eMeasured := fun i ↦ commonChartData (e i) (closedBall 0 (4 * μ)) χ
      ∃ Vcurrent : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i, (∀ f : carrierInitialTestSpace n, Vcurrent i (carrierInitialTestToLp f) =ᵐ[volume]
          carrierTestIntegral (e i) f.val) ∧
          (∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
            (Vcurrent i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
          ∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n, (∀ f : carrierInitialTestSpace n,
            Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) → Wop = Vcurrent i) ∧
        (∀ i, let Wop := restrictCarrier χ (Vcurrent i)
          (∀ f : carrierInitialTestSpace n,
            Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (eMeasured i) f.val) ∧
          (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ (eMeasured i).outputChart → Wop f x = 0) ∧
          (∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (eMeasured i) w) 2 (carrierMeasure n) ∧
            Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (eMeasured i) w)) ∧
      let image := imageChannel (coeff σ hσ) χ χsrc
      let V := fun i ↦ restrictCarrier χ (Vcurrent i)
      ‖physicalRow image V‖ ≤ Real.sqrt (M ^ 2 + min g (NormalAugmentation.globalGap g M) / 2) ∧
      (∀ w : OutputL2 n,
        (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
        (g / 2) * ‖w‖ ^ 2 ≤ ‖(physicalRow image V).adjoint w‖ ^ 2) ∧
      (∀ w : OutputL2 n, (NormalAugmentation.globalGap g M / 2) * ‖w‖ ^ 2 ≤
        inner ℝ (augmentedNormal image V (innerCutoff hrInner hInnerCell) w) w) ∧
      (∀ w : OutputL2 n, (NormalAugmentation.globalGap g M / 2) * ‖w‖ ^ 2 ≤
        ‖(augmentedRow image V (innerCutoff hrInner hInnerCell)).adjoint w‖ ^ 2) ∧
      (∀ w : OutputL2 n, ∀ᵐ x ∂volume,
        centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
          exteriorChannel (innerCutoff hrInner hInnerCell) w x = 0) ∧
      let Arow := augmentedRow image V (innerCutoff hrInner hInnerCell)
      let E := CoerciveInverse.normalOperator Arow
      let Q₀ := CoerciveInverse.rightInverse Arow
      let S := periodicSobolevScale n (Euclidean n)
      Arow ∘L Q₀ = ContinuousLinearMap.id ℝ (OutputL2 n) ∧
      ‖E.inverse‖ ≤ (NormalAugmentation.globalGap g M / 2)⁻¹ ∧
      (∀ e, ‖Q₀ e‖ ^ 2 ≤ (NormalAugmentation.globalGap g M / 2)⁻¹ * ‖e‖ ^ 2 ∧
        E (E.inverse e) = e ∧ E.inverse (E e) = e ∧
        (∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
          (Q₀ e).snd x = 0) ∧
        (∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
          physicalRow image V (Q₀ e).fst x = e x)) ∧
      (∀ s w, w ∈ S.level s → E w ∈ S.level (s + 1) → w ∈ S.level (s + 1)) ∧
      (∀ s w, w ∈ S.level (s + 1) → E w ∈ S.level (s + 1) →
        S.gradeNorm (s + 1) w ≤ Cell (s + 1) *
          (S.gradeNorm (s + 1) (E w) + S.gradeNorm s w +
            ‖w‖)) ∧
      (∀ s e, e ∈ S.level s → E.inverse e ∈ S.level s ∧
        S.gradeNorm s (E.inverse e) ≤ bootstrapConstant (NormalAugmentation.globalGap g M / 2) Cell s *
          (S.gradeNorm s e + ‖e‖)) ∧
      (∀ s w, w ∈ S.level s →
        Arow.adjoint w ∈ augmentedInputLevel n ι s ∧
        (augmentedInputSobolevScale n ι).gradeNorm s (Arow.adjoint w) ≤
          Kraw s * (S.gradeNorm s w + ‖w‖)) ∧
      (∀ s e, e ∈ S.level s →
        Q₀ e ∈ augmentedInputLevel n ι s ∧
        S.gradeNorm s (E.inverse e) + (augmentedInputSobolevScale n ι).gradeNorm s (Q₀ e) ≤
          Cfull s * (S.gradeNorm s e + ‖e‖)) ∧
      (∀ s e, e ∈ S.level (s + 1) →
        ∃ hf : ∀ i, MemRawSobolev 1 ((Q₀ e).fst.snd i),
          (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut (roots i) (NormedSpace.normalize (ηb i)) (ha' i)
              (angularWidth_spec (hηb i) (hr' i)).1 ((Q₀ e).fst.snd i) (hf i))) ∧
            MemPhysicalSobolev s (physicalComplexifyL2
            (density (roots i) (NormedSpace.normalize (ηb i)) (ha' i)
              (angularWidth_spec (hηb i) (hr' i)).1 (χinitial i) ((Q₀ e).fst.snd i) (hf i)))) ∧
          densityUncutFamilySize roots (fun i ↦ NormedSpace.normalize (ηb i)) ha'
            (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) s (Q₀ e) ≤
            Dfull s * (S.gradeNorm (s + 1) e + ‖e‖) ∧
          densityFamilySize roots (fun i ↦ NormedSpace.normalize (ηb i)) ha'
            (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) χinitial s (Q₀ e) ≤
            Dfull s * (S.gradeNorm (s + 1) e + ‖e‖)) := by
  classical
  have hP (i : ι) : (patches i).IsValid c C := (hDd.2.2.2.2.1 i.1.1.1.1 i.2).1
  have hτlead (i : ι) : 0 < τlead i := by
    rw [hτeq i]
    exact div_pos (existenceTime_pos (hRc i) (liftedLowBound_nonneg (family i) (hBflow i))) (by norm_num)
  have hτRc (i : ι) : τlead i ≤ Rc i / 16 := by
    have ht := (existenceTime_le (hRc i) (liftedLowBound_nonneg (family i) (hBflow i))).1
    rw [hτeq i]
    linarith
  have hpatch (i : ι) : Ωflow i ⊆ ball 0 (family i).physicalRadius ×ˢ parameterCube (2 * (patches i).radius) :=
    fun w hw ↦ ⟨(hΩpatch i hw).1.2, fun j ↦ ((hΩpatch i hw).2 j).le.trans (by linarith only [(hP i).1])⟩
  obtain ⟨aMax, bMax, haMax, hbMax, _haMaxCap, χplateau, hrawMasks⟩ :=
    exists_retained_source_augmentedAdjoint_for_prescribed_masks
      H hP family hUG hbounded hΩ hKΩ hpatch hRc hτlead hτRc hbuffer hphysical c₀ htrans
      hR hRT hRU hV hVP hflow hzRoot hzV hk hinc hd (by norm_num : (0 : ℝ) < 1)
  refine ⟨aMax, bMax, haMax, hbMax, ?_⟩
  intro r a r' a' hr hr' ha' hcell haRaw hbRaw hrr haa har' haR hsupportD houter
    p₀ q₀ ρ τ hρ hτ W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg A ε gap hε hgap hfreq
    Qc Ωsource hQc hΩsource hQcΩ hne hcone δgeometry hδgeometry hgeometry hkernel hcenter hQcBall
    εcover hcover hdomain hgram hdetector ρgraph τgraph hρgraph hgraph hworking
    μ hμ hμcell hμa houterCell χcoeff hχcoeff hχsupport hχplateau χinitial angular χ χsrc
  obtain ⟨g, hg, rInner, hrInner, hInnerCell, M, hM, hrμ, hG, Cell, hCell,
      cap₀, hcap₀, hcap₀1, current₀, hcurrent₀, coeff₀, hcoeff₀, hsmooth₀, hinverse⟩ :=
    exists_realized_retained_incidence_inverse_estimates menu centers hn₅ hDd H hUG hbounded
      Ωflow hΩ zCell ρc Rc B τlead L Mc row col hKΩ hΩpatch hRc hL hbuffer hphysical c₀ htrans
      hBflow hτeq hΩscale hMc hforward R hR hRT hRU hRtime V hV hVP hflow hlabel D hD
      ηb hηb r a r' a' hr hr' ha' hcell hrr haa har' haR hsupportD houter
      p₀ q₀ ρ τ hρ hτ W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg
      A ε gap hε hgap hfreq Qc Ωsource hQc hΩsource hQcΩ hne hcone δgeometry hδgeometry hgeometry
      hkernel hcenter hQcBall εcover hcover hdomain hgram hdetector hρgraph hgraph hworking
      hμ hμcell hμa houterCell χcoeff hχcoeff hχsupport hχplateau
  let ψ := innerCutoff (n := n) hrInner hInnerCell
  let γ := NormalAugmentation.globalGap g M / 2
  have hγ : 0 < γ := half_pos hG
  obtain ⟨_hsupported, capRaw, hcapRaw, _hcapRaw1, coeffRaw, Kraw, Lraw,
      hKraw, hLraw, _hcoeffRawSmooth, _hcoeffRaw, hraw⟩ :=
    hrawMasks a' (fun i ↦ angularWidth (ηb i) (r' i)) ha'
      (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) haRaw hbRaw
      μ hμ hμcell houterCell hμa χcoeff hχcoeff hχsupport hχplateau χinitial ψ
      (innerCutoff_smooth hrInner hInnerCell)
  let β := bootstrapConstant γ Cell
  let Cfull := fun s ↦ β s + Kraw s * (β s + γ⁻¹)
  let Dfull := fun s ↦ Lraw s * (β (s + 1) + γ⁻¹)
  have hβ (s : ℕ) : 0 ≤ β s := bootstrapConstant_nonneg hγ hCell s
  have hCfull (s : ℕ) : 0 ≤ Cfull s := add_nonneg (hβ s)
    (mul_nonneg (hKraw s) (add_nonneg (hβ s) (inv_nonneg.mpr hγ.le)))
  have hDfull (s : ℕ) : 0 ≤ Dfull s := mul_nonneg (hLraw s)
    (add_nonneg (hβ (s + 1)) (inv_nonneg.mpr hγ.le))
  let cap := min cap₀ capRaw
  have hcap : 0 < cap := lt_min hcap₀ hcapRaw
  have hc₀ : cap ≤ cap₀ := min_le_left _ _
  have hcRaw : cap ≤ capRaw := min_le_right _ _
  let current := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ current₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩
  let coeff := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ coeff₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩
  refine ⟨g, hg, rInner, hrInner, hInnerCell, M, hM, hrμ, hG,
    Cell, Kraw, Cfull, Dfull, hCell, hKraw, hCfull, hDfull,
    cap, hcap, hc₀.trans hcap₀1, current, fun σ hσ ↦ hcurrent₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩,
    coeff, fun σ hσ ↦ hcoeff₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩,
    fun σ hσ ↦ hsmooth₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩, ?_⟩
  intro σ hσ e eMeasured
  have hzeroNorm (K : Set (Euclidean (n - 1) × Euclidean 3)) (s : ℕ) :
      cNorm K s (fun _ ↦ (0 : ℝ)) = 0 := cNorm_zero K s
  obtain ⟨Vcurrent, htest, hmeasured, hnorm, hlocal, hnormal, hgapRow, hexterior,
      hright, hEinv, hbase, hreg, hstep, hest, _hnormalized⟩ :=
    hinverse σ ⟨hσ.1, hσ.2.trans hc₀⟩ (fun _ _ ↦ 0)
      (fun _ ↦ contDiffOn_const) (by intro i q hq; norm_num)
      (by intro i q hq; norm_num) (by intro i; rw [hzeroNorm]; exact zero_le_one)
  simp only [positiveDensityAmplitude_zero] at htest hmeasured hnorm hlocal hnormal hgapRow hexterior hright hEinv hbase hreg hstep hest
  simp only [hzeroNorm, Finset.sum_const_zero, add_zero, one_mul] at hstep hest
  refine ⟨Vcurrent, htest, hmeasured, hnorm, hlocal, hnormal, hgapRow, hexterior, ?_⟩
  intro Arow E Q₀ S
  obtain ⟨_hplateau, hkernel, Vraw, _hVraw, _hunique, hrawActual⟩ :=
    hraw σ ⟨hσ.1, hσ.2.trans hcRaw⟩
  have hηdir (i : ι) : NormedSpace.normalize
      ((family i).data.adapted.embedding.toContinuousLinearMap.adjoint (k i)) = NormedSpace.normalize (ηb i) :=
    congrArg NormedSpace.normalize (hηbk i).symm
  have hrep (i : ι) (w : ComplexOutputL2 n) :
      (restrictCarrier χ (Vcurrent i)).adjoint w =ᵐ[carrierMeasure n]
        carrierAdjointIntegral (normalizedCarrierData (family i) (c₀ i).Q H.map (row i) (col i)
          (c₀ i).forward (c₀ i).inverse (fun _ ↦ 1) hμ hμcell
          (angularMask (roots i) (NormedSpace.normalize
            ((family i).data.adapted.embedding.toContinuousLinearMap.adjoint (k i))) (ha' i)
            (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency σ) w := by
    have hkern := hkernel (current σ hσ) i
    simp only [hηdir] at hkern ⊢
    have hmeas : eMeasured i = data (family i) (current σ hσ i).Q (sourceDilation H.map σ)
        (row i) (col i) (current σ hσ i).forward (current σ hσ i).inverse (fun _ ↦ σ)
        hμ hμcell (angular i) FixedCutoffs.highFrequency := rfl
    have hh : (restrictCarrier χ (Vcurrent i)).adjoint w =ᵐ[carrierMeasure n]
        carrierAdjointIntegral (eMeasured i) w := ((hmeasured i).2.2 w).2
    rw [hmeas, carrierAdjointIntegral_congr_kernel hkern] at hh
    exact hh
  obtain ⟨hrawRow, hdensityRow⟩ := hrawActual (coeff σ hσ)
    (hcoeff₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩) (fun i ↦ restrictCarrier χ (Vcurrent i)) hrep
  have hfull (s : ℕ) (f : OutputL2 n) (hf : f ∈ S.level s) :
      Q₀ f ∈ augmentedInputLevel n ι s ∧
      S.gradeNorm s (E.inverse f) + (augmentedInputSobolevScale n ι).gradeNorm s (Q₀ f) ≤
        Cfull s * (S.gradeNorm s f + ‖f‖) := by
    have hinv := hest s f hf
    refine ⟨(hrawRow s _ hinv.1).1, ?_⟩
    simpa only [one_mul] using inverse_add_rightInverse_gradeNorm_le S
      (augmentedInputSobolevScale n ι) Arow hγ hgapRow (hKraw s) zero_le_one
      hinv.1 (by simpa only [one_mul] using hinv.2)
      (fun w hw ↦ by simpa only [one_mul] using (hrawRow s w hw).2)
  refine ⟨hright, hEinv, hbase, hreg, hstep, hest, hrawRow, hfull, ?_⟩
  intro s f hf
  have hi := hest (s + 1) f hf
  obtain ⟨hrawOne, hmem, huncut, hcut⟩ := hdensityRow s (E.inverse f) hi.1
  have hb : (periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) (E.inverse f) + ‖E.inverse f‖ ≤
      (β (s + 1) + γ⁻¹) * (S.gradeNorm (s + 1) f + ‖f‖) := by
    have hlow := CoerciveInverse.norm_inverse_apply_le E hγ hnormal f
    have hs := S.gradeNorm_nonneg (s + 1) f
    have hgi := inv_nonneg.mpr hγ.le
    dsimp only [β]
    nlinarith [hi.2]
  have hb' := mul_le_mul_of_nonneg_left hb (hLraw s)
  simp only [hηdir] at hrawOne hmem huncut hcut
  refine ⟨hrawOne, hmem, huncut.trans ?_, hcut.trans ?_⟩ <;>
    simpa only [Dfull, mul_assoc] using hb'

end JanetCartan.ContinuumInverse
