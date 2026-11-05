module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.MeasuredPerturbation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityFreezing.UnitSeed
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.MeasuredImage
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedFrozenGap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.SeedCovector
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SelectedSourceNormals
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.RetainedCommonCone
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.SourceFamily

/-!
# Coercivity of the realized positive-source row

The current carriers are built on charts pulled back from the supplied seeds. The
comparison uses the genuine divided-footpoint carrier at zero; its companion
origin-frozen carrier is the one furnished by the initialized detector gap.
Its unit input is constructed from this same kernel, and the original detector
covectors follow by dilation at the origin.
The image and measured carrier errors each cost a quarter of the smaller gap.

The geometric inputs are projections of the retained comparison construction:
the current/frozen conic callback and the original kernel’s buffered phase
inverse. The seed’s frozen output ball and inverse range follow from the
positive-source ball by setting the two positions to zero. The same positive
source also supplies the common zero cone. Each positive source lies below half
the geometric frame threshold, leaving room for the finite history comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace NNReal Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.ActualConstruction
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

/-- Construct the positive-source charts and operators and prove their local row and
global augmented half-gaps on the supplied retained geometry. Both literal normal
realizations are constructed for the original nonconstant positive density class.
The original phase-kernel geometry, detector plateaus and conic callback are
used on these very cells to construct the nonconstant frozen gap. A strict
frame margin and the inverse label range on the original coefficient region
are retained for history admission.
The inner cutoff and gaps precede the scale and density
(`app:ch_background:prop:bg-normalized`, `app:ch_background:eq:bg-local-bound`,
`app:ch_background:eq:bg-global-bound`). -/
theorem exists_realized_retained_incidence_source_coercivity
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
    (r a r' a' : ι → ℝ) (hr : ∀ i, 0 < r i) (hr' : ∀ i, 0 < r' i)
    (ha' : ∀ i, 0 < a' i) (hcell : ∀ i, 4 * a' i < 1 / 2)
    (hrr : ∀ i, r' i ≤ r i) (haa : ∀ i, a' i ≤ a i)
    (har' : ∀ i, a' i ≤ r' i) (haR : ∀ i, 6 * a i < (family i).family.radius)
    (hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (ha' i) 1) ×ˢ
      carrierSupport (roots i) (r := a' i) ⊆ (D i).field.carrier)
    (houter : ∀ i, coefficientDomain (roots i) (r i) (6 * a i) ⊆
      ball (0 : Euclidean n) (R i) ×ˢ V i)
    (p₀ : ι → InputVariables n) (q₀ : ι → Variables n × Euclidean 2)
    (ρ τ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hτ : ∀ i, 0 < τ i)
    (W Bi : ι → Set (InputVariables n)) (hW : ∀ i, IsOpen (W i))
    (hKiW : ∀ i, closedBall (p₀ i) (ρ i) ⊆ W i)
    (hBi : ∀ i, IsCompact (Bi i)) (hWBi : ∀ i, W i ⊆ Bi i)
    (hBiDom : ∀ i, Bi i ⊆ symbolInputDomain (roots i) (ηb i) (r i) (6 * a i))
    (hfoot : ∀ i p, p ∈ closedBall (p₀ i) (ρ i) → (D i).Contains p)
    (It : ι → Set ℝ) (hIt : ∀ i, IsOpen (It i)) (hIIt : ∀ i, Icc (0 : ℝ) 1 ⊆ It i)
    (hsegT : ∀ i t, t ∈ It i → MapsTo (transportSegmentInput n t) (W i) (D i).field.region)
    (hseg : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      MapsTo (transportSegmentInput n t) (W i) (D i).field.carrier)
    (A : ι → InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (ε gap : ι → ℝ) (hε : ∀ i, 0 < ε i) (hgap : ∀ i, 0 < gap i)
    (hfreq : ∀ i p, p ∈ Bi i → ε i ≤ ‖p.2.2‖)
    (Qc Ωsource : ι → Set (Variables n × Euclidean 2))
    (hQc : ∀ i, IsCompact (Qc i)) (hΩsource : ∀ i, IsOpen (Ωsource i))
    (hQcΩ : ∀ i, Qc i ⊆ Ωsource i)
    (hne : ∀ i q, q ∈ Ωsource i → q.1.2.2 ≠ 0)
    (hcone : ∀ i t, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ωsource i ↔ q ∈ Ωsource i)
    (δgeometry : ι → ℝ) (hδgeometry : ∀ i, 0 < δgeometry i)
    (hgeometry : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
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
    (hkernel : ∀ i, RetainedSpectralGeometry (family i) (c₀ i).Q (roots i) (ηb i) (r i) (a i))
    (hcenter : ∀ i, originOutput (q₀ i) = q₀ i)
    (hQcBall : ∀ i, Qc i ⊆ closedBall (q₀ i) (τ i))
    (εcover : centers → ℝ)
    (hcover : sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (εcover j))
    (hdomain : ∀ j : centers, ball j.1.1.2 (εcover j) ⊆ cover.domain j.1.1.1)
    (hgram : ∀ j : centers, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ s : Euclidean n,
      c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil q) s‖ ^ 2 +
        ∑ l, inner ℝ (CubeCarrier.quadratic ((cover.patches j.1.1.1 l).toFun
          (cover.roots j.1.1.1 l q))) s ^ 2)
    (hdetector : ∀ j : centers, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ l : Fin (cover.patchCount j.1.1.1),
      let i : ι := ⟨j, l⟩
      let zq := cover.roots j.1.1.1 l q
      (zq 0, spectatorCenter zq) ∈ V i ∧
        angularMask (roots i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1
          (zq 0, spectatorCenter zq) (NormedSpace.normalize
            ((family i).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1)
    {ρgraph τgraph : ι → ℝ} (hρgraph : ∀ i, 0 < ρgraph i)
    (hgraph : ∀ i, MapsTo (carrierGraph (family i)) (coefficientDomain (roots i) (r i) (6 * a i))
      (closedBall ((0 : Euclidean n), (zCell i, (family i).reference.spatialPatch (zCell i))) (ρgraph i)))
    (hworking : ∀ i,
      closedBall ((0 : Euclidean n), (zCell i, (family i).reference.spatialPatch (zCell i))) (2 * ρgraph i) ⊆
        (coordinates (adaptedCoordinates (family i).data.adapted)).symm ''
          (Icc (-τgraph i / 2) (τgraph i / 2) ×ˢ closedBall
            ((0 : Euclidean (n - 1)), zCell i, (family i).reference.spatialPatch (zCell i)) (L i / 64)))
    {μ : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2) (hμa : ∀ i, 6 * μ < a' i)
    (houterCell : 6 * μ < 1 / 2)
    (χcoeff : Euclidean n → ℝ) (hχcoeff : ContDiff ℝ ∞ χcoeff)
    (hχsupport : tsupport χcoeff ⊆ ball 0 (5 * μ))
    (hχplateau : closedBall 0 (4 * μ) ⊆ interior {x | χcoeff x = 1}) :
    let angular := fun i ↦ angularMask (roots i) (NormedSpace.normalize (ηb i)) (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1
    let χ := FixedCutoffs.periodic (n := n) hμ hμcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hμ hμcell 2
    ∃ g > (0 : ℝ), ∃ (rInner : ℝ) (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2),
    ∃ M ≥ (0 : ℝ), rInner ≤ μ ∧ 0 < NormalAugmentation.globalGap g M ∧
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
    ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4))) →
      (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4) → 0 < 1 + v i q) →
      (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8) →
        1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8))
        (2 * (n + 1) + 14) (v i) ≤ 1) →
      let e := fun i ↦ data (family i) (current σ hσ i).Q (sourceDilation H.map σ) (row i) (col i)
        (current σ hσ i).forward (current σ hσ i).inverse (fun q ↦ positiveDensityAmplitude σ (v i q))
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
          exteriorChannel (innerCutoff hrInner hInnerCell) w x = 0) := by
  classical
  intro angular χ χsrc
  have hn : 0 < n := by omega
  have hP (i : ι) : (patches i).IsValid c C := (hDd.2.2.2.2.1 i.1.1.1.1 i.2).1
  have hτlead (i : ι) : 0 < τlead i := by
    rw [hτeq i]
    exact div_pos (existenceTime_pos (hRc i) (liftedLowBound_nonneg (family i) (hBflow i))) (by norm_num)
  have hτRc (i : ι) : τlead i ≤ Rc i / 16 := by
    have h := (existenceTime_le (hRc i) (liftedLowBound_nonneg (family i) (hBflow i))).1
    rw [hτeq i]
    linarith
  have hF := H.contDiff
  have hi : IsImmersionOn H.map U := isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1)
    (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ H.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUG hx)
  have hflat : ∀ x ∈ U, inducedMetric H.map x = 1 := fun x _ ↦ H.inducedMetric_eq_one x
  have hpatch (i : ι) : Ωflow i ⊆ ball 0 (family i).physicalRadius ×ˢ parameterCube (2 * (patches i).radius) :=
    fun w hw ↦ ⟨(hΩpatch i hw).1.2, fun j ↦ ((hΩpatch i hw).2 j).le.trans (by linarith only [(hP i).1])⟩
  choose δcov hδcov hcovector using fun i : ι ↦
    exists_uniform_seed_carrierGradient_zero (family i) (hP i)
  let δchart := fun i ↦ min (δgeometry i / 2) (δcov i)
  obtain ⟨sourceCap, hsourceCap, hcap1, current, hcharts⟩ :=
    NormalizedChartFamily.exists_finite_source_charts_with_lifts H hUG hbounded family Ωflow hΩ
      zCell ρc Rc B τlead δchart row col hRc hBflow (fun i ↦ lt_min (half_pos (hδgeometry i)) (hδcov i)) hτeq hKΩ hpatch
      (fun i _ hw ↦ (hΩpatch i hw).1.1) hΩscale hphysical hbuffer c₀ htrans
  let anchor := sourceCap / 2
  have hanchor : anchor ∈ Ioc (0 : ℝ) sourceCap :=
    ⟨half_pos hsourceCap, half_le_self hsourceCap.le⟩
  let Qanchor := fun i ↦ (current anchor hanchor i).Q
  let Z := fun i ↦ normalizedTransportPosition (family i) (c₀ i).Q 0
  let J := fun i ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (family i)) (Z i)
  let u₀ := fun i ↦ frozenSymbolInverse (family i) (c₀ i).Q (roots i) (ηb i) (r i) (6 * a i)
  let S := fun i ↦ closedBall (spectatorCenter (roots i)) (a' i / 2)
  choose Gphase β cJ Vphase Lphase hcJ hVphase hLphase hf hInv hconePhase hslice using
    fun i ↦ (hkernel i).2.2
  have hsource (i : ι) : ∀ σ ∈ Ioc (0 : ℝ) 1,
      MapsTo (densityFootpoint (family i) (sourceTransportFlow (c₀ i).inverse σ)) (ball 0 (R i) ×ˢ V i)
        (ball ((0 : Euclidean (n - 1)), zCell i) (L i / 16)) := by
    intro σ hσ p hp
    apply sourceDensityFootpoint_mem_original_ball_of_forward_cNorm (family i) (hL i) (hRc i) (hτlead i) (hMc i)
      (c₀ i) (hforward i) (hflow i hp) (hlabel i p hp) _ hσ.1 hσ.2
    change |(adaptedCoordinates (family i).data.adapted p.1).1| < L i / (64 * Mc i)
    rw [adaptedCoordinates_apply]
    have ht := abs_real_inner_le_norm (family i).data.adapted.normal p.1
    rw [(family i).data.adapted.normal_unit, one_mul] at ht
    exact (ht.trans_lt (mem_ball_zero_iff.mp hp.1)).trans_le (hRtime i)
  have hzero (i : ι) := by
    obtain ⟨_, _, _, hiA, hrankA, hsmallA, _⟩ := (hcharts anchor hanchor i).choose_spec
    have hframe := (current anchor hanchor i).frame_eq
    have hlow := (Qanchor i).2.2
    change cNorm _ 6 ((current anchor hanchor i).Q.val - _) < _ at hlow
    rw [hframe] at hlow hsmallA
    have hFA : ContDiffOn ℝ ∞ (sourceDilation H.map anchor) U :=
      (contDiff_sourceDilation H.contDiff).contDiffOn
    have hgeom := hgeometry i (sourceDilation H.map anchor) hFA hiA hrankA hlow
      ((hsmallA.trans_le (min_le_left _ _)).trans (half_lt_self (hδgeometry i)))
    have hQA : (⟨projectedStress (sourceDilation H.map anchor),
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hFA hiA hrankA), hlow⟩ :
        {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (family i).family.threshold}) = Qanchor i :=
      Subtype.ext hframe.symm
    dsimp only at hgeom
    rw [hQA] at hgeom
    obtain ⟨hbase, _, hcone₀⟩ := hgeom
    obtain ⟨hΩf, _, hrange, hnormalized, _, hhalf, hJ, _, _, _, _, hmask, _⟩ := hcone₀
    have hmaskInput : conicMaskSupport (roots i) (ηb i) (r' i) (a' i) ⊆
        frozenInputDomain (roots i) (ηb i) (r i) (6 * a i) := by
      intro p hp
      have hx := (conicMaskSupport_subset (hηb i) (hr' i) (ha' i) (har' i)).trans
        (symbolInputDomain_mono (roots i) (ηb i) (hrr i) (mul_le_mul_of_nonneg_left (haa i) (by norm_num))) hp
      have ha := (ha' i).trans_le (haa i)
      exact ⟨⟨hx.1.1, mem_ball_self (by positivity), mem_ball_self (by positivity)⟩, hx.2⟩
    obtain ⟨_, _, _, hright, hhalf₀, hgap₀, _, _, _, hscale, _, hpunct, hshell⟩ :=
      retained_seed_frozen_comparison_geometry_of_source (family i) (c₀ i).Q (Qanchor i)
        hF hrank (hphysical i) (c₀ i).frame_eq (htrans i) hanchor.1 (hanchor.2.trans hcap1)
        hframe (hP i) (hηb i) (hr i) ((ha' i).trans_le (haa i)) (by norm_num : (0 : ℝ) < 1 / 4)
        hbase.1 (hKiW i) ((hWBi i).trans (hBiDom i)) (hQc i) (hQcΩ i) hΩf (hne i) (hcone i)
        hrange hnormalized (A i) hhalf (fun p hp ↦ hJ p (hWBi i (hKiW i hp))) hmaskInput
        (fun p hp ↦ (hmask p hp).2.2.1)
    have huEq := frozenSymbolInverse_eq_of_source_dilation (family i) (c₀ i).Q (Qanchor i)
      hF hrank (hphysical i) (c₀ i).frame_eq (htrans i) hanchor.1 (hanchor.2.trans hcap1)
      hframe (hP i) (hηb i) (hr i) hbase.1
    have hball := closedBall_subset_closedBall (x := q₀ i) (by linarith only [hτ i] : τ i ≤ 2 * τ i)
    have horigin (p : Variables n × Euclidean 2) (hp : p ∈ closedBall (q₀ i) (τ i)) :
        originOutput p ∈ closedBall (q₀ i) (τ i) := by
      rw [← hcenter i]
      simp only [mem_closedBall, originOutput, Prod.dist_eq, max_le_iff, dist_self] at hp ⊢
      exact ⟨⟨(hτ i).le, (hτ i).le, hp.1.2.2⟩, hp.2⟩
    have hdomEq := frozenSymbolDomain_eq_of_source_dilation (family i) (c₀ i).Q (Qanchor i)
      hF hrank (hphysical i) (c₀ i).frame_eq (htrans i) hanchor.1 (hanchor.2.trans hcap1)
      hframe (hP i) (ηb := ηb i) (hr i) hbase.1.1 hbase.1.2.1
    have houtput₀ : closedBall (q₀ i) (τ i) ⊆
        frozenSymbolDomain (family i) (c₀ i).Q (roots i) (ηb i) (r i) (6 * a i) := by
      rw [← hdomEq]
      exact fun p hp ↦ hbase.2.1 (hball (horigin p hp))
    have hrange₀ : MapsTo (inverseCoordinates (u₀ i)) (closedBall (q₀ i) (τ i))
        (closedBall (p₀ i) (ρ i)) := by
      dsimp only [u₀]
      rw [← huEq]
      intro p hp
      have hxy := hbase.2.2.1 (hball hp)
      have hrest := hbase.2.2.1 (hball (horigin p hp))
      simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hxy hrest ⊢
      exact ⟨hxy.1, hrest.2⟩
    rw [huEq] at hnormalized
    obtain ⟨hY, _, hzeroLabel, hparam, _⟩ := exists_retained_chart_source_primitive_convergence_on_outputCylinder
      (hP i) (family i) (hΩ i) (hKΩ i) (hΩpatch i) (hRc i) (hτlead i) (hτRc i) (hbuffer i)
      hF hi hrank (hphysical i) (c₀ i) (htrans i) hflat (hR i) (hRT i) (hRU i) (hV i) (hVP i)
      (hflow i) (D i) ((D i).field.ball_subset.trans (hD i)) (a' i) (ha' i) (hcell i)
      (angular i) FixedCutoffs.highFrequency
    have hmaps := fun p hp ↦ (c₀ i).small_subset
      ((outputCylinder_spec (hRc i) (hτlead i)).2 (hflow i (x := p) hp))
    obtain ⟨_, hscalar, _, _, _, _, _, _⟩ := (c₀ i).scalar_spec (hτlead i) (fun _ ↦ 1)
      contDiffOn_const (fun _ _ ↦ zero_lt_one)
    have hscalar' := hscalar.comp
      (contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)).contDiffOn hmaps
    have hcommon := exists_retained_source_zero_density_limit_on_common_cone (family i) (c₀ i).Q H.map (row i) (col i)
      (c₀ i).forward (c₀ i).inverse (hηb i) (hr i) (hr' i) (ha' i) (hrr i) (haa i) (har' i)
      (hcell i) (hP i) (c₀ i).frame_eq hF.contDiffOn hi hrank (hR i) (hRT i) (hRU i)
      (hV i) (houter i) (hVP i) hscalar' hY hzeroLabel hparam (hL i) zero_lt_one (hsource i)
      (D i) (hD i) (hkernel i).1 (hkernel i).2.1 (hf i) (hInv i) (hconePhase i)
      (hVphase i) (hLphase i) (hcJ i) (hslice i)
      (p₀ i) (q₀ i) (hρ i) (hτ i) (hW i) (hKiW i) (hBi i) (hWBi i) (hBiDom i)
      houtput₀ (hIt i) (hIIt i) (hsegT i) (hseg i) (A i) (hgap i) (hε i)
      (fun p hp ↦ hfreq i p (hWBi i (hKiW i hp))) (hfoot i) (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num) hrange₀ hhalf₀ hgap₀ (fun x hx v _ hv ↦ hQcBall i (hshell (x, v) hv hx))
      (hsupportD i) (u₀ i) (hne i) hnormalized (fun t ht p _ ↦ hscale t ht p) hright hpunct
    exact And.intro (unitCarrierOutput_of_retained_density_kernel (family i) (c₀ i).Q H.map (row i) (col i)
      (c₀ i).forward (c₀ i).inverse (hηb i) (hr i) (hr' i) (ha' i) (hrr i) (haa i) (har' i)
      (hcell i) (hP i) (c₀ i).frame_eq hF.contDiffOn hi hrank (hR i) (hRT i) (hRU i)
      (hV i) (houter i) (hVP i) hscalar' hY hzeroLabel hparam (hL i) zero_lt_one (hsource i)
      (D i) (hD i) (hkernel i).1 (hkernel i).2.1 (hf i) (hInv i) (hconePhase i)
      (hVphase i) (hLphase i) (hcJ i) (hslice i)
      (p₀ i) (q₀ i) (hρ i) (hτ i) (hW i) (hKiW i) (hBi i) (hWBi i) (hBiDom i)
      houtput₀ (hIt i) (hIIt i) (hsegT i) (hseg i) (A i) (hgap i) (hε i)
      (fun p hp ↦ hfreq i p (hWBi i (hKiW i hp))) (hfoot i) (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num) hrange₀ hhalf₀ hgap₀ (fun x hx v _ hv ↦ hQcBall i (hshell (x, v) hv hx))
      (hsupportD i)) hcommon
  choose Mzero hMzero B₀ hB₀ Czero hCzero hrealize using fun i ↦ (hzero i).2
  let Bzero : ι → ℝ≥0 := fun i ↦ ⟨B₀ i, (hB₀ i).le⟩
  have hQ : ContDiffOn ℝ ∞ (projectedStress H.map) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF.contDiffOn hi hrank)
  have hlow (i : ι) : cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
      (projectedStress H.map - fun _ ↦ cubeStress n) < (family i).family.threshold := by
    rw [← (c₀ i).frame_eq]
    exact (c₀ i).Q.2.2
  let Qseed := fun i : ι ↦ (⟨projectedStress H.map, hQ, hlow i⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (family i).family.threshold})
  have hQseed (i : ι) : Qseed i = (c₀ i).Q := Subtype.ext (c₀ i).frame_eq.symm
  have hcov (i : ι) (z : Euclidean 3) (hz : z ∈ parameterCube (patches i).radius) :
      (family i).carrierGradient (Qseed i) 0 z = (patches i).toFun z := by
    rw [hQseed]
    obtain ⟨_, _, _, _, _, _, hsmallA, _⟩ := hcharts anchor hanchor i
    have he := SourceMatching.current_carrierGradient_source_dilation (family i) (c₀ i).Q (Qanchor i)
      hF hrank (hphysical i) (c₀ i).frame_eq (htrans i) hanchor.1 (hanchor.2.trans hcap1)
      (current anchor hanchor i).frame_eq (mem_ball_self (family i).physicalRadius_pos)
      (z := z) (fun j ↦ (hz j).trans (by linarith only [(hP i).1]))
    rw [smul_zero] at he
    apply he.symm.trans (hcovector i _ (hsmallA.trans_le (min_le_right _ _)) ?_ z hz)
    change (current anchor hanchor i).Q.1 0 = cubeStress n
    rw [(current anchor hanchor i).frame_eq, NormalizedFrozenGap.projectedStress_sourceDilation_origin H hanchor.1]
  have hDc (i : ι) : MapsTo (densityCoordinates (family i)) (ball (0 : Euclidean n) (R i) ×ˢ V i)
      (c₀ i).D := fun _ hp ↦ (c₀ i).small_subset ((outputCylinder_spec (hRc i) (hτlead i)).2 (hflow i hp))
  have hcol (j : centers) (q : Euclidean n) (hq : q ∈ ball j.1.1.2 (εcover j))
      (l : Fin (cover.patchCount j.1.1.1)) :
      carrierNullvector (family ⟨j, l⟩) (Qseed ⟨j, l⟩) (col ⟨j, l⟩) (0, cover.roots j.1.1.1 l q) ≠ 0 := by
    let i : ι := ⟨j, l⟩
    let z := cover.roots j.1.1.1 l q
    have hh := (c₀ i).domain_coefficients (hDc i (x := ((0 : Euclidean n), z 0, spectatorCenter z))
      ⟨mem_ball_self (hR i), (hdetector j q hq l).1⟩)
    change (coordinates (adaptedCoordinates (family i).data.adapted)).symm
      (coordinates (adaptedCoordinates (family i).data.adapted) (0, parameter (z 0, spectatorCenter z))) ∈ Ωflow i at hh
    simp only [ContinuousLinearEquiv.symm_apply_apply, parameter_apply, carrierParameters_spectatorCenter] at hh
    rw [hQseed]
    exact ((c₀ i).null_spec _ hh).1
  have hHz : (0 : Euclidean n) ∈ H.domain.chart n :=
    mem_ball_self (H.domain.coreRadius_pos.trans H.domain.coreRadius_lt_chartRadius)
  have hiH : IsImmersionOn H.map (H.domain.chart n) := isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1)
    (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ H.inducedMetric_eq_one x)
  have hkernelSeed (i : ι) : RetainedSpectralGeometry (family i) (Qseed i) (roots i) (ηb i) (r i) (a i) := by
    rw [hQseed]
    exact hkernel i
  have hunitSeed (i : ι) : UnitCarrierOutput (family i) (Qseed i) H.map (row i) (col i)
      (c₀ i).forward (c₀ i).inverse (roots i) (ηb i) (r i) (a i) (r' i) (a' i) (hr' i) (ha' i)
      (hcell i) (hηb i) (2 * (n + 1)) le_rfl := by
    rw [hQseed]
    exact (hzero i).1
  have hseed := NormalizedFrozenGap.initializedFrozenSeedGap_of_retained_normalized_family hDd menu centers
    (projectedStress H.map) hQ hlow H.map row col (fun i ↦ (c₀ i).forward) (fun i ↦ (c₀ i).inverse)
    ηb r a r' a' hηb hr (fun i ↦ (ha' i).trans_le (haa i)) hr' ha' hrr haa hn₅ εcover hcover hdomain hgram
    har' (funext (projectedStress_flatReference_zero H)) rfl (hF.contDiffAt.of_le (by simp))
    (hiH 0 hHz) (H.fullNormalRank 0 hHz)
    (fun j q hq l ↦ hcov ⟨j, l⟩ _ (fun m ↦ (((hDd.2.2.2.2.1 j.1.1.1 l).2.2.1 q (hdomain j hq)).1 m).le))
    (fun j q hq l ↦ (hdetector j q hq l).2) hcol
    hkernelSeed hcell hunitSeed
    zCell L τgraph ρgraph hL hρgraph (fun i ↦ coefficientDomain (roots i) (r i) (6 * a i))
    (fun _ ↦ Subset.rfl) hgraph hworking (fun i ↦ (c₀ i).D) (fun i ↦ (c₀ i).D)
    (fun i ↦ (hDc i).mono_left (houter i)) (fun _ ↦ Subset.rfl)
    (fun i ↦ Ioo (-τlead i) (τlead i)) (fun i ↦ ball ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8))
    (fun i ↦ (c₀ i).inverse_range) (fun i ↦ (c₀ i).initial) (fun i ↦ (c₀ i).forward_inverse)
  change InitializedFrozenSeedGap family Qseed H.map row col (fun i ↦ (c₀ i).forward)
    (fun i ↦ (c₀ i).inverse) roots ηb r' a' hr' ha' hcell hηb zCell L at hseed
  rw [show Qseed = fun i ↦ (c₀ i).Q from funext hQseed] at hseed
  obtain ⟨g, hg, rInner, hrInner, hInnerCell, M, hM, hrμ, hG, hcoercive⟩ :=
    exists_initialized_source_density_limit_coercivity hn family (fun i ↦ (c₀ i).Q) H.map row col
      (fun i ↦ (c₀ i).forward) (fun i ↦ (c₀ i).inverse) roots ηb r' a'
      hr' ha' hcell hηb zCell L hseed hμ hμcell hμa J u₀ Ωsource S Bzero
  let G := NormalAugmentation.globalGap g M
  let κ := min g G
  have hκ : 0 < κ := lt_min hg hG
  obtain ⟨_Cnorm, Bsource, _hCnorm, _hBsource, hcontrol⟩ := exists_selected_source_family_normal_control
    hn H patches hUG hbounded family hP Ωflow hΩ zCell ρc Rc B τlead L Mc row col hKΩ hΩpatch hRc hτlead
    hτRc hL hbuffer hphysical c₀ htrans hMc hforward R hR hRT hRU hRtime V hV hVP hflow hlabel
    D hD roots ηb hηb r a r' a' hr hr' ha' hcell hrr haa har' haR hsupportD houter
    p₀ q₀ ρ τ hρ hτ W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg A ε gap hε hgap
    hfreq Qc Ωsource hQc hΩsource hQcΩ hne hcone hsourceCap hcap1 current δgeometry hδgeometry hgeometry
  obtain ⟨capCarrier, hcapCarrier, hcapCarrierSource, _hcapCarrierOne, hcarrierComparison⟩ := hcontrol κ hκ
  obtain ⟨capImage, hcapImage, hcapImageOne, dImage, coeff₀, hd, _hdsmooth, _hdplateau,
      hcoeff₀, hcoeffSmooth, _hcoeffPlateau, _hjets, _hformula, _hweak, _hadjoint⟩ :=
    RetainedAssembly.NormalizedImage.exists_normalized_image_coefficients H
      (by positivity : 0 < 4 * μ) (by linarith : 4 * μ < 5 * μ)
      (by linarith : 5 * μ < 6 * μ) houterCell hχcoeff hχsupport hχplateau
  obtain ⟨_Bimage, _hBimage, himageTolerance⟩ := exists_supplied_measurement_imageNormal_threshold
    H hμ hμcell houterCell χcoeff hχcoeff hχsupport hχplateau dImage hd
  obtain ⟨capError, hcapError, _hcapErrorOne, himageError⟩ := himageTolerance (κ / 4) (by positivity)
  let cap := min capCarrier (min capImage capError)
  have hcap : 0 < cap := lt_min hcapCarrier (lt_min hcapImage hcapError)
  have hcapSource : cap ≤ sourceCap := (min_le_left _ _).trans hcapCarrierSource
  have hcapCarrier' : cap ≤ capCarrier := min_le_left _ _
  have hcapImage' : cap ≤ capImage := (min_le_right _ _).trans (min_le_left _ _)
  have hcapError' : cap ≤ capError := (min_le_right _ _).trans (min_le_right _ _)
  let coeff := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦
    coeff₀ σ ⟨hσ.1, hσ.2.trans hcapImage'⟩
  have hcoeff : ∀ σ hσ j x, coeff σ hσ j x = χcoeff (centeredTorusRepresentative x) *
      geometricReducedCoefficients (sourceDilation H.map σ) (centeredTorusRepresentative x) j :=
    fun σ hσ ↦ hcoeff₀ σ ⟨hσ.1, hσ.2.trans hcapImage'⟩
  let cur := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ current σ ⟨hσ.1, hσ.2.trans hcapSource⟩
  refine ⟨g, hg, rInner, hrInner, hInnerCell, M, hM, hrμ, hG, cap, hcap,
    hcapImage'.trans hcapImageOne, cur, ?_, coeff, hcoeff,
    fun σ hσ ↦ hcoeffSmooth σ ⟨hσ.1, hσ.2.trans hcapImage'⟩, ?_⟩
  · intro σ hσ i
    obtain ⟨Ψ, hlift, hfwd, hinv, _, _, hframe, hforwardEq, hinvEq, _⟩ :=
      hcharts σ ⟨hσ.1, hσ.2.trans hcapSource⟩ i
    refine ⟨Ψ, hlift, hfwd, hinv, hforwardEq, hinvEq, ?_, ?_⟩
    · rw [← (cur σ hσ i).frame_eq]
      exact hframe.trans_le (min_le_left _ _)
    · intro p hp
      have hdom := (cur σ hσ i).small_subset
        ((outputCylinder_spec (hRc i) (hτlead i)).2 (hflow i (hD i hp)))
      change (cur σ hσ i).inverse (densityCoordinates (family i) p) ∈ _
      rw [show (cur σ hσ i).inverse (densityCoordinates (family i) p) = _ from hinvEq hdom]
      exact hsource i σ ⟨hσ.1, hσ.2.trans (hcapImage'.trans hcapImageOne)⟩ (hD i hp)
  intro σ hσ v hv hpos hinterval hvnorm e eMeasured
  obtain ⟨Vfrozen, hfrozenReal, hzeroCoercive⟩ := hcoercive v hv hinterval
  choose hb₀ hA₀ hs₀ Vzero hVz hAdjz htestz hadjz huniqz hmatch using
    fun i ↦ hrealize i (v i) (hv i) (hpos i) (hinterval i) (hvnorm i)
  have hnormals i (t : Bool) := (hmatch i (Vfrozen i) (hfrozenReal i).1 t).2.2.2.2.2.1
  obtain ⟨hzeroM, hzeroLocal, hzeroGlobal, _, _hexterior⟩ :=
    hzeroCoercive hb₀ hA₀ Vzero (fun i t ↦ hnormals i t _ _ _ _ _)
  obtain ⟨_, hb, hs, hB, Vcurrent, _hVnorm, hVcurrent, _, hmeas⟩ :=
    hcarrierComparison σ ⟨hσ.1, hσ.2.trans hcapCarrier'⟩ v hv hpos hinterval hvnorm
  refine ⟨Vcurrent, fun i ↦ ⟨(hVcurrent i).1, (hVcurrent i).2.1,
    fun Wop ↦ carrierExtensions_eq_of_initialTests (e i) (Vcurrent i) Wop (hVcurrent i).1⟩, ?_, ?_⟩
  · intro i
    have hm := NormalizedMeasurement.supplied_carrier_common_measurement (e i) hμ (ha' i) hμcell
      (hcell i) (hμa i) rfl (fun _ _ ↦ rfl) rfl
    obtain ⟨_, htest, hadjoint⟩ := hm.2.2.2.2.2.2.2.2 (Vcurrent i)
    exact ⟨(htest (hVcurrent i).1).1, (htest (hVcurrent i).1).2, hadjoint (hVcurrent i).2.1⟩
  intro image VcurrentMeas
  let image₀ := fixedPeriodicChannel hμ hμcell (frozenImageArrays (projectedStress H.map 0))
  let VzeroMeas := fun i ↦ restrictCarrier χ (Vzero i)
  have hNzero (i : ι) := realized_normal_eq_of_amplitude_witnesses hn (4 * a' i) (4 * a' i)
    _ _ (hb₀ i true) (hb 1 i) (hs₀ i true) (hs 1 i) (Bzero i) (Bsource i)
    (fun j k ξ is his ↦ hA₀ i true j k ξ is (his.trans (Nat.le_succ _))) (hB 1 i)
    (by simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, ↓reduceIte, u₀]) (Vzero i)
    (hnormals i true _ _ _ _ _)
  have hmeasured : ‖∑ i, (carrierChannel (VcurrentMeas i) ∘L (carrierChannel (VcurrentMeas i)).adjoint -
      carrierChannel (VzeroMeas i) ∘L (carrierChannel (VzeroMeas i)).adjoint)‖ ≤ κ / 4 := by
    have hh := hmeas χ (FixedCutoffs.periodic_norm_le_one hμ hμcell 1)
    simp_rw [← hNzero, ← carrierChannel_restrictCarrier_normal] at hh
    exact hh
  have himage : ‖NormalPerturbation.normal image - NormalPerturbation.normal image₀‖ ≤ κ / 4 := by
    have heq : ProjectedStressFrame.projectedStress H.map 0 = cubeStress n :=
      funext (ProjectedStressFrame.projectedStress_flatReference_zero H)
    dsimp only [image₀]
    rw [heq]
    exact (himageError σ ⟨hσ.1, hσ.2.trans hcapError'⟩ (coeff σ hσ) (hcoeff σ hσ)).2.2.le
  let Acurrent := physicalRow image VcurrentMeas
  let Azero := physicalRow image₀ VzeroMeas
  have hcomparison : ‖NormalPerturbation.normal Acurrent - NormalPerturbation.normal Azero‖ ≤ κ / 2 := by
    dsimp only [Acurrent, Azero, NormalPerturbation.normal]
    rw [physicalRow_normal, physicalRow_normal, add_sub_add_comm, ← Finset.sum_sub_distrib]
    apply (norm_add_le _ _).trans
    exact (add_le_add himage hmeasured).trans (by linarith)
  exact retained_row_half_gaps_of_physical_normal_error image image₀ VcurrentMeas VzeroMeas
    hrInner hInnerCell hg hG hzeroM hzeroLocal hzeroGlobal hcomparison

end JanetCartan.ContinuumNormal.ActualConstruction
