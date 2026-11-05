module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.IncidenceSourceCoercivity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.FiniteDensityCarriers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedDensityActions
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.ExteriorElliptic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CoerciveNormal

/-!
# The inverse of the constructed retained incidence row

Apply the actual source coercivity constructor, then the sharp retained carrier
producer to its returned charts. Equality on the literal test integrals identifies
the bounded carrier with the coercive carrier. The existing elliptic bootstrap
therefore applies to the same normal and the same supplied inner exterior.

Only the original retained seed and geometric projections are inputs. No gap,
operator estimate, regularity conclusion or current-chart existence is assumed.
The original initializer must still supply those geometric projections on its
own retained witnesses. Consumers: positive background, prepared history and
canonical changes (`app:ch_background:prop:bg-inverse`).
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

/-- The energy identity for the canonical right inverse gives the square-norm
estimate used in `app:ch_background:prop:bg-inverse`, for both the constructed
source row and its original-density history continuation. -/
theorem canonical_rightInverse_norm_sq_le
    {n : ℕ} {κ : Type*} [Fintype κ]
    (A : AugmentedInput n κ →L[ℝ] OutputL2 n) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ w, γ * ‖w‖ ^ 2 ≤ ‖A.adjoint w‖ ^ 2) (e : OutputL2 n) :
    ‖CoerciveInverse.rightInverse A e‖ ^ 2 ≤ γ⁻¹ * ‖e‖ ^ 2 := by
  let E := CoerciveInverse.normalOperator A
  have hnormal := CoerciveInverse.normalOperator_gap A hgap
  have henergy : ‖CoerciveInverse.rightInverse A e‖ ^ 2 = inner ℝ e (E.inverse e) := by
    change ‖A.adjoint (E.inverse e)‖ ^ 2 = _
    rw [← CoerciveInverse.inner_normalOperator]
    rw [CoerciveInverse.apply_inverse E hγ hnormal]
  rw [henergy]
  calc
    inner ℝ e (E.inverse e) ≤ ‖e‖ * ‖E.inverse e‖ := real_inner_le_norm _ _
    _ ≤ ‖e‖ * (γ⁻¹ * ‖e‖) := mul_le_mul_of_nonneg_left
      (CoerciveInverse.norm_inverse_apply_le E hγ hnormal e) (norm_nonneg e)
    _ = γ⁻¹ * ‖e‖ ^ 2 := by ring

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

/-- Construct the canonical L² right inverse and all normal-inverse Sobolev
estimates on the row returned by actual retained-incidence coercivity.
The sharp `μ+1` baseline is proved from the original `μ+14` density class;
higher estimates retain one high density norm. Constants, the inner cutoff
and the source cap precede every source scale, density and target. Literal test
uniqueness transfers all analytic estimates to the SAME constructed row.
The returned normalized density carrier retains the current inverse ODE label;
its literal actions identify every supplied realization with this same measured
row, normal inverse and right inverse
(`app:ch_background:prop:bg-inverse`, `app:ch_background:eq:bg-r-inverse`,
`app:ch_background:eq:bg-commutator`). -/
theorem exists_realized_retained_incidence_inverse_estimates
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
    ∃ Cell : ℕ → ℝ, (∀ s, 0 ≤ Cell s) ∧
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
          exteriorChannel (innerCutoff hrInner hInnerCell) w x = 0) ∧
      let Arow := augmentedRow image V (innerCutoff hrInner hInnerCell)
      let E := CoerciveInverse.normalOperator Arow
      let Q₀ := CoerciveInverse.rightInverse Arow
      let S := periodicSobolevScale n (Euclidean n)
      let densityProfile := fun p ↦ ∑ i, cNorm
        (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8)) p (v i)
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
            (1 + densityProfile (s + 1 + (2 * (n + 1) + 14))) * ‖w‖)) ∧
      (∀ s e, e ∈ S.level s → E.inverse e ∈ S.level s ∧
        S.gradeNorm s (E.inverse e) ≤ bootstrapConstant (NormalAugmentation.globalGap g M / 2) Cell s *
            (S.gradeNorm s e + (1 + densityProfile (s + (2 * (n + 1) + 14))) * ‖e‖)) ∧
      let normalizedDensity := fun i ↦ weightNormal
        (normalizedCarrierData (family i) (c₀ i).Q H.map (row i) (col i)
          (c₀ i).forward (c₀ i).inverse (fun _ ↦ 1) hμ hμcell (angular i)
          FixedCutoffs.highFrequency σ)
        (fun p ↦ Real.sqrt (1 + v i (densityFootpoint (family i) (current σ hσ i).inverse p)))
      (∀ i, carrierKernel (eMeasured i) = carrierKernel (normalizedDensity i) ∧
        carrierTestIntegral (eMeasured i) = carrierTestIntegral (normalizedDensity i) ∧
        carrierAdjointIntegral (eMeasured i) = carrierAdjointIntegral (normalizedDensity i)) ∧
      (∀ i f, restrictCarrier χ (Vcurrent i) (carrierInitialTestToLp f) =ᵐ[volume]
        carrierTestIntegral (normalizedDensity i) f.val) ∧
      (∀ i (w : ComplexOutputL2 n), MemLp (carrierAdjointIntegral (normalizedDensity i) w) 2 (carrierMeasure n) ∧
        (restrictCarrier χ (Vcurrent i)).adjoint w =ᵐ[carrierMeasure n]
          carrierAdjointIntegral (normalizedDensity i) w) ∧
      ∀ Vnormalized : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i w, (Vnormalized i).adjoint w =ᵐ[carrierMeasure n]
          carrierAdjointIntegral (normalizedDensity i) w) →
        Vnormalized = (fun i ↦ restrictCarrier χ (Vcurrent i)) ∧
        augmentedRow image Vnormalized (innerCutoff hrInner hInnerCell) = Arow ∧
        (CoerciveInverse.normalOperator
          (augmentedRow image Vnormalized (innerCutoff hrInner hInnerCell))).inverse = E.inverse ∧
        CoerciveInverse.rightInverse
          (augmentedRow image Vnormalized (innerCutoff hrInner hInnerCell)) = Q₀ := by
  classical
  intro angular χ χsrc
  have hn : 0 < n := by omega
  obtain ⟨g, hg, rInner, hrInner, hInnerCell, M, hM, hrμ, hG,
      cap₀, hcap₀, hcap₀1, current₀, hcurrent₀, coeff₀, hcoeff₀, hsmooth₀, hcoercive⟩ :=
    exists_realized_retained_incidence_source_coercivity menu centers hn₅ hDd H hUG hbounded
      Ωflow hΩ zCell ρc Rc B τlead L Mc row col hKΩ hΩpatch hRc hL hbuffer hphysical c₀ htrans
      hBflow hτeq hΩscale hMc hforward R hR hRT hRU hRtime V hV hVP hflow hlabel D hD
      ηb hηb r a r' a' hr hr' ha' hcell hrr haa har' haR hsupportD houter
      p₀ q₀ ρ τ hρ hτ W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg
      A ε gap hε hgap hfreq Qc Ωsource hQc hΩsource hQcΩ hne hcone δgeometry hδgeometry hgeometry
      hkernel hcenter hQcBall εcover hcover hdomain hgram hdetector hρgraph hgraph hworking
      hμ hμcell hμa houterCell χcoeff hχcoeff hχsupport hχplateau
  have hP (i : ι) : (patches i).IsValid c C := (hDd.2.2.2.2.1 i.1.1.1.1 i.2).1
  have hτlead (i : ι) : 0 < τlead i := by
    rw [hτeq i]
    exact div_pos (existenceTime_pos (hRc i) (liftedLowBound_nonneg (family i) (hBflow i))) (by norm_num)
  have hτRc (i : ι) : τlead i ≤ Rc i / 16 := by
    have ht := (existenceTime_le (hRc i) (liftedLowBound_nonneg (family i) (hBflow i))).1
    rw [hτeq i]
    linarith
  obtain ⟨capCarrier, hcapCarrier, _hcapCarrierOne, Cnorm, Cpdo, _hCnorm, hCpdo,
      Bhigh, hBhigh, hcarriers⟩ := exists_finite_retained_source_density_carriers
    H patches hUG hbounded family hP Ωflow hΩ zCell ρc Rc B τlead L Mc row col hKΩ hΩpatch
    hRc hτlead hτRc hL hbuffer hphysical c₀ htrans hMc hforward R hR hRT hRU hRtime
    V hV hVP hflow hlabel D hD roots ηb hηb r a r' a' hr hr' ha' hcell hrr haa har' haR
    hsupportD houter p₀ q₀ ρ τ hρ hτ W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg
    A ε gap hε hgap hfreq δgeometry hδgeometry
    (fun i F hF hi hrank hlow hsmall ↦ (hgeometry i F hF hi hrank hlow hsmall).1)
  let ψ := innerCutoff (n := n) hrInner hInnerCell
  let γ := NormalAugmentation.globalGap g M / 2
  have hγ : 0 < γ := half_pos hG
  obtain ⟨capElliptic, hcapElliptic, _hcapEllipticOne, helliptic⟩ :=
    NormalizedBackground.exists_normalized_row_elliptic_profile_estimates_with_exterior
      («ι» := RetainedIncidenceChannel cover centers) H hn hμ houterCell hχcoeff hχsupport hχplateau ψ
      (innerCutoff_smooth hrInner hInnerCell)
  let Qhigh := fun p ↦ ∑ i, Bhigh i p
  have hQhigh (p : ℕ) : 0 ≤ Qhigh p := Finset.sum_nonneg fun i _ ↦ (hBhigh i p).le
  obtain ⟨Cell, hCell, hest⟩ := helliptic Cpdo (fun i ↦ (hCpdo i).le) Qhigh hQhigh γ hγ
  let cap := min cap₀ (min capCarrier capElliptic)
  have hcap : 0 < cap := lt_min hcap₀ (lt_min hcapCarrier hcapElliptic)
  have hc₀ : cap ≤ cap₀ := min_le_left _ _
  have hcC : cap ≤ capCarrier := (min_le_right _ _).trans (min_le_left _ _)
  have hcE : cap ≤ capElliptic := (min_le_right _ _).trans (min_le_right _ _)
  let current := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ current₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩
  let coeff := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ coeff₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩
  refine ⟨g, hg, rInner, hrInner, hInnerCell, M, hM, hrμ, hG, Cell, hCell,
    cap, hcap, hc₀.trans hcap₀1, current, fun σ hσ ↦ hcurrent₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩,
    coeff, fun σ hσ ↦ hcoeff₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩,
    fun σ hσ ↦ hsmooth₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩, ?_⟩
  intro σ hσ v hv hpos hinterval hvnorm e eMeasured
  obtain ⟨Vcurrent, htest, hmeasured, hnorm, hlocal, hnormal, hgapRow, hexterior⟩ :=
    hcoercive σ ⟨hσ.1, hσ.2.trans hc₀⟩ v hv hpos hinterval hvnorm
  obtain ⟨hsupport, hb, hlow, Vanalytic, hanalytic⟩ :=
    hcarriers σ ⟨hσ.1, hσ.2.trans hcC⟩ (current σ hσ) v hv hpos hinterval hvnorm
  have hopEq : Vanalytic = Vcurrent := by
    funext i
    exact (htest i).2.2 (Vanalytic i) (hanalytic i).2.2.1
  subst Vanalytic
  refine ⟨Vcurrent, htest, hmeasured, hnorm, hlocal, hnormal, hgapRow, hexterior, ?_⟩
  intro Arow E Q₀ S densityProfile
  have hprofile (p : ℕ) : 0 ≤ densityProfile p := Finset.sum_nonneg fun i _ ↦ cNorm_nonneg _ _ _
  have hmono : Monotone densityProfile := fun p q hpq ↦
    Finset.sum_le_sum fun _ _ ↦ cNorm_mono_order hpq
  let amp := fun i ↦ fullReflectedMatrixAmplitude
    (coefficientsOfCarrier (e i) (FixedCutoffs.physical (ha' i) 1))
    (symbolJacobian (family i) (current σ hσ i).Q)
    (symbolInverse (family i) (current σ hσ i).Q (roots i) (ηb i) (r i) (6 * a i))
    (symbolDomain (family i) (current σ hσ i).Q (roots i) (ηb i) (r i) (6 * a i))
    (closedBall (spectatorCenter (roots i)) (a' i / 2))
  have hs (i : ι) : ∀ ξ j k, SupportedInCenteredBox (4 * a' i) (fun z ↦ amp i ξ z j k) :=
    fullReflectedMatrixAmplitude_supportedInCenteredBox _ _ _ _ _ (4 * a' i) (hsupport i)
  have hhigh : ∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
      HasAmplitudeDerivativeBound (fun ξ z ↦ amp i ξ z l j) p (Qhigh p * (1 + densityProfile p)) := by
    intro i p _ l j ξ is his z
    apply ((hanalytic i).2.2.2.2.2.2.2.1 p l j ξ is his z).trans
    apply mul_le_mul
    · exact Finset.single_le_sum (fun k _ ↦ (hBhigh k p).le) (Finset.mem_univ i)
    · exact add_le_add (le_refl (1 : ℝ)) (Finset.single_le_sum
        (fun k _ ↦ cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), zCell k) (L k / 8)) p (v k))
        (Finset.mem_univ i))
    · exact add_nonneg zero_le_one (cNorm_nonneg _ _ _)
    · exact hQhigh p
  have hnormaleq (i : ι) : carrierChannel (Vcurrent i) ∘L (carrierChannel (Vcurrent i)).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn (4 * a' i) (amp i) (hb i) (hs i) (Cpdo i)
          (fun l j ξ is his ↦ hlow i l j ξ is (his.trans (Nat.le_succ _))))) :=
    (hanalytic i).2.2.2.2.2.2.1
  obtain ⟨hreg, hstep, hinverse⟩ := hest σ ⟨hσ.1, hσ.2.trans hcE⟩ (coeff σ hσ)
    (hcoeff₀ σ ⟨hσ.1, hσ.2.trans hc₀⟩) densityProfile hprofile hmono amp hb hlow hhigh
    (fun i ↦ 4 * a' i) Cpdo hs (fun i l j ξ is his ↦ hlow i l j ξ is (his.trans (Nat.le_succ _)))
    Vcurrent hnormaleq hgapRow
  refine ⟨CoerciveInverse.comp_rightInverse Arow hγ hgapRow,
    CoerciveInverse.norm_inverse_le E hγ hnormal, ?_, hreg, hstep, hinverse, ?_⟩
  · intro f
    refine ⟨canonical_rightInverse_norm_sq_le Arow hγ hgapRow f,
      CoerciveInverse.apply_inverse E hγ hnormal f,
      CoerciveInverse.inverse_apply E hγ hnormal f, ?_, ?_⟩
    · rw [CoerciveNormal.rightInverse_exterior_eq]
      exact hexterior _
    · have heq : physicalRow (imageChannel (coeff σ hσ) χ χsrc)
          (fun i ↦ restrictCarrier χ (Vcurrent i)) (Q₀ f).fst +
          exteriorChannel ψ (Q₀ f).snd = f := by
        simpa only [Arow, Q₀, ψ, augmentedRow_apply] using CoerciveInverse.apply_rightInverse Arow hγ hgapRow f
      have hae := Lp.coeFn_add
        (physicalRow (imageChannel (coeff σ hσ) χ χsrc) (fun i ↦ restrictCarrier χ (Vcurrent i)) (Q₀ f).fst)
        (exteriorChannel ψ (Q₀ f).snd)
      rw [heq] at hae
      filter_upwards [hae, hexterior (Q₀ f).snd] with x hx hext
      intro hxcore
      change f x = physicalRow (imageChannel (coeff σ hσ) χ χsrc)
        (fun i ↦ restrictCarrier χ (Vcurrent i)) (Q₀ f).fst x + exteriorChannel ψ (Q₀ f).snd x at hx
      have hz : exteriorChannel ψ (Q₀ f).snd x = 0 := hext hxcore
      rw [hz, add_zero] at hx
      exact hx.symm
  · intro normalizedDensity
    have hflowMeasured (i : ι) : MapsTo (densityCoordinates (family i))
        (closedBall (0 : Euclidean n) (4 * μ) ×ˢ carrierSupport (roots i) (r := a' i))
        (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τlead i)) := by
      rintro ⟨x, z⟩ ⟨hx, hz⟩
      apply hflow i
      apply hD i
      apply (D i).field.ball_subset
      apply hsupportD i
      refine ⟨?_, hz⟩
      have hx₂ : x ∈ closedBall (0 : Euclidean n) (2 * a' i) :=
        closedBall_subset_closedBall (by linarith [hμa i]) hx
      have hxplateau : x ∈ interior {y | FixedCutoffs.physical (ha' i) 1 y = 1} := by
        apply FixedCutoffs.physical_plateau (ha' i) 1
        simpa only [Fin.val_one, Nat.cast_one, one_add_one_eq_two] using hx₂
      have hxone : FixedCutoffs.physical (ha' i) 1 x = 1 :=
        show x ∈ {y | FixedCutoffs.physical (ha' i) 1 y = 1} from interior_subset hxplateau
      apply subset_tsupport
      change FixedCutoffs.physical (ha' i) 1 x ≠ 0
      rw [hxone]
      exact one_ne_zero
    have hactions (i : ι) : carrierKernel (eMeasured i) = carrierKernel (normalizedDensity i) ∧
        carrierTestIntegral (eMeasured i) = carrierTestIntegral (normalizedDensity i) ∧
        carrierAdjointIntegral (eMeasured i) = carrierAdjointIntegral (normalizedDensity i) := by
      have hpatch : Ωflow i ⊆ ball 0 (family i).physicalRadius ×ˢ
          parameterInterior (2 * (patches i).radius) := by
        intro p hp
        exact ⟨(hΩpatch i hp).1.2,
          fun j ↦ ((hΩpatch i hp).2 j).trans (by linarith only [(hP i).1])⟩
      apply retained_chart_weighted_normalized_kernel_and_integrals (hP i) (family i)
        (hΩ i) (hKΩ i) hpatch (hRc i) (hτlead i) (hτRc i) (hbuffer i) H.contDiff
        (fun x hx ↦ H.fullNormalRank x (hUG hx)) (hphysical i) (c₀ i) (htrans i)
        (fun x _ ↦ H.inducedMetric_eq_one x) hμ hμcell (angular i) FixedCutoffs.highFrequency
        ?_ hσ.1 (hσ.2.trans (hc₀.trans hcap₀1)) (current σ hσ i)
        (fun q ↦ Real.sqrt (1 + v i q))
      intro x z η hm hz
      obtain ⟨hs, ht, _⟩ := angularMask_nonzero (roots i)
        (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1 hz
      exact (outputCylinder_spec (hRc i) (hτlead i)).2
        (@hflowMeasured i (centeredTorusRepresentative x, z)
          ⟨FixedCutoffs.physical_tsupport_four hμ 1 (subset_tsupport _ hm),
            ball_subset_closedBall hs, ball_subset_closedBall ht⟩)
    have hadjoint (i : ι) (w : ComplexOutputL2 n) :
        MemLp (carrierAdjointIntegral (normalizedDensity i) w) 2 (carrierMeasure n) ∧
        (restrictCarrier χ (Vcurrent i)).adjoint w =ᵐ[carrierMeasure n]
          carrierAdjointIntegral (normalizedDensity i) w := by
      rw [← (hactions i).2.2]
      exact (hmeasured i).2.2 w
    refine ⟨hactions, ?_, hadjoint, ?_⟩
    · intro i f
      rw [← (hactions i).2.1]
      exact (hmeasured i).1 f
    · intro Vnormalized hnormalized
      have heq : Vnormalized = (fun i ↦ restrictCarrier χ (Vcurrent i)) := by
        funext i
        have hadj : (Vnormalized i).adjoint = (restrictCarrier χ (Vcurrent i)).adjoint := by
          ext1 w
          exact Lp.ext ((hnormalized i w).trans (hadjoint i w).2.symm)
        simpa only [ContinuousLinearMap.adjoint_adjoint] using
          congrArg ContinuousLinearMap.adjoint hadj
      exact ⟨heq, by rw [heq], by rw [heq], by rw [heq]⟩

end JanetCartan.ContinuumInverse
