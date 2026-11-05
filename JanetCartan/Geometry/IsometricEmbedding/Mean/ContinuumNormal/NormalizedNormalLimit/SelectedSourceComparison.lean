module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SelectedSourceNormals
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SeedZeroRealization

/-!
# Literal current and genuine zero normals on the same selected family

Construct the original seed's genuine zero-density carriers from one admitted
positive source, then match their normals to the same comparison PDOs. The
finite quarter-gap is therefore a bound between literal carrier normals.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection FrozenModel RetainedFrozen
open ContinuumNormalReduction TransportSymbol TransportKernel ContinuumRow.CarrierNormalRealization
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.RetainedRowGeometry
open CarrierVariation.FamilyInputs.PositiveReference CarrierVariation.FamilyInputs.WideDensity
open PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude NormalizedBackground.SourceGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2 ProjectedStressFrame

/-- On the SAME supplied normalized family, construct both current and
genuine zero-density carriers and prove their normal sum differs by at most
a quarter of the requested gap. The zero carriers are actual bounded
realizations with literal tests and adjoints. Their normals match the exact
comparison amplitudes by dense-test witness independence. All constants
precede the gap and one cap precedes source scale and the original `μ+14`
densities. Common measurement preserves the same bound. No row-operator norm
convergence or identification with the origin-frozen density is used.
Consumers: normalized normal coercivity and `SourceInverse`
(`app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`, `bg-uniform-normalized`). -/
theorem exists_selected_source_family_normal_comparison :
  ∀
    {n : ℕ} {ι : Type} [Fintype ι] (hn : 0 < n) (H : FlatReference n)
    (P : ι → Patch n) {U : Set (Euclidean n)} {hU : IsOpen U}
    (_hUG : U ⊆ H.domain.chart n) (_hbounded : Bornology.IsBounded U)
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    {c C : ℝ} (_hP : ∀ i, (P i).IsValid c C)
    (Ωflow : ι → Set (Euclidean n × Euclidean 3)) (_hΩ : ∀ i, IsOpen (Ωflow i))
    (zCell : ι → Euclidean 3) (ρc Rc B τlead L Mc : ι → ℝ) (row col : ι → Fin n)
    (_hKΩ : ∀ i, closedBall ((0 : Euclidean n), zCell i) (ρc i) ⊆ Ωflow i)
    (_hΩpatch : ∀ i, Ωflow i ⊆ (U ∩ ball 0 (T i).physicalRadius) ×ˢ
      parameterInterior (3 * (P i).radius / 2))
    (_hRc : ∀ i, 0 < Rc i) (_hτlead : ∀ i, 0 < τlead i)
    (_hτRc : ∀ i, τlead i ≤ Rc i / 16) (_hL : ∀ i, 0 < L i)
    (_hbuffer : ∀ i, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i))
      (closedBall ((0 : Euclidean n), zCell i) (ρc i)))
    (_hphysical : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (c₀ : (i : ι) → Chart (T i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i) H.map)
    (_htrans : ∀ i q, q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (c₀ i).Q.1 (c₀ i).Q.2.1).hp q,
        (T i).data.adapted.normal⟫_ℝ ≠ 0)
    (_hMc : ∀ i, 0 < Mc i)
    (_hforward : ∀ i, cNorm (Icc (-τlead i) (τlead i) ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) 1 (c₀ i).forward ≤ Mc i)
    (R : ι → ℝ) (_hR : ∀ i, 0 < R i) (_hRT : ∀ i, R i ≤ (T i).physicalRadius)
    (_hRU : ∀ i, ball (0 : Euclidean n) (R i) ⊆ U)
    (_hRtime : ∀ i, R i ≤ L i / (64 * Mc i))
    (V : ι → Set CarrierParameter) (_hV : ∀ i, IsOpen (V i))
    (_hVP : ∀ i, V i ⊆ parameter ⁻¹' parameterInterior (3 * (P i).radius / 2))
    (_hflow : ∀ i, MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) (R i) ×ˢ V i)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τlead i)))
    (_hlabel : ∀ i p, p ∈ ball (0 : Euclidean n) (R i) ×ˢ V i →
      (densityCoordinates (T i) p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 64))
    (D : ι → CoefficientNormCharts n)
    (_hD : ∀ i, (D i).field.region ⊆ ball (0 : Euclidean n) (R i) ×ˢ V i)
    (z₀ : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1)) (hηb : ∀ i, ηb i ≠ 0)
    (r a r' a' : ι → ℝ) (_hr : ∀ i, 0 < r i) (hr' : ∀ i, 0 < r' i)
    (ha' : ∀ i, 0 < a' i) (hcell : ∀ i, 4 * a' i < 1 / 2)
    (_hrr : ∀ i, r' i ≤ r i) (_haa : ∀ i, a' i ≤ a i)
    (_har' : ∀ i, a' i ≤ r' i) (_haR : ∀ i, 6 * a i < (T i).family.radius)
    (_hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (ha' i) 1) ×ˢ
      carrierSupport (z₀ i) (r := a' i) ⊆ (D i).field.carrier)
    (_houter : ∀ i, coefficientDomain (z₀ i) (r i) (6 * a i) ⊆
      ball (0 : Euclidean n) (R i) ×ˢ V i)
    (p₀ : ι → InputVariables n) (q₀ : ι → Variables n × Euclidean 2)
    (ρ τ : ι → ℝ) (_hρ : ∀ i, 0 < ρ i) (_hτ : ∀ i, 0 < τ i)
    (W Bi : ι → Set (InputVariables n)) (_hW : ∀ i, IsOpen (W i))
    (_hKiW : ∀ i, closedBall (p₀ i) (ρ i) ⊆ W i)
    (_hBi : ∀ i, IsCompact (Bi i)) (_hWBi : ∀ i, W i ⊆ Bi i)
    (_hBiDom : ∀ i, Bi i ⊆ symbolInputDomain (z₀ i) (ηb i) (r i) (6 * a i))
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
    {sourceCap : ℝ} (_hsourceCap : 0 < sourceCap) (_hcap1 : sourceCap ≤ 1)
    (current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) sourceCap → (i : ι) →
      Chart (T i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
        ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i)
        (sourceDilation H.map σ))
    (δgeometry : ι → ℝ) (_hδgeometry : ∀ i, 0 < δgeometry i)
    (_hgeometry : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < (δgeometry i) →
        let QF : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (T i).family.threshold} := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (RetainedSpectralGeometry (T i) QF (z₀ i) (ηb i) (r i) (a i) ∧
        closedBall (q₀ i) (2 * (τ i)) ⊆ symbolDomain (T i) QF (z₀ i) (ηb i) (r i) (6 * (a i)) ∧
        MapsTo (inverseCoordinates (symbolInverse (T i) QF (z₀ i) (ηb i) (r i) (6 * (a i))))
          (closedBall (q₀ i) (2 * (τ i))) (closedBall (p₀ i) (ρ i)) ∧
        (∀ p ∈ closedBall (p₀ i) (ρ i), ‖(A i).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition (T i) QF)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ (Bi i), (gap i) ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
          (transportPosition (T i) QF) p) ∧
        (closure (augmentedTransportGradient (transportPosition (T i) QF) ''
          conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i)) ∩ {p | p.1.2.2 ≠ 0} ⊆
            symbolDomain (T i) QF (z₀ i) (ηb i) (r i) (6 * (a i))) ∧
        (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition (T i) QF) ''
            conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i)) → (x, v) ∈ closedBall (q₀ i) (τ i)) ∧
        (∀ p ∈ symbolDomain (T i) QF (z₀ i) (ηb i) (r i) (6 * (a i)),
          ‖(symbolInverse (T i) QF (z₀ i) (ηb i) (r i) (6 * (a i)) p).2‖ ≤ 2 * ‖p.1.2.2‖)) ∧
      (let u := symbolInverse (T i) QF (z₀ i) (ηb i) (r i) (6 * (a i))
      (Ωsource i) ⊆ symbolDomain (T i) QF (z₀ i) (ηb i) (r i) (6 * (a i)) ∧
      ContDiffOn ℝ ∞ u (Ωsource i) ∧ MapsTo (inverseCoordinates u) (Qc i) (closedBall (p₀ i) (ρ i)) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) (Ωsource i) (closedBall (p₀ i) (ρ i)) ∧
      (∀ q ∈ (Ωsource i), transportAveragedGradient (transportPosition (T i) QF)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall (p₀ i) (ρ i)), ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition (T i) QF)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ (Bi i), (gap i) ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (transportPosition (T i) QF) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (transportPosition (T i) QF)) (W i) ∧
      EqOn (symbolJacobian (T i) QF)
        (transportAbsoluteJacobian (adaptedSliceCoordinates (T i)) (transportPosition (T i) QF)) (W i) ∧
      InjOn (augmentedTransportGradient (transportPosition (T i) QF)) (closedBall (p₀ i) (ρ i)) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i),
        scaleInput (‖(ηb i)‖ / ‖p.2.2‖) p ∈ (closedBall (p₀ i) (ρ i)) ∧
        transportAveragedGradient (transportPosition (T i) QF) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition (T i) QF) p) ∈ (Qc i) ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (transportPosition (T i) QF) p‖) p ∈ (closedBall (p₀ i) (ρ i)) ∧
        inverseCoordinates u (augmentedTransportGradient (transportPosition (T i) QF) p) = p) ∧
      (closure (augmentedTransportGradient (transportPosition (T i) QF) ''
        conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i)) ∩ {q | q.1.2.2 ≠ 0} ⊆ (Ωsource i))) ∧
      (let u := frozenSymbolInverse (T i) QF (z₀ i) (ηb i) (r i) (6 * (a i))
      (Ωsource i) ⊆ frozenSymbolDomain (T i) QF (z₀ i) (ηb i) (r i) (6 * (a i)) ∧
      ContDiffOn ℝ ∞ u (Ωsource i) ∧ MapsTo (inverseCoordinates u) (Qc i) (closedBall (p₀ i) (ρ i)) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) (Ωsource i) (closedBall (p₀ i) (ρ i)) ∧
      (∀ q ∈ (Ωsource i), transportAveragedGradient (normalizedTransportPosition (T i) QF 0)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall (p₀ i) (ρ i)), ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition (T i) QF 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ (Bi i), (gap i) ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (normalizedTransportPosition (T i) QF 0) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (normalizedTransportPosition (T i) QF 0)) (W i) ∧
      EqOn (frozenKernelJacobian (T i) QF)
        (transportAbsoluteJacobian (adaptedSliceCoordinates (T i)) (normalizedTransportPosition (T i) QF 0)) (W i) ∧
      InjOn (augmentedTransportGradient (normalizedTransportPosition (T i) QF 0)) (closedBall (p₀ i) (ρ i)) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i),
        scaleInput (‖(ηb i)‖ / ‖p.2.2‖) p ∈ (closedBall (p₀ i) (ρ i)) ∧
        transportAveragedGradient (normalizedTransportPosition (T i) QF 0) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (normalizedTransportPosition (T i) QF 0) p) ∈ (Qc i) ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (normalizedTransportPosition (T i) QF 0) p‖) p ∈ (closedBall (p₀ i) (ρ i)) ∧
        inverseCoordinates u (augmentedTransportGradient (normalizedTransportPosition (T i) QF 0) p) = p) ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition (T i) QF 0) ''
        conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i)) ∩ {q | q.1.2.2 ≠ 0} ⊆ (Ωsource i)))),
    let Qcurrent : (i : ι) → ℝ → {QF : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ QF U ∧ cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (QF - fun _ ↦ cubeStress n) < (T i).family.threshold} := fun i σ ↦ if hσ : σ ∈ Ioc (0 : ℝ) sourceCap
      then (current σ hσ i).Q else (c₀ i).Q
    let μ := 2 * (n + 1)
    let angular := fun i ↦ angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1
    let d := fun i σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData (T i) (c₀ i).Q H.map (row i) (col i) (c₀ i).forward (c₀ i).inverse (fun _ ↦ 1)
        (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency σ) (FixedCutoffs.physical (ha' i) 1)
    let J := fun i σ ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
      (normalizedTransportPosition (T i) (c₀ i).Q σ)
    let u := fun i σ ↦ if σ = 0 then frozenSymbolInverse (T i) (c₀ i).Q (z₀ i) (ηb i) (r i) (6 * a i)
      else symbolInverse (T i) (Qcurrent i σ) (z₀ i) (ηb i) (r i) (6 * a i)
    let S := fun i ↦ closedBall (spectatorCenter (z₀ i)) (a' i / 2)
    let b := fun i σ (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      fullReflectedMatrixAmplitude
        {d i σ with normal := fun p ↦ Real.sqrt (1 + v
          (sourceDensityFootpointExtension (T i) (c₀ i).inverse (σ, p))) • (d i σ).normal p}
        (J i σ) (u i σ) (Ωsource i) (S i)
    let eZero : ι → (Euclidean (n - 1) × Euclidean 3 → ℝ) → CarrierData n (embeddingDimension n) :=
      fun (i : ι) (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      SourceDensityLimitRealization.weightNormal (n := n) (N := embeddingDimension n)
        (normalizedCarrierData (T i) (c₀ i).Q H.map (row i) (col i) (c₀ i).forward (c₀ i).inverse
          (fun _ ↦ 1) (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency 0)
        (fun p : Euclidean n × CarrierParameter ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension (T i) (c₀ i).inverse (0, p))))
    ∃ Cnorm Bsource Mzero : ι → ℝ,
    (∀ i, 0 < Cnorm i) ∧ (∀ i, 0 < Bsource i) ∧ (∀ i, 0 ≤ Mzero i) ∧
    ∀ targetGap > (0 : ℝ),
    let tol := targetGap / (4 * ((Fintype.card ι : ℝ) + 1))
    ∃ cap > (0 : ℝ), ∃ hcapSource : cap ≤ sourceCap, cap ≤ 1 ∧
    ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap),
    ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4))) →
      (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4) → 0 < 1 + v i q) →
      (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8) →
        1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8)) (μ + 14) (v i) ≤ 1) →
    let cσ := current σ ⟨hσ.1, hσ.2.trans hcapSource⟩
    let e : ι → CarrierData n (embeddingDimension n) := fun i ↦
      data (T i) (cσ i).Q (sourceDilation H.map σ) (row i) (col i) (cσ i).forward (cσ i).inverse
        (fun q ↦ positiveDensityAmplitude σ (v i q)) (ha' i) (hcell i) (angular i)
        FixedCutoffs.highFrequency
    let pair := fun (t : Fin 2) i ↦ b i (![σ, 0] t) (v i)
    (∀ i j k, HasAmplitudeDerivativeBound (fun ξ z ↦ pair 0 i ξ z j k - pair 1 i ξ z j k) μ tol) ∧
    ∃ hb : ∀ t i, ContDiff ℝ ∞ (Function.uncurry (pair t i)),
    ∃ hs : ∀ t i ξ j k, SupportedInCenteredBox (4 * a' i) (fun z ↦ pair t i ξ z j k),
    ∃ hB : ∀ t i j k, HasAmplitudeDerivativeBound (fun ξ z ↦ pair t i ξ z j k) μ (Bsource i),
    let Aop := fun t i ↦ vectorTwoPositionL2Operator hn (4 * a' i) (pair t i) (hb t i) (hs t i)
      (Bsource i) (hB t i)
    let Nop := fun t i ↦ realOutputCompression (transferOperator (Aop t i))
    ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i, ‖Vop i‖ ≤ Real.sqrt ((n : ℝ) ^ (2 : ℕ) * (fixedBoxAmplitudeConstant n (4 * a' i) * Cnorm i))) ∧
      (∀ i,
        (∀ f : carrierInitialTestSpace n, Vop i (carrierInitialTestToLp f) =ᵐ[volume]
          carrierTestIntegral (e i) f.val) ∧
        (∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
          (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
        carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint = Nop 0 i ∧
        ‖carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint - Nop 1 i‖ ≤ tol) ∧
      (∑ i, ‖carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint - Nop 1 i‖) ≤ targetGap / 4 ∧
      (∀ χ : C(Torus n, ℝ), ‖χ‖ ≤ 1 →
        ‖∑ i, (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i)) ∘L
          (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i))).adjoint -
          cutoffMultiplier χ ∘L Nop 1 i ∘L cutoffMultiplier χ)‖ ≤ targetGap / 4) ∧
      ∃ Vzero : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i, ‖Vzero i‖ ≤ Mzero i ∧ ‖(Vzero i).adjoint‖ ≤ Mzero i) ∧
        (∀ i,
          (∀ f : carrierInitialTestSpace n,
            Vzero i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (eZero i (v i)) f.val) ∧
          (∀ f : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (eZero i (v i)) f) 2 (carrierMeasure n) ∧
            (Vzero i).adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral (eZero i (v i)) f) ∧
          (∀ Wzero : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ f : carrierInitialTestSpace n,
              Wzero (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (eZero i (v i)) f.val) →
              Wzero = Vzero i) ∧
          carrierChannel (Vzero i) ∘L (carrierChannel (Vzero i)).adjoint = Nop 1 i) ∧
        (∑ i, ‖carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint -
          carrierChannel (Vzero i) ∘L (carrierChannel (Vzero i)).adjoint‖) ≤ targetGap / 4 ∧
        ∀ χ : C(Torus n, ℝ), ‖χ‖ ≤ 1 →
          ‖∑ i, (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i)) ∘L
            (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i))).adjoint -
            carrierChannel (CommonMeasurement.restrictCarrier χ (Vzero i)) ∘L
            (carrierChannel (CommonMeasurement.restrictCarrier χ (Vzero i))).adjoint)‖ ≤ targetGap / 4 := by
  intro n ι instFintype hn H P U hU hUG hbounded T c C hP Ωflow hΩ zCell ρc Rc B τlead L Mc row col
    hKΩ hΩpatch hRc hτlead hτRc hL hbuffer hphysical c₀ htrans hMc hforward R hR hRT hRU hRtime V hV
    hVP hflow hlabel D hD z₀ ηb hηb r a r' a' hr hr' ha' hcell hrr haa har' haR hsupportD houter p₀
    q₀ ρ τ hρ hτ W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg A ε gap hε hgap hfreq Qc
    Ωsource hQc hΩsource hQcΩ hne hcone sourceCap hsourceCap hcap1 current δgeometry hδgeometry
    hgeometry
  classical
  intro Qcurrent μ angular d J u S b eZero
  obtain ⟨Cnorm, Bsource, hCnorm, hBsource, hpositive⟩ :=
    exists_selected_source_family_normal_control hn H P hUG hbounded T hP Ωflow hΩ
      zCell ρc Rc B τlead L Mc row col hKΩ hΩpatch hRc hτlead hτRc hL hbuffer hphysical
      c₀ htrans hMc hforward R hR hRT hRU hRtime V hV hVP hflow hlabel D hD z₀ ηb hηb
      r a r' a' hr hr' ha' hcell hrr haa har' haR hsupportD houter p₀ q₀ ρ τ hρ hτ
      W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg A ε gap hε hgap hfreq
      Qc Ωsource hQc hΩsource hQcΩ hne hcone hsourceCap hcap1 current δgeometry hδgeometry hgeometry
  obtain ⟨εgeometry, hεgeometry, hεgeometry_le⟩ :=
    (finite_range δgeometry).isCompact.exists_forall_le' continuousOn_id
      (by rintro x ⟨i, rfl⟩; exact hδgeometry i)
  obtain ⟨admissionCap, hadmissionCap, _hadmissionCap1, hadmit⟩ :=
    SourceMatching.exists_joint_stress_scale_interval H hbounded hεgeometry
  let anchor := min admissionCap sourceCap / 2
  have hanchor : 0 < anchor := half_pos (lt_min hadmissionCap hsourceCap)
  have hanchorSource : anchor ≤ sourceCap :=
    (half_le_self (lt_min hadmissionCap hsourceCap).le).trans (min_le_right _ _)
  have hanchorAdmission : anchor ≤ admissionCap :=
    (half_le_self (lt_min hadmissionCap hsourceCap).le).trans (min_le_left _ _)
  have hanchorMem : anchor ∈ Ioc (0 : ℝ) sourceCap := ⟨hanchor, hanchorSource⟩
  let ca := current anchor hanchorMem
  have hgeom (i : ι) := by
    obtain ⟨hiσ, hrankσ, hframeSmooth, hsmall⟩ := hadmit anchor hanchor hanchorAdmission
    have hsmallCell : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress (sourceDilation H.map anchor) - fun _ ↦ cubeStress n) < δgeometry i := by
      apply ((cNorm_mono_set_of_contDiffAt ((hphysical i).trans subset_closure)
        hbounded.isCompact_closure ?_).trans_lt hsmall).trans_le (hεgeometry_le _ ⟨i, rfl⟩)
      exact fun x hx ↦ ((hframeSmooth x hx).sub contDiffAt_const).of_le (by simp)
    have hFσ : ContDiffOn ℝ ∞ (sourceDilation H.map anchor) U :=
      (contDiff_sourceDilation H.contDiff).contDiffOn
    have hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress (sourceDilation H.map anchor) - fun _ ↦ cubeStress n) <
        (T i).family.threshold := by
      rw [← (ca i).frame_eq]
      exact (ca i).Q.2.2
    have hg := hgeometry i (sourceDilation H.map anchor) hFσ hiσ hrankσ hlow hsmallCell
    have hQ : (⟨projectedStress (sourceDilation H.map anchor),
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hFσ hiσ hrankσ), hlow⟩ :
        {QF : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ QF U ∧
          cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (QF - fun _ ↦ cubeStress n) < (T i).family.threshold}) = (ca i).Q :=
      Subtype.ext (ca i).frame_eq.symm
    dsimp only at hg
    rw [hQ] at hg
    exact hg
  have hi : IsImmersionOn H.map U := isImmersionOn_of_isIsometricOn
    (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ H.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUG hx)
  have hzeroCell (i : ι) := by
    obtain ⟨hbase, _hcur, hfrozen⟩ := hgeom i
    obtain ⟨hspectral, hout, hrange, _hhalfCurrent, _hJcurrent, _hbufferCurrent, hshell, _hupper⟩ := hbase
    obtain ⟨hc, _hs, _hrange, _hnormalized, _heq, hhalf, hJ, _hJs, _hJeq, _hinj,
      _hscale, _hmask, hpunct⟩ := hfrozen
    exact exists_retained_seed_zero_density_realization_of_source
      (hP i) (T i) (hΩ i) (hKΩ i) (hΩpatch i) (hRc i) (hτlead i) (hτRc i) (hbuffer i)
      H.contDiff hi hrank (hphysical i) (c₀ i) (htrans i) (fun x _ ↦ H.inducedMetric_eq_one x)
      (hL i) (hMc i) (hR i) (hforward i) (hRT i) (hRU i) (hRtime i) (hV i) (hVP i)
      (hflow i) (hlabel i) (D i) (hD i) (hηb i) (hr i) (hr' i) (ha' i) (hrr i) (haa i)
      (har' i) (hcell i) (houter i) (ca i).Q hanchor (hanchorSource.trans hcap1) (ca i).frame_eq
      hspectral (p₀ i) (q₀ i) (hρ i) (hτ i) (hW i) (hKiW i) (hBi i) (hWBi i) (hBiDom i)
      hout hrange hshell (hIt i) (hIIt i) (hsegT i) (hseg i) (A i) (hgap i) (hε i)
      (fun p hp ↦ hfreq i p (hWBi i (hKiW i hp))) (hfoot i)
      hhalf (fun p hp ↦ hJ p (hWBi i (hKiW i hp))) (hsupportD i) hc hpunct
  choose Mzero hMzero Bzero hBzero hzero using hzeroCell
  refine ⟨Cnorm, Bsource, Mzero, hCnorm, hBsource, hMzero, ?_⟩
  intro targetGap htargetGap tol
  obtain ⟨cap, hcap, hcapSource, hcapOne, hposFamily⟩ := hpositive targetGap htargetGap
  refine ⟨cap, hcap, hcapSource, hcapOne, ?_⟩
  intro σ hσ v hv hpos hinterval hvnorm cσ e pair
  obtain ⟨hamp, hb, hs, hB, Vop, hVop, hprops, hsum, hmeas⟩ :=
    hposFamily σ hσ v hv hpos hinterval hvnorm
  refine ⟨hamp, hb, hs, hB, ?_⟩
  intro Aop Nop
  choose hbZero hAZero hsZero Vzero hzprops using
    fun i ↦ hzero i (v i) (hv i) (hpos i) (hinterval i) (hvnorm i) true
  have hzeroNormal (i : ι) :
      carrierChannel (Vzero i) ∘L (carrierChannel (Vzero i)).adjoint = Nop 1 i := by
    obtain ⟨_hV, _hAdj, _htest, _hadj, _huniq, _hfrozen, _hnormal, hconsumer⟩ := hzprops i
    have hu0 : u i 0 = frozenSymbolInverse (T i) (c₀ i).Q (z₀ i) (ηb i) (r i) (6 * a i) := by
      dsimp only [u]
      exact ite_eq_left rfl
    let bz := fullReflectedMatrixAmplitude
      {d i 0 with normal := fun p ↦ Real.sqrt (1 + v i
        (sourceDensityFootpointExtension (T i) (c₀ i).inverse (0, p))) • (d i 0).normal p}
      (J i 0) (frozenSymbolInverse (T i) (c₀ i).Q (z₀ i) (ηb i) (r i) (6 * a i))
      (Ωsource i) (S i)
    have hpairZero : pair 1 i = bz := by
      change b i (![σ, 0] (1 : Fin 2)) (v i) = bz
      rw [show ![σ, 0] (1 : Fin 2) = 0 from rfl]
      exact congrArg (fun inv ↦ fullReflectedMatrixAmplitude
        {d i 0 with normal := fun p ↦ Real.sqrt (1 + v i
          (sourceDensityFootpointExtension (T i) (c₀ i).inverse (0, p))) • (d i 0).normal p}
        (J i 0) inv (Ωsource i) (S i)) hu0
    have hb0 : ContDiff ℝ ∞ (Function.uncurry bz) := hpairZero ▸ hb 1 i
    have hs0 : ∀ ξ j k, SupportedInCenteredBox (4 * a' i) (fun z ↦ bz ξ z j k) :=
      hpairZero ▸ hs 1 i
    have hB0 : ∀ j k, HasAmplitudeDerivativeBound (fun ξ z ↦ bz ξ z j k) μ (Bsource i) :=
      hpairZero ▸ hB 1 i
    have hn0 := hconsumer (4 * a' i) (Bsource i) hb0 hs0 hB0
    exact SourceDensityLimitRealization.realized_normal_eq_of_amplitude_witnesses hn
      (4 * a' i) (4 * a' i) bz (pair 1 i) hb0 (hb 1 i) hs0 (hs 1 i)
      (Bsource i) (Bsource i) hB0 (hB 1 i) hpairZero.symm (Vzero i) hn0

  refine ⟨Vop, hVop, hprops, hsum, hmeas, Vzero, ?_, ?_, ?_, ?_⟩
  · exact fun i ↦ ⟨(hzprops i).1, (hzprops i).2.1⟩
  · exact fun i ↦ ⟨(hzprops i).2.2.1, (hzprops i).2.2.2.1,
      (hzprops i).2.2.2.2.1, hzeroNormal i⟩
  · simpa only [hzeroNormal] using hsum
  · intro χ hχ
    simpa only [CommonMeasurement.carrierChannel_restrictCarrier_normal, hzeroNormal] using hmeas χ hχ

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
