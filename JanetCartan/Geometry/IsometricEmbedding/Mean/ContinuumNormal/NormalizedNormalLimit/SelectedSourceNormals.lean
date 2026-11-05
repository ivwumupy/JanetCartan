module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SelectedSourceControl
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.RetainedNormal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.FiniteDensityCarriers

/-!
# Literal positive-source normals on the supplied selected family

Construct the bounded carriers for the supplied source charts and identify their
literal normals with the normalized PDO comparison. All original selector
witnesses are retained; the cap and absolute constants precede source scale and
density. The genuine zero-source bounded realization is a separate producer.
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

/-- Construct the actual current carriers on the supplied normalized charts
and prove the quarter-gap comparison with the genuine zero-source reflected
PDO. The geometric callback is exactly the full current/frozen output of
`exists_finite_incidence_comparison_inputs`. The original `L/8` density class,
`μ+14` reserve, both divided footpoints, masks and spectator measures remain
unchanged. The fixed-family `FiniteDensityCarriers` producer supplies the
operators and their literal adjoints; dense-test PDO uniqueness transfers their
normal identities to the independently proved comparison bounds. No row-norm
continuity or zero-scale application of positive-source matching is used.
The final bound is for the literal commonly restricted positive-source normals.

Consumer: actual normalized coercivity, then `SourceInverse`. The genuine
zero-source carrier identity remains with `SourceDensityLimitRealization`
(`app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`, `bg-uniform-normalized`). -/
theorem exists_selected_source_family_normal_control
    {n : ℕ} {ι : Type} [Fintype ι] (hn : 0 < n) (H : FlatReference n)
    (P : ι → Patch n) {U : Set (Euclidean n)} {hU : IsOpen U}
    (hUG : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    (Ωflow : ι → Set (Euclidean n × Euclidean 3)) (hΩ : ∀ i, IsOpen (Ωflow i))
    (zCell : ι → Euclidean 3) (ρc Rc B τlead L Mc : ι → ℝ) (row col : ι → Fin n)
    (hKΩ : ∀ i, closedBall ((0 : Euclidean n), zCell i) (ρc i) ⊆ Ωflow i)
    (hΩpatch : ∀ i, Ωflow i ⊆ (U ∩ ball 0 (T i).physicalRadius) ×ˢ
      parameterInterior (3 * (P i).radius / 2))
    (hRc : ∀ i, 0 < Rc i) (hτlead : ∀ i, 0 < τlead i)
    (hτRc : ∀ i, τlead i ≤ Rc i / 16) (hL : ∀ i, 0 < L i)
    (hbuffer : ∀ i, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i))
      (closedBall ((0 : Euclidean n), zCell i) (ρc i)))
    (hphysical : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (c₀ : (i : ι) → Chart (T i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i) H.map)
    (htrans : ∀ i q, q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (c₀ i).Q.1 (c₀ i).Q.2.1).hp q,
        (T i).data.adapted.normal⟫_ℝ ≠ 0)
    (hMc : ∀ i, 0 < Mc i)
    (hforward : ∀ i, cNorm (Icc (-τlead i) (τlead i) ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) 1 (c₀ i).forward ≤ Mc i)
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRT : ∀ i, R i ≤ (T i).physicalRadius)
    (hRU : ∀ i, ball (0 : Euclidean n) (R i) ⊆ U)
    (hRtime : ∀ i, R i ≤ L i / (64 * Mc i))
    (V : ι → Set CarrierParameter) (hV : ∀ i, IsOpen (V i))
    (hVP : ∀ i, V i ⊆ parameter ⁻¹' parameterInterior (3 * (P i).radius / 2))
    (hflow : ∀ i, MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) (R i) ×ˢ V i)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τlead i)))
    (hlabel : ∀ i p, p ∈ ball (0 : Euclidean n) (R i) ×ˢ V i →
      (densityCoordinates (T i) p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 64))
    (D : ι → CoefficientNormCharts n)
    (hD : ∀ i, (D i).field.region ⊆ ball (0 : Euclidean n) (R i) ×ˢ V i)
    (z₀ : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1)) (hηb : ∀ i, ηb i ≠ 0)
    (r a r' a' : ι → ℝ) (hr : ∀ i, 0 < r i) (hr' : ∀ i, 0 < r' i)
    (ha' : ∀ i, 0 < a' i) (hcell : ∀ i, 4 * a' i < 1 / 2)
    (hrr : ∀ i, r' i ≤ r i) (haa : ∀ i, a' i ≤ a i)
    (har' : ∀ i, a' i ≤ r' i) (haR : ∀ i, 6 * a i < (T i).family.radius)
    (hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (ha' i) 1) ×ˢ
      carrierSupport (z₀ i) (r := a' i) ⊆ (D i).field.carrier)
    (houter : ∀ i, coefficientDomain (z₀ i) (r i) (6 * a i) ⊆
      ball (0 : Euclidean n) (R i) ×ˢ V i)
    (p₀ : ι → InputVariables n) (q₀ : ι → Variables n × Euclidean 2)
    (ρ τ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hτ : ∀ i, 0 < τ i)
    (W Bi : ι → Set (InputVariables n)) (hW : ∀ i, IsOpen (W i))
    (hKiW : ∀ i, closedBall (p₀ i) (ρ i) ⊆ W i)
    (hBi : ∀ i, IsCompact (Bi i)) (hWBi : ∀ i, W i ⊆ Bi i)
    (hBiDom : ∀ i, Bi i ⊆ symbolInputDomain (z₀ i) (ηb i) (r i) (6 * a i))
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
    {sourceCap : ℝ} (hsourceCap : 0 < sourceCap) (hcap1 : sourceCap ≤ 1)
    (current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) sourceCap → (i : ι) →
      Chart (T i) (Ωflow i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
        ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i)
        (sourceDilation H.map σ))
    (δgeometry : ι → ℝ) (hδgeometry : ∀ i, 0 < δgeometry i)
    (hgeometry : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
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
        conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i)) ∩ {q | q.1.2.2 ≠ 0} ⊆ (Ωsource i)))) :
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
    ∃ Cnorm Bsource : ι → ℝ, (∀ i, 0 < Cnorm i) ∧ (∀ i, 0 < Bsource i) ∧
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
      ∀ χ : C(Torus n, ℝ), ‖χ‖ ≤ 1 →
        ‖∑ i, (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i)) ∘L
          (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i))).adjoint -
          cutoffMultiplier χ ∘L Nop 1 i ∘L cutoffMultiplier χ)‖ ≤ targetGap / 4 := by
  classical
  intro Qcurrent μ angular d J u S b
  have hKBi (i : ι) : closedBall (p₀ i) (ρ i) ⊆ Bi i := (hKiW i).trans (hWBi i)
  have hWinput (i : ι) := (hWBi i).trans (hBiDom i)
  have hend (i : ι) (side : Bool) : MapsTo (densityEndpoint side) (W i) (D i).field.region := by
    have hh : MapsTo (densityEndpoint side) (W i) (D i).field.carrier := by
      intro p hp
      cases side
      · simpa only [densityEndpoint, Bool.false_eq_true, ↓reduceIte, transportSegmentInput_apply,
          one_smul, add_sub_cancel] using hseg i 1 ⟨by norm_num, le_rfl⟩ hp
      · simpa only [densityEndpoint, ↓reduceIte, transportSegmentInput_apply,
          zero_smul, add_zero] using hseg i 0 ⟨le_rfl, by norm_num⟩ hp
    exact hh.mono_right (D i).field.ball_subset
  have hminimal (i : ι) (F : Euclidean n → Euclidean (embeddingDimension n))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
      (hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold)
      (hsmall : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δgeometry i) := by
    obtain ⟨hbase, hcur, hfrozen⟩ := hgeometry i F hF hi hrank hlow hsmall
    obtain ⟨hc, _hs, hrange, hnormalized, _heq, hhalf, hJ, _hJs, _hJeq, _hinj,
      _hscale, hmask, _hpunct⟩ := hcur
    obtain ⟨hc₀, _hs₀, hrange₀, hnormalized₀, _heq₀, hhalf₀, hJ₀, _hJs₀, _hJeq₀, _hinj₀,
      _hscale₀, hmask₀, _hpunct₀⟩ := hfrozen
    exact And.intro hbase.1 <| And.intro
      (And.intro hc <| And.intro hrange <| And.intro hnormalized <| And.intro hhalf <| And.intro
        (fun p hp ↦ hJ p (hKBi i hp)) (fun p hp ↦ (hmask p hp).2.2.1))
      (And.intro hc₀ <| And.intro hrange₀ <| And.intro hnormalized₀ <| And.intro hhalf₀ <| And.intro
        (fun p hp ↦ hJ₀ p (hKBi i hp)) (fun p hp ↦ (hmask₀ p hp).2.2.1))
  obtain ⟨Bsource, hBsource, hcontrols⟩ := exists_selected_source_family_quarter_gap
    hn H hP hUG hbounded T hΩ hKΩ hΩpatch hRc hτlead hτRc hbuffer hphysical c₀ htrans
    hL hMc hR hforward hRT hRU hRtime hV hVP hflow hlabel D hD hηb hr hr' ha'
    hrr haa har' hcell houter (fun i ↦ isCompact_closedBall (p₀ i) (ρ i))
    (fun i ↦ convex_closedBall (p₀ i) (ρ i)) hW hKiW hWinput hQc hΩsource hQcΩ hne hcone
    hfoot hIt hIIt hsegT hend hε hgap hsourceCap hcap1 (fun i p hp ↦ hfreq i p (hKBi i hp))
    A current δgeometry hδgeometry hminimal
  obtain ⟨carrierCap, hcarrierCap, _hcarrierCap8, Cnorm, Cpdo, hCnorm, _hCpdo,
      Bhigh, _hBhigh, hcarriers⟩ := exists_finite_retained_source_density_carriers
    H P hUG hbounded T hP Ωflow hΩ zCell ρc Rc B τlead L Mc row col hKΩ hΩpatch
    hRc hτlead hτRc hL hbuffer hphysical c₀ htrans hMc hforward R hR hRT hRU hRtime
    V hV hVP hflow hlabel D hD z₀ ηb hηb r a r' a' hr hr' ha' hcell hrr haa har' haR
    hsupportD houter p₀ q₀ ρ τ hρ hτ W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt
    hsegT hseg A ε gap hε hgap hfreq δgeometry hδgeometry
    (fun i F hF hi hrank hlow hsmall ↦ (hgeometry i F hF hi hrank hlow hsmall).1)
  obtain ⟨εgeometry, hεgeometry, hεgeometry_le⟩ :=
    (finite_range δgeometry).isCompact.exists_forall_le' continuousOn_id
      (by rintro x ⟨i, rfl⟩; exact hδgeometry i)
  obtain ⟨admissionCap, hadmissionCap, _hadmissionCap1, hadmit⟩ :=
    SourceMatching.exists_joint_stress_scale_interval H hbounded hεgeometry
  have hi : IsImmersionOn H.map U := isImmersionOn_of_isIsometricOn
    (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ H.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUG hx)
  refine ⟨Cnorm, Bsource, hCnorm, hBsource, ?_⟩
  intro targetGap htargetGap tol
  obtain ⟨comparisonCap, hcomparisonCap, hcomparisonSource, hcomparisonOne, hcontrol⟩ :=
    hcontrols targetGap htargetGap
  let cap := min comparisonCap (min carrierCap admissionCap)
  have hcapSource : cap ≤ sourceCap := (min_le_left _ _).trans hcomparisonSource
  refine ⟨cap, lt_min hcomparisonCap (lt_min hcarrierCap hadmissionCap), hcapSource,
    (min_le_left _ _).trans hcomparisonOne, ?_⟩
  intro σ hσ v hv hpos hinterval hvnorm cσ e pair
  have hσsource : σ ∈ Ioc (0 : ℝ) sourceCap := ⟨hσ.1, hσ.2.trans hcapSource⟩
  have hσone : σ ≤ 1 := hσsource.2.trans hcap1
  have hσcomparison : σ ∈ Ioc (0 : ℝ) comparisonCap := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hσcarrier : σ ∈ Ioc (0 : ℝ) carrierCap :=
    ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hvAt (i : ι) (y) (hy : y ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8)) :
      ContDiffAt ℝ ∞ (v i) y :=
    (hv i).contDiffAt (isOpen_ball.mem_nhds ((closedBall_subset_ball (by linarith [hL i])) hy))
  obtain ⟨hamp, hb, hs, hB, hnorms, hsum, hmeas⟩ :=
    hcontrol σ hσcomparison v hvAt hvnorm (fun i y hy ↦ (hinterval i y hy).1)
  refine ⟨hamp, hb, hs, hB, ?_⟩
  intro Aop Nop
  obtain ⟨hsupport, hbsmooth, hA, Vop, hop⟩ :=
    hcarriers σ hσcarrier (current σ hσsource) v hv hpos hinterval hvnorm
  have hgeometryCurrent (i : ι) := by
    obtain ⟨hiσ, hrankσ, hframeSmooth, hsmall⟩ := hadmit σ hσ.1
      (hσ.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hsmallCell : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) < δgeometry i := by
      apply ((cNorm_mono_set_of_contDiffAt ((hphysical i).trans subset_closure)
        hbounded.isCompact_closure ?_).trans_lt hsmall).trans_le (hεgeometry_le _ ⟨i, rfl⟩)
      exact fun x hx ↦ ((hframeSmooth x hx).sub contDiffAt_const).of_le (by simp)
    have hFσ : ContDiffOn ℝ ∞ (sourceDilation H.map σ) U :=
      (contDiff_sourceDilation H.contDiff).contDiffOn
    have hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) < (T i).family.threshold := by
      rw [← (current σ hσsource i).frame_eq]
      exact (current σ hσsource i).Q.2.2
    have hh := hminimal i (sourceDilation H.map σ) hFσ hiσ hrankσ hlow hsmallCell
    have hQ : (⟨projectedStress (sourceDilation H.map σ),
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hFσ hiσ hrankσ), hlow⟩ :
        {QF : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ QF U ∧
          cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (QF - fun _ ↦ cubeStress n) < (T i).family.threshold}) = (current σ hσsource i).Q :=
      Subtype.ext (current σ hσsource i).frame_eq.symm
    rw [hQ] at hh
    exact And.intro hh.1 hh.2.1
  have hnormal (i : ι) : carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint = Nop 0 i := by
    have hg := hgeometryCurrent i
    obtain ⟨_hforward, _hu, _hrange, hmap, heq, _hhalf, _hJgap, _hJs, _hJpos, _hJeq,
        _hscale, _hJscale, hpunct, _hshell⟩ :=
      retained_source_canonical_comparison_geometry (T i) (c₀ i).Q (current σ hσsource i).Q
        (hP i) H.contDiff hrank (hphysical i) (c₀ i).frame_eq (htrans i) hσ.1 hσone
        (current σ hσsource i).frame_eq (hRT i) (hV i) (hVP i) (hηb i) (hr i) (hr' i)
        (ha' i) (hrr i) (haa i) (har' i) (by norm_num : (0 : ℝ) < 1 / 4) (houter i) hg.1
        (hKiW i) (hWinput i) (hQc i) (hQcΩ i) hg.2.1 (hne i) (hcone i)
        hg.2.2.1 hg.2.2.2.1 (A i) hg.2.2.2.2.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2
    have huSource : u i σ = symbolInverse (T i) (current σ hσsource i).Q
        (z₀ i) (ηb i) (r i) (6 * a i) := by
      simp only [u, ite_eq_right (ne_of_gt hσ.1), Qcurrent, dite_eq_left hσsource]
    have hnormalSource := (retained_source_normal_eq_normalized_on_common_cone (hP i) (T i)
      (hΩ i) (hKΩ i) (hΩpatch i) (hRc i) (hτlead i) (hτRc i) (hbuffer i)
      H.contDiff hi hrank (hphysical i) (c₀ i) (htrans i) (fun x _ ↦ H.inducedMetric_eq_one x)
      (hR i) (hRT i) (hRU i) (hV i) (hVP i) (hflow i) (D i) (hD i)
      (hηb i) (hr i) (hr' i) (ha' i) (hrr i) (haa i) (har' i) (hcell i) (houter i)
      hσ.1 hσone (current σ hσsource i) hg.1 (Ωsource i) hpunct (W i) (hWinput i)
      (u i σ) (huSource.symm ▸ hmap) (huSource.symm ▸ heq) (v i) (S i))
      (4 * a' i) (Cpdo i) (hbsmooth i)
      (fullReflectedMatrixAmplitude_supportedInCenteredBox _ _ _ _ _ (4 * a' i) (hsupport i))
      (fun j k ξ is his ↦ hA i j k ξ is (his.trans (Nat.le_succ _)))
      (Vop i) (hop i).2.2.2.2.2.2.1
    exact hnormalSource.1 (4 * a' i) (Bsource i) (hb 0 i) (hs 0 i) (hB 0 i)
  refine ⟨Vop, fun i ↦ (hop i).1, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hop i).2.2.1, (hop i).2.2.2.2.2.1, hnormal i, ?_⟩
    rw [hnormal i]
    exact (hnorms i).2.2
  · simpa only [hnormal] using hsum
  · intro χ hχ
    simpa only [CommonMeasurement.carrierChannel_restrictCarrier_normal, hnormal] using hmeas χ hχ

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
