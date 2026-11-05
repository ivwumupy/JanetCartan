module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RawCappedInitialization.LocalCaps
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Radius

/-!
# A finite original incidence row retaining prescribed raw caps

The prescribed positive caps may depend on the incidence center and original
flow cell. They are imposed before the finite subcover is selected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol FullPhaseCharts ActualPhase ActualComparison
open CarrierVariation.FamilyInputs PositiveReference ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude CarrierSobolev
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.NormalInputs ContinuumAdjoint.Canonical.PhaseExtension CommonMeasurement

/-- Select the finite incidence cover using masks that obey the prescribed
raw-adjoint caps on the original seed cells. The source of these caps is
`ContinuumInverse.exists_corrected_seed_rawAdjoint_for_submasks`; their actual
application follows in `RawCappedInitialization`. The original current/frozen
conic geometry, full detector support, measurement radius and uncorrected raw
bounds are retained on these same masks (`app:ch_background:defn:bg-row`,
`app:ch_background:prop:bg-adjoint`, `app:ch_waves:thm:sampling`). -/
theorem exists_finite_incidence_geometry_rawAdjoints_and_sampling_with_prescribed_caps
    {n : ℕ} {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C) (H : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    (T : (b : Fin D.chartCount) → (a : Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches b a) U hU)
    (I : (b : Fin D.chartCount) → Fin (D.patchCount b) → Type*)
    (Ω : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) →
      I b l → Set (Euclidean n × Euclidean 3))
    (hΩ : ∀ b l j, IsOpen (Ω b l j))
    (zCell : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) → I b l → Euclidean 3)
    (ρc Rc M τlead : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) → I b l → ℝ)
    (row col : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) → I b l → Fin n)
    (hKΩ : ∀ b l j, closedBall ((0 : Euclidean n), zCell b l j) (ρc b l j) ⊆ Ω b l j)
    (hpatch : ∀ b l j, Ω b l j ⊆
      ball (0 : Euclidean n) (T b l).physicalRadius ×ˢ parameterCube (2 * (D.patches b l).radius))
    (hRc : ∀ b l j, 0 < Rc b l j) (hτ : ∀ b l j, 0 < τlead b l j)
    (hτR : ∀ b l j, τlead b l j ≤ Rc b l j / 16)
    (hbuffer : ∀ b l j, MapsTo (coordinates (adaptedCoordinates (T b l).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell b l j)) (Rc b l j))
      (closedBall ((0 : Euclidean n), zCell b l j) (ρc b l j)))
    (hphysical : ∀ b l, closedBall (0 : Euclidean n) (T b l).data.localReference.stateRadius ⊆ U)
    (c₀ : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) → (j : I b l) →
      FlowConstruction.Chart (T b l) (Ω b l j)
        (closedBall ((0 : Euclidean n), zCell b l j) (ρc b l j))
        ((0 : Euclidean (n - 1)), zCell b l j) (Rc b l j) (M b l j) (τlead b l j)
        (row b l j) (col b l j) H.map)
    (htrans : ∀ b l j q, q ∈ closedBall (0, (T b l).data.center)
        (T b l).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (c₀ b l j).Q.1 (c₀ b l j).Q.2.1).hp q,
        (T b l).data.adapted.normal⟫_ℝ ≠ 0)
    (R : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) → I b l → ℝ)
    (V : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) → I b l → Set CarrierParameter)
    (hR : ∀ b l j, 0 < R b l j)
    (hRphysical : ∀ b l j, R b l j ≤ (T b l).physicalRadius)
    (hRU : ∀ b l j, ball (0 : Euclidean n) (R b l j) ⊆ U)
    (hV : ∀ b l j, IsOpen (V b l j))
    (hVP : ∀ b l j, V b l j ⊆ parameter ⁻¹' parameterInterior (3 * (D.patches b l).radius / 2))
    (hflow : ∀ b l j, MapsTo (densityCoordinates (T b l))
      (ball (0 : Euclidean n) (R b l j) ×ˢ V b l j)
      (FlowConstruction.outputCylinder ((0 : Euclidean (n - 1)), zCell b l j)
        (Rc b l j) (τlead b l j)))
    (hcover : ∀ b l z, z ∈ parameterCube (D.patches b l).radius →
      ∃ j, ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
        ball (0 : Euclidean n) (R b l j) ×ˢ V b l j)
    (aCap bCap : (p : IncidenceCenter D) → (l : Fin (D.patchCount p.1.1)) → I p.1.1 l → ℝ)
    (haCap : ∀ p l j, 0 < aCap p l j) (hbCap : ∀ p l j, 0 < bCap p l j)
    {cap : ℝ} (hcap : 0 < cap) :
    let E := fun b l j ↦ ball (0 : Euclidean n) (R b l j) ×ˢ V b l j
    ∃ cell : (p : IncidenceCenter D) → (a : Fin (D.patchCount p.1.1)) → I p.1.1 a,
      (∀ p a, ((0 : Euclidean n),
        (D.roots p.1.1 a p.1.2 0, spectatorCenter (D.roots p.1.1 a p.1.2))) ∈
          E p.1.1 a (cell p a)) ∧
    ∃ centers : Finset (IncidenceCenter D), ∃ εcover : centers → ℝ,
      (∀ j, 0 < εcover j) ∧
      sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (εcover j) ∧
      (∀ j, ball j.1.1.2 (εcover j) ⊆ D.domain j.1.1.1) ∧
      (∀ j, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ s : Euclidean n,
        c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil q) s‖ ^ 2 +
          ∑ a, inner ℝ (CubeCarrier.quadratic ((D.patches j.1.1.1 a).toFun
            (D.roots j.1.1.1 a q))) s ^ 2) ∧
    let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
    let family := fun i : ι ↦ T i.1.1.1.1 i.2
    let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
    let k := fun i : ι ↦ i.1.1.1.2
    ∃ t r a r' a' : ι → ℝ,
    ∃ (_ht : ∀ i, 0 < t i) (_hr : ∀ i, 0 < r i) (_ha : ∀ i, 0 < a i)
      (hr' : ∀ i, 0 < r' i) (ha' : ∀ i, 0 < a' i),
    ∃ hcell : ∀ i, 4 * a' i < 1 / 2,
    let ηb := fun i ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint (t i • k i)
    ∃ hηb : ∀ i, ηb i ≠ 0,
      (∀ i, ‖t i • k i‖ = 1 / 4) ∧
      (∀ i, NormedSpace.normalize (t i • k i) = NormedSpace.normalize (k i)) ∧
      (∀ i, a' i ≤ aCap i.1.1 i.2 (cell i.1.1 i.2) ∧
        angularWidth (ηb i) (r' i) ≤ bCap i.1.1 i.2 (cell i.1.1 i.2)) ∧
      (∀ i, 6 * a i < cap ∧
        coefficientDomain (z i) (r i) (6 * a i) ⊆ E i.1.1.1.1 i.2 (cell i.1.1 i.2) ∧
        r' i ≤ r i ∧ a' i ≤ a i ∧ a' i ≤ r' i ∧ 6 * a i < (family i).family.radius) ∧
      (∀ j : centers, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ l : Fin (D.patchCount j.1.1.1),
        ((0 : Euclidean n), (D.roots j.1.1.1 l q 0, spectatorCenter (D.roots j.1.1.1 l q))) ∈
          E j.1.1.1 l (cell j.1 l) ∧
        angularMask (z ⟨j, l⟩) (NormedSpace.normalize (ηb ⟨j, l⟩))
          (ha' ⟨j, l⟩) (angularWidth_spec (hηb ⟨j, l⟩) (hr' ⟨j, l⟩)).1
          (D.roots j.1.1.1 l q 0, spectatorCenter (D.roots j.1.1.1 l q))
          (NormedSpace.normalize ((family ⟨j, l⟩).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1) ∧
    ∃ b : ℝ, ∃ (_hb : 0 < b) (_hbcell : 4 * b < 1 / 2),
      6 * b < H.domain.chartRadius ∧ 6 * b < 1 / 2 ∧ (∀ i, 6 * b < a' i) ∧
    (∀ i : ι,
      IsCompact (parameter '' carrierSupport (z i) (r := a' i)) ∧
      MapsTo parameter (carrierSupport (z i) (r := a' i))
        (parameterInterior (D.patches i.1.1.1.1 i.2).radius) ∧
      (∀ z' ∈ parameter '' carrierSupport (z i) (r := a' i),
        ∀ θ ∈ closedDirections (ηb i) (r' i),
          NormedSpace.normalize (Sampling.frozenInputCovector (family i) z' θ) ∈
            D.domain i.1.1.1.1) ∧
      ∀ detector : Euclidean (n - 1) → ℂ,
        (∀ ξ, detector ξ ≠ 0 → NormedSpace.normalize ξ ∈ closedDirections (ηb i) (r' i)) →
        (∀ z' ∈ parameter '' carrierSupport (z i) (r := a' i),
          ∀ θ ∈ Sampling.detectorDirectionSupport detector,
            NormedSpace.normalize (Sampling.frozenInputCovector (family i) z' θ) ∈
              D.domain i.1.1.1.1) ∧
        IsCompact (Sampling.transverseDetectorIncidenceSupport (family i)
          (parameter '' carrierSupport (z i) (r := a' i)) detector) ∧
        ∀ w ∈ Sampling.transverseDetectorIncidenceSupport (family i)
            (parameter '' carrierSupport (z i) (r := a' i)) detector,
          w.1 ∈ parameterInterior (D.patches i.1.1.1.1 i.2).radius ∧ w.2 ≠ 0 ∧
          incidence w.2 ((D.patches i.1.1.1.1 i.2).toFun w.1) = 0 ∧
          fderiv ℝ (fun z' ↦ incidence w.2 ((D.patches i.1.1.1.1 i.2).toFun z')) w.1
            (EuclideanSpace.single 0 1) ≠ 0) ∧
    ∃ δ > (0 : ℝ), (∀ i : ι,
    let T := family i
    let P := D.patches i.1.1.1.1 i.2
    let z₀ := z i
    let ηb := ηb i
    let r := r i
    let a := a i
    let r' := r' i
    let a' := a' i
    let ha' := ha' i
    let E := E i.1.1.1.1 i.2 (cell i.1.1 i.2)
    ∃ (D : CoefficientNormCharts n) (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
      (ρ τ : ℝ) (W Bi : Set (InputVariables n)) (It : Set ℝ)
      (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) (ε gap : ℝ)
      (Qc Ωi : Set (Variables n × Euclidean 2)),
    ∃ (β cJ : ℝ) (Vphase Lphase : Set (ℝ × Euclidean (n - 1)))
      (G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))),
      (p₀ = augmentedInputCenter T (z₀ := z₀) (k := t i • k i) ∧
      q₀ = frozenAugmentedChart T p₀ ∧ 6 * a ≤ r ∧ 4 * a < 1 / 2 ∧
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
      r' ≤ ρ ∧ 4 * a' < ρ ∧ 0 < β ∧ 0 < cJ ∧ IsOpen Vphase ∧
      IsCompact (closure Vphase) ∧ IsCompact Lphase ∧ Lphase ⊆ Vphase) ∧
      originOutput q₀ = q₀ ∧
      Qc = compactTarget (1 / 4) q₀ τ ∧ Ωi = conicTarget (1 / 4) q₀ τ ∧
      0 < ρ ∧ 0 < τ ∧ IsOpen W ∧ closedBall p₀ ρ ⊆ W ∧ IsCompact Bi ∧ W ⊆ Bi ∧
      Bi ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧ D.field.region ⊆ E ∩ coefficientDomain z₀ r (6 * a) ∧
      (∀ p ∈ closedBall p₀ ρ, D.Contains p) ∧
      (tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
        carrierSupport z₀ (r := a') ⊆ D.field.carrier) ∧
      IsOpen It ∧ Icc (0 : ℝ) 1 ⊆ It ∧
      (∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier) ∧
      (∀ side, MapsTo (CarrierVariation.FamilyInputs.WideDensity.densityEndpoint side)
        W D.field.carrier) ∧
      0 < ε ∧ (∀ p ∈ Bi, ε ≤ ‖p.2.2‖) ∧ 0 < gap ∧
      IsCompact Qc ∧ IsOpen Ωi ∧ Qc ⊆ Ωi ∧
      (∀ q ∈ Qc, ‖q.1.2.2‖ = 1 / 4) ∧ (∀ q ∈ Ωi, q.1.2.2 ≠ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ωi ↔ q ∈ Ωi) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
          (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖G.symm.toContinuousLinearMap.comp
            (fderiv ℝ (adaptedTransportChart T Q p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) Vphase Lphase β cJ G ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a),
          ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
            ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) ∧
        closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ,
          ‖A.symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (closure (augmentedTransportGradient (transportPosition T Q) '' conicMaskSupport z₀ ηb r' a') ∩
          {p | p.1.2.2 ≠ 0} ⊆ symbolDomain T Q z₀ ηb r (6 * a)) ∧
        (∀ x : Variables n, ‖x.2.2‖ = (1 / 4 : ℝ) → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
          ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖) ∧
        (closedBall q₀ (2 * τ) ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ,
          ‖A.symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ x : Variables n, ‖x.2.2‖ = (1 / 4 : ℝ) → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
          conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
          frozenSymbolDomain T Q z₀ ηb r (6 * a)))) ∧
        (RetainedSpectralGeometry T Q z₀ ηb r a ∧
        closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ, ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (transportPosition T Q) p) ∧
        (closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
            symbolDomain T Q z₀ ηb r (6 * a)) ∧
        (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
          ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)) ∧
      (let u := symbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (transportPosition T Q)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q)) W ∧
      EqOn (symbolJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)) W ∧
      InjOn (augmentedTransportGradient (transportPosition T Q)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (transportPosition T Q) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition T Q) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (transportPosition T Q) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (transportPosition T Q) p) = p) ∧
      (closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi)) ∧
      (let u := frozenSymbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (normalizedTransportPosition T Q 0)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0)) W ∧
      EqOn (frozenKernelJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)) W ∧
      InjOn (augmentedTransportGradient (normalizedTransportPosition T Q 0)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (normalizedTransportPosition T Q 0) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (normalizedTransportPosition T Q 0) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) = p) ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi))) ∧
    ∃ χinitial : ι → ContDiffBump (0 : CarrierVariable n),
    ∃ Cbound Lbound : ι → ℕ → ℝ,
      (∀ i s, 0 ≤ Cbound i s) ∧ (∀ i s, 0 ≤ Lbound i s) ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧ ∀ i : ι,
    let T := family i
    let z₀ := z i
    let ηb := ηb i
    let a' := a' i
    let hr' := hr' i
    let ha' := ha' i
    let hcell := hcell i
    let hηb := hηb i
    let j := cell i.1.1 i.2
    let Ω := Ω i.1.1.1.1 i.2 j
    let zCell := zCell i.1.1.1.1 i.2 j
    let ρc := ρc i.1.1.1.1 i.2 j
    let Rc := Rc i.1.1.1.1 i.2 j
    let M := M i.1.1.1.1 i.2 j
    let τlead := τlead i.1.1.1.1 i.2 j
    let row := row i.1.1.1.1 i.2 j
    let col := col i.1.1.1.1 i.2 j
    let c₀ := c₀ i.1.1.1.1 i.2 j
    let χinitial := χinitial i
    let Cbound := Cbound i
    let Lbound := Lbound i
    supportedChart (n := n) z₀ a' ⊆ E i.1.1.1.1 i.2 j ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.2, normalizedTransportPosition T c₀.Q σ p))
        (supportedChart z₀ a') (interior {q | χinitial q = 1}) ∧
      let d := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
        (fun _ ↦ 1) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency σ
      (∀ cσ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρc)
        ((0 : Euclidean (n - 1)), zCell) Rc M τlead row col (sourceDilation H.map σ),
        carrierKernel (data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
          (fun _ ↦ σ) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency) = carrierKernel d) ∧
      ∃ A : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
        (∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → B = A) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∃ hraw : ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          MemRawSobolev s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)),
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          rawSobolevNorm s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            (2 * Cbound s) * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) (s + 1),
          let f := (carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 (s + 1) w)
          let hf := (hraw (s + 1) w).mono (by omega : 1 ≤ s + 1)
          MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ∧
          MemPhysicalSobolev s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) := by
  classical
  let E := fun b l j ↦ ball (0 : Euclidean n) (R b l j) ×ˢ V b l j
  have hE : ∀ b l j, IsOpen (E b l j) := fun b l j ↦ isOpen_ball.prod (hV b l j)
  obtain ⟨cell, hcell, hfinite⟩ := exists_retained_incidence_cell_selection hD T I E hE hcover
  have hk (p : IncidenceCenter D) : p.1.2 ≠ 0 := by
    intro hzero
    have hs := p.2.1
    simp [hzero] at hs
  have hz (p : IncidenceCenter D) (a : Fin (D.patchCount p.1.1)) :=
    ((hD.2.2.2.2.1 p.1.1 a).2.2.1 p.1.2 p.2.2).1
  have hinc (p : IncidenceCenter D) (a : Fin (D.patchCount p.1.1)) :=
    ((hD.2.2.2.2.1 p.1.1 a).2.2.1 p.1.2 p.2.2).2.2.2
  have hd (p : IncidenceCenter D) (a : Fin (D.patchCount p.1.1)) :
      fderiv ℝ (fun w ↦ incidence p.1.2 ((D.patches p.1.1 a).toFun w))
        (D.roots p.1.1 a p.1.2) (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le ((hD.2.2.2.2.1 p.1.1 a).2.2.2 p.1.2 p.2.2 _
      (fun j ↦ (hz p a j).le)))
  choose t ht htnorm hdir hηdir r a r' a' hr ha hr' ha' hcell' hacap houter
    hrr haa har' haR hηb hspatial hangular hparameter hdirections hdetector δ hδ hlocal χinitial σlocal hσlocal hσone
    hcellRaw hchart Cbound Lbound hCbound hLbound hraw using
    fun (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) ↦
      exists_retained_normalized_cell_geometry_and_rawAdjoint_with_prescribed_caps H (hD.2.2.2.2.1 p.1.1 l).1
        (T p.1.1 l) hUH hbounded (hΩ p.1.1 l (cell p l))
        (hKΩ p.1.1 l (cell p l)) (hpatch p.1.1 l (cell p l))
        (hRc p.1.1 l (cell p l)) (hτ p.1.1 l (cell p l)) (hτR p.1.1 l (cell p l))
        (hbuffer p.1.1 l (cell p l)) (hphysical p.1.1 l) (c₀ p.1.1 l (cell p l))
        (htrans p.1.1 l (cell p l)) (hR p.1.1 l (cell p l))
        (hRphysical p.1.1 l (cell p l)) (hRU p.1.1 l (cell p l))
        (hV p.1.1 l (cell p l)) (hVP p.1.1 l (cell p l)) (hflow p.1.1 l (cell p l))
        (hz p l) (hcell p l).2 (hk p) (hinc p l) (hd p l)
        (hD.2.2.1 p.1.1)
        (by
          rw [NormedSpace.normalize_eq_self_of_norm_eq_one
            (mem_sphere_zero_iff_norm.mp p.2.1)]
          exact p.2.2) hcap (haCap p l (cell p l)) (hbCap p l (cell p l))
  obtain ⟨centers, εcover, hεcover, hcover, hdomain, hmask, hgram⟩ :=
    hfinite a' (fun p l ↦ angularWidth
      ((T p.1.1 l).data.adapted.embedding.toContinuousLinearMap.adjoint (t p l • p.1.2))
      (r' p l)) ha' (fun p l ↦ (angularWidth_spec (hηb p l) (hr' p l)).1)
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  obtain ⟨δ₀, hδ₀, hδle⟩ :=
    (finite_range (fun i : ι ↦ δ i.1.1 i.2)).isCompact.exists_forall_le' continuousOn_id
      (by rintro d ⟨i, rfl⟩; exact hδ i.1.1 i.2)
  obtain ⟨σ₀, hσ₀, hσle⟩ :=
    (finite_range (fun i : ι ↦ σlocal i.1.1 i.2)).isCompact.exists_forall_le' continuousOn_id
      (by rintro d ⟨i, rfl⟩; exact hσlocal i.1.1 i.2)
  obtain ⟨b, hb, hbH, hbhalf, hba⟩ := CommonMeasurement.exists_common_radius H
    (fun i : ι ↦ a' i.1.1 i.2) (fun i ↦ ha' i.1.1 i.2)
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover, hdomain, hgram,
    (fun i ↦ t i.1.1 i.2), (fun i ↦ r i.1.1 i.2), (fun i ↦ a i.1.1 i.2),
    (fun i ↦ r' i.1.1 i.2), (fun i ↦ a' i.1.1 i.2),
    (fun i ↦ ht i.1.1 i.2), (fun i ↦ hr i.1.1 i.2), (fun i ↦ ha i.1.1 i.2),
    (fun i ↦ hr' i.1.1 i.2), (fun i ↦ ha' i.1.1 i.2), (fun i ↦ hcell' i.1.1 i.2),
    (fun i ↦ hηb i.1.1 i.2), (fun i ↦ htnorm i.1.1 i.2), (fun i ↦ hdir i.1.1 i.2),
    (fun i ↦ ⟨hspatial i.1.1 i.2, hangular i.1.1 i.2⟩),
    (fun i ↦ ⟨hacap i.1.1 i.2, houter i.1.1 i.2, hrr i.1.1 i.2,
      haa i.1.1 i.2, har' i.1.1 i.2, haR i.1.1 i.2⟩), ?_,
    b, hb, (by linarith), hbH, hbhalf, hba, ?_, δ₀, hδ₀, ?_,
    (fun i ↦ χinitial i.1.1 i.2), (fun i ↦ Cbound i.1.1 i.2),
    (fun i ↦ Lbound i.1.1 i.2), (fun i ↦ hCbound i.1.1 i.2),
    (fun i ↦ hLbound i.1.1 i.2), min σ₀ 1, lt_min hσ₀ zero_lt_one, min_le_right _ _, ?_⟩
  · intro j q hq l
    simpa only [hηdir] using hmask j q hq l
  · intro i
    have hZ : IsCompact (parameter '' carrierSupport
        (D.roots i.1.1.1.1 i.2 i.1.1.1.2) (r := a' i.1.1 i.2)) :=
      (carrierSupport_compact _).image parameter.continuous
    refine ⟨hZ, hparameter i.1.1 i.2, hdirections i.1.1 i.2, ?_⟩
    intro detector hdet
    have hchart := hdetector i.1.1 i.2 detector hdet
    exact ⟨hchart, Sampling.transverseDetectorIncidenceSupport_spec
      (T i.1.1.1.1 i.2) (hD.2.2.2.2.1 i.1.1.1.1 i.2).1 hZ
      (by rintro _ ⟨p, hp, rfl⟩; exact hparameter i.1.1 i.2 hp)
      (hD.2.2.2.2.1 i.1.1.1.1 i.2).2 detector hchart⟩
  · intro i
    obtain ⟨D, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi,
      β, cJ, Vphase, Lphase, G, hbufferData, horigin, hcompact, hcone, hρ, hτ, hW, hKiW, hBi, hWBi, hBiDom, hD, hfoot, hsupportD,
      hIt, hIIt, hsegT, hseg, hend, hε, hfreq, hgap, hQc, hΩi, hQcΩi,
      hQcnorm, hΩne, hΩrad, hgeometry⟩ := hlocal i.1.1 i.2
    refine ⟨D, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi,
      β, cJ, Vphase, Lphase, G, hbufferData, horigin, hcompact, hcone, hρ, hτ, hW, hKiW, hBi, hWBi, hBiDom, hD, hfoot, hsupportD,
      hIt, hIIt, hsegT, hseg, hend, hε, hfreq, hgap, hQc, hΩi, hQcΩi,
      hQcnorm, hΩne, hΩrad, ?_⟩
    intro F hF hi hrank hlow hsmall
    exact hgeometry F hF hi hrank hlow (hsmall.trans_le (hδle _ ⟨i, rfl⟩))
  · intro i
    refine ⟨hchart i.1.1 i.2, ?_⟩
    intro σ hσ
    exact hraw i.1.1 i.2 σ
      ⟨hσ.1, (hσ.2.trans (min_le_left _ _)).trans (hσle _ ⟨i, rfl⟩)⟩


end JanetCartan.ContinuumRow.NormalizedSelection
