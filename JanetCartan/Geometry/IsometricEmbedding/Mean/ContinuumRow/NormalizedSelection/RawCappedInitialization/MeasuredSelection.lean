module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RawCappedInitialization.CorrectedSelection
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RawCappedInitialization.MeasuredDensityBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.MeasuredFamily
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.MeasuredRawBounds

/-!
# The original measured row and its corrected raw adjoint

Impose corrected raw caps before finite incidence selection, then choose one
measurement radius and coefficient array. Both the unit row and every admitted
corrected density retain that row's masks, geometry and original cutoffs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol FullPhaseCharts ActualPhase ActualComparison
open CarrierVariation.FamilyInputs PositiveReference ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude CarrierSobolev GeometricProfile
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.PhaseExtension CommonMeasurement

/-- Construct the original measured incidence row and actual corrected
augmented-adjoint bounds on the same masks, coefficient cutoff and measurement
radius. The corrected bounds allow the supplied smooth exterior returned by
the inverse construction. The raw caps are imposed before choosing the incidence cover. Every
higher density norm appears once, at the original derivative reserve, and all
constants precede the varying source scale and density. Literal adjoint
uniqueness identifies any supplied bounded realization on that same row.
The same masks also obey the supplied positive history cap `aExtra`; its
actual producer is `exists_generic_current_rawAdjoint_cap`.
The consumer is the corrected positive inverse inside the common initializer
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-density-adjoint`, `app:ch_background:prop:bg-positive`). -/
theorem exists_finite_measured_incidence_row_with_corrected_rawAdjoints
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
    (hpatchStrong : ∀ b l j, Ω b l j ⊆
      (U ∩ ball (0 : Euclidean n) (T b l).physicalRadius) ×ˢ
        parameterInterior (3 * (D.patches b l).radius / 2))
    (hM : ∀ b l j, 0 ≤ M b l j)
    (hτeq : ∀ b l j, τlead b l j =
      existenceTime (Rc b l j) (liftedLowBound (T b l) (M b l j)) / 4)
    (hΩscale : ∀ b l j σ, σ ∈ Ioc (0 : ℝ) 1 →
      MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) (Ω b l j) (Ω b l j))
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
    (L Mforward : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) → I b l → ℝ)
    (hL : ∀ b l j, 0 < L b l j) (hMforward : ∀ b l j, 0 < Mforward b l j)
    (hforward : ∀ b l j, cNorm (Icc (-τlead b l j) (τlead b l j) ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell b l j) (Rc b l j / 8)) 1
        (c₀ b l j).forward ≤ Mforward b l j)
    (hRtime : ∀ b l j, R b l j ≤ L b l j / (64 * Mforward b l j))
    (hlabel : ∀ b l j p, p ∈ ball (0 : Euclidean n) (R b l j) ×ˢ V b l j →
      (densityCoordinates (T b l) p).2 ∈
        closedBall ((0 : Euclidean (n - 1)), zCell b l j) (L b l j / 64))
    (hcover : ∀ b l z, z ∈ parameterCube (D.patches b l).radius →
      ∃ j, ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
        ball (0 : Euclidean n) (R b l j) ×ˢ V b l j)
    {cap : ℝ} (hcap : 0 < cap)
    (aExtra : (p : IncidenceCenter D) → (l : Fin (D.patchCount p.1.1)) →
      I p.1.1 l → {ε : ℝ // 0 < ε} := fun _ _ _ ↦ ⟨1, by norm_num⟩) :
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
      (∀ i, a' i ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) ∧
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
    ∃ rMeasure : ℝ, ∃ hrMeasure : 0 < rMeasure, ∃ hMeasureCell : 4 * rMeasure < 1 / 2,
      6 * rMeasure < b ∧ 6 * rMeasure < H.domain.chartRadius ∧
      6 * rMeasure < 1 / 2 ∧ (∀ i, 6 * rMeasure < a' i) ∧
    ∃ χcoeff : Euclidean n → ℝ,
      ContDiff ℝ ∞ χcoeff ∧ (∀ x, χcoeff x ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χcoeff ∧ tsupport χcoeff ⊆ ball 0 (5 * rMeasure) ∧
      closedBall 0 (4 * rMeasure) ⊆ interior {x | χcoeff x = 1} ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ coeff : ℝ → ReducedCoefficientIndex n → C(Torus n, ℝ),
    ∃ Cimage Cbound Lbound : ℕ → ℝ,
      (∀ m, 0 < Cimage m) ∧ (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      (∀ σ j, IsSmoothPeriodic (coeff σ j)) ∧
      (∀ j x, coeff 0 j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
        ProtectedFlow.reducedCoefficientBackground (fun _ _ ↦ 0)
          (AmplitudeBound.centeredTorusRepresentative x) j) ∧
      (∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ j x,
        coeff σ j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
          geometricReducedCoefficients (sourceDilation H.map σ)
            (AmplitudeBound.centeredTorusRepresentative x) j) ∧
      (∀ m σ, σ ∈ Ioc (0 : ℝ) σ₀ → ∀ j x,
        ‖iteratedFDeriv ℝ m (periodicLift (coeff σ j - coeff 0 j)) x‖ ≤ Cimage m * σ ∧
        ‖iteratedFDeriv ℝ m (periodicLift (coeff σ j)) x‖ ≤ Cimage m) ∧
    let χ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 1
    let χsrc := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 2
    let ψ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 0
    let selected := fun i : ι ↦ cell i.1.1 i.2
    let seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
    let rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
    let coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
    let angular := fun i ↦ angularMask (z i) (NormedSpace.normalize (ηb i))
      (ha' i) (angularWidth_spec (hηb i) (hr' i)).1
    (
    ∀ σ ∈ Ioc (0 : ℝ) σ₀,
    let d := fun i ↦ normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
      (seed i).forward (seed i).inverse (fun _ ↦ 1) (ha' i) (hcell i) (angular i)
      FixedCutoffs.highFrequency σ
    let e := fun i ↦ normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
      (seed i).forward (seed i).inverse (fun _ ↦ 1) hrMeasure hMeasureCell (angular i)
      FixedCutoffs.highFrequency σ
    (∀ i, MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.2, normalizedTransportPosition (family i) (seed i).Q σ p))
      (closedBall 0 (6 * rMeasure) ×ˢ carrierSupport (z i) (r := a' i))
      (interior {q | χinitial i q = 1})) ∧
    ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i w, (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) ∧
    let Uop := fun i ↦ restrictCarrier χ (Vop i);
      (∀ i, ‖Uop i‖ ≤ ‖Vop i‖) ∧
      (∀ i w, (Uop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
      (∀ i, ∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) → B = Uop i) ∧
      (∀ i, (∀ f : carrierInitialTestSpace n,
          Vop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (d i) f.val) →
        ∀ f : carrierInitialTestSpace n,
          Uop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) ∧
      augmentedNormal (imageChannel (coeff σ) χ χsrc) Uop ψ =
        imageChannel (coeff σ) χ χsrc ∘L (imageChannel (coeff σ) χ χsrc).adjoint +
          (∑ i, cutoffMultiplier χ ∘L
            (carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint) ∘L cutoffMultiplier χ) +
          cutoffMultiplier ((1 - ψ) ^ 2) ∧
      ∀ selectedCoeff : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j x, selectedCoeff j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
          geometricReducedCoefficients (sourceDilation H.map σ)
            (AmplitudeBound.centeredTorusRepresentative x) j) →
      ∀ B : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i w, (B i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) →
        let A := augmentedRow (imageChannel selectedCoeff χ χsrc) B ψ
        (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
          A.adjoint w ∈ augmentedInputLevel n ι s ∧
          (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
            Cbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + ‖w‖)) ∧
        ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
          let u := A.adjoint w
          ∃ hf : ∀ i, MemRawSobolev 1 (u.fst.snd i),
            (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
              (densityUncut (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                (angularWidth_spec (hηb i) (hr' i)).1 (u.fst.snd i) (hf i))) ∧
              MemPhysicalSobolev s (physicalComplexifyL2
              (density (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                (angularWidth_spec (hηb i) (hr' i)).1 (χinitial i) (u.fst.snd i) (hf i)))) ∧
            densityUncutFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
              (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) s u ≤
              Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖) ∧
            densityFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
              (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) χinitial s u ≤
              Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖)) ∧
    ∀ ψcorrected : C(Torus n, ℝ), IsSmoothPeriodic ψcorrected →
    ∃ Ccorrected Lcorrected : ℕ → ℝ,
      (∀ s, 0 ≤ Ccorrected s) ∧ (∀ s, 0 ≤ Lcorrected s) ∧
    ∀ σ ∈ Ioc (0 : ℝ) σ₀,
    ∀ vDensity : ι → CarrierVariable n → ℝ,
      (∀ i, ContDiff ℝ ∞ (vDensity i)) →
      (∀ i q, 1 + vDensity i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i))
        (L i.1.1.1.1 i.2 (selected i) / 8)) (2 * (n + 1) + 14)
          (PositiveBackground.densityOnInitialLabels (vDensity i)) ≤ 1) →
    let Hhigh := fun s ↦ 1 + ∑ i,
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i))
        (L i.1.1.1.1 i.2 (selected i) / 8)) (s + 2 * (n + 1) + 14)
          (PositiveBackground.densityOnInitialLabels (vDensity i))
    let d := fun i ↦ CorrectedPositiveInverse.correctedCarrierData
      (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
        (seed i).forward (seed i).inverse (fun _ ↦ 1) (ha' i) (hcell i) (angular i)
        FixedCutoffs.highFrequency σ) (vDensity i)
    let e := fun i ↦ CorrectedPositiveInverse.correctedCarrierData
      (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
        (seed i).forward (seed i).inverse (fun _ ↦ 1) hrMeasure hMeasureCell (angular i)
        FixedCutoffs.highFrequency σ) (vDensity i)
    ∃ Vcorrected : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i w, (Vcorrected i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) ∧
    let Ucorrected := fun i ↦ restrictCarrier χ (Vcorrected i);
      (∀ i w, (Ucorrected i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
      (∀ i, ∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) → B = Ucorrected i) ∧
      ∀ selectedCoeff : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j x, selectedCoeff j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
          geometricReducedCoefficients (sourceDilation H.map σ)
            (AmplitudeBound.centeredTorusRepresentative x) j) →
      ∀ B : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i w, (B i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) →
        let A := augmentedRow (imageChannel selectedCoeff χ χsrc) B ψcorrected
        (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
          A.adjoint w ∈ augmentedInputLevel n ι s ∧
          (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
            Ccorrected s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + Hhigh s * ‖w‖)) ∧
        ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
          let u := A.adjoint w
          ∃ hf : ∀ i, MemRawSobolev 1 (u.fst.snd i),
            (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
              (densityUncut (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                (angularWidth_spec (hηb i) (hr' i)).1 (u.fst.snd i) (hf i))) ∧
              MemPhysicalSobolev s (physicalComplexifyL2
              (density (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                (angularWidth_spec (hηb i) (hr' i)).1 (χinitial i) (u.fst.snd i) (hf i)))) ∧
            densityUncutFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
              (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) s u ≤
              Lcorrected s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + Hhigh (s + 1) * ‖w‖) ∧
            densityFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
              (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) χinitial s u ≤
              Lcorrected s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + Hhigh (s + 1) * ‖w‖) := by
  classical
  obtain ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, hconic, huncorrected, sCorrected, hsCorrected, _hsCorrected1, hcorrected⟩ :=
    exists_finite_incidence_row_with_corrected_rawAdjoints hD H hUH hbounded T I Ω hΩ
      zCell ρc Rc M τlead row col hKΩ hpatchStrong hM hτeq hΩscale hRc hτ hτR hbuffer hphysical
      c₀ htrans R V hR hRphysical hRU hV hVP hflow L Mforward hL hMforward hforward hRtime hlabel
      hcover hcap aExtra
  obtain ⟨χinitial, Craw, Lraw, hCraw, hLraw, sRaw, hsRaw, _hsRaw1, hraw⟩ := huncorrected
  choose χcorrected _hchartCorrected CrawCorrected _LrawCorrected hCrawCorrected _hLrawCorrected hrawCorrected
    using hcorrected
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let family := fun i : ι ↦ T i.1.1.1.1 i.2
  let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let ηb := fun i : ι ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint
    (t i • i.1.1.1.2)
  let selected := fun i : ι ↦ cell i.1.1 i.2
  let seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
  let rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
  let coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
  let width := fun i : ι ↦ angularWidth (ηb i) (r' i)
  have hwidth (i : ι) : 0 < width i := (angularWidth_spec (hηb i) (hr' i)).1
  obtain ⟨rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    sImage, hsImage, hsImage1, coeff, Cimage, hCimage, hcoeff, hzero, hformula,
    hjets, hmeasured⟩ := exists_common_measured_normalized_data H family
      (fun i ↦ Ω i.1.1.1.1 i.2 (selected i))
      (fun i ↦ closedBall ((0 : Euclidean n), zCell i.1.1.1.1 i.2 (selected i))
        (ρc i.1.1.1.1 i.2 (selected i)))
      (fun i ↦ ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i)))
      (fun i ↦ Rc i.1.1.1.1 i.2 (selected i)) (fun i ↦ M i.1.1.1.1 i.2 (selected i))
      (fun i ↦ τlead i.1.1.1.1 i.2 (selected i)) rowi coli seed (fun _ _ ↦ 1)
      a' ha' hlocal z (fun i ↦ NormedSpace.normalize (ηb i)) width hwidth hb
      (H.domain.coreRadius_pos.trans H.domain.coreRadius_lt_chartRadius)
  let χ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 1
  let χsrc := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 2
  let ψ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 0
  obtain ⟨Cbound, Lbound, hCbound, hLbound, hrow⟩ := exists_uniform_measured_row_bounds
    H χ χsrc ψ (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 1)
    (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 2)
    (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 0)
    Cimage (fun m ↦ (hCimage m).le) Craw hCraw z
    (fun i ↦ NormedSpace.normalize (ηb i)) ha' hwidth χinitial
  let Kin := fun i : ι ↦ closedBall
    ((0 : Euclidean (n - 1)), zCell i.1.1.1.1 i.2 (selected i))
    (L i.1.1.1.1 i.2 (selected i) / 8)
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, hconic, χinitial, rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    min sRaw (min sImage sCorrected), lt_min hsRaw (lt_min hsImage hsCorrected),
    ((min_le_right _ _).trans (min_le_left _ _)).trans hsImage1,
    coeff, Cimage, Cbound, Lbound, hCimage, hCbound, hLbound, hcoeff, hzero,
    (fun σ hσ ↦ hformula σ ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩),
    (fun m σ hσ ↦ hjets m σ ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩), ?_⟩
  intro χ χsrc ψ selected seed rowi coli angular
  refine ⟨?_, ?_⟩
  · intro σ hσ d e
    have hσRaw : σ ∈ Ioc (0 : ℝ) sRaw := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
    have hσImage : σ ∈ Ioc (0 : ℝ) sImage := ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    choose hplateau hkernel Vop hrep hunique hlocalRaw hrealMem hrealBound hdensity using
      fun i ↦ (hraw i).2 σ hσRaw
    obtain ⟨hnorm, htest, hadj, hnormal⟩ := hmeasured.2 σ Vop
    have hArep (i : ι) (w : ComplexOutputL2 n) :
        (restrictCarrier χ (Vop i)).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w :=
      (hadj i (fun v ↦ ⟨(memLp_congr_ae (hrep i v)).mp (Lp.memLp ((Vop i).adjoint v)), hrep i v⟩) w).2
    have hUunique (i : ι) (B : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (hB : ∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) :
        B = restrictCarrier χ (Vop i) := by
      have he := DerivativeKernels.literalCarrierAdjointOperator_unique (e i)
        B.adjoint (restrictCarrier χ (Vop i)).adjoint hB (hArep i)
      simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg ContinuousLinearMap.adjoint he
    refine ⟨?_, Vop, hrep, hnorm, hArep, hUunique, htest, hnormal, ?_⟩
    · intro i p hp
      apply hplateau i
      exact NormalizedMeasurement.source_product_subset_original_supportedChart (z i) hrMeasure (hra i) hp
    · intro selectedCoeff hselected B hB
      have hcoeffEq : selectedCoeff = coeff σ := by
        funext j
        apply ContinuousMap.ext
        intro x
        exact (hselected j x).trans (hformula σ hσImage j x).symm
      have hBEq : B = fun i ↦ restrictCarrier χ (Vop i) := funext fun i ↦ hUunique i (B i) (hB i)
      subst selectedCoeff B
      exact hrow (coeff σ) (hcoeff σ) (fun m j x ↦ (hjets m σ hσImage j x).2)
        d Vop hrep hlocalRaw
  · intro ψcorrected hψcorrected
    obtain ⟨Ccorrected, Lcorrected, hCcorrected, hLcorrected, hrowCorrected⟩ :=
      exists_uniform_measured_density_row_bounds H χ χsrc ψcorrected
        (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 1)
        (FixedCutoffs.periodic_smooth hrMeasure hMeasureCell 2) hψcorrected
        Cimage (fun m ↦ (hCimage m).le) CrawCorrected hCrawCorrected Kin z
        (fun i ↦ NormedSpace.normalize (ηb i)) ha' hwidth χinitial
    refine ⟨Ccorrected, Lcorrected, hCcorrected, hLcorrected, ?_⟩
    intro σ hσ vDensity hvDensity hinterval hlow Hhigh d e
    have hσCorrected : σ ∈ Ioc (0 : ℝ) sCorrected :=
      ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    have hσImage : σ ∈ Ioc (0 : ℝ) sImage :=
      ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    choose _hplateau Vop hrep _hunique hlocalRaw _hrealMem _hrealBound _hdensity using
      fun i ↦ hrawCorrected i σ hσCorrected (vDensity i) (hvDensity i) (hinterval i) (hlow i)
    have hArep (i : ι) (w : ComplexOutputL2 n) :
        (restrictCarrier χ (Vop i)).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w := by
      have hs := NormalizedMeasurement.supplied_carrier_common_measurement (d i)
        hrMeasure (ha' i) hMeasureCell (hlocal i) (hra i) rfl (fun _ _ ↦ rfl) rfl
      exact ((hs.2.2.2.2.2.2.2.2 (Vop i)).2.2
        (fun w ↦ ⟨(memLp_congr_ae (hrep i w)).mp (Lp.memLp ((Vop i).adjoint w)), hrep i w⟩) w).2
    have hUunique (i : ι) (B : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (hB : ∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) :
        B = restrictCarrier χ (Vop i) := by
      have he := DerivativeKernels.literalCarrierAdjointOperator_unique (e i)
        B.adjoint (restrictCarrier χ (Vop i)).adjoint hB (hArep i)
      simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg ContinuousLinearMap.adjoint he
    refine ⟨Vop, hrep, hArep, hUunique, ?_⟩
    intro selectedCoeff hselected B hB
    have hcoeffEq : selectedCoeff = coeff σ := by
      funext j
      apply ContinuousMap.ext
      intro x
      exact (hselected j x).trans (hformula σ hσImage j x).symm
    have hBEq : B = fun i ↦ restrictCarrier χ (Vop i) := funext fun i ↦ hUunique i (B i) (hB i)
    subst selectedCoeff B
    exact hrowCorrected (coeff σ) (hcoeff σ) (fun m j x ↦ (hjets m σ hσImage j x).2)
      (fun i ↦ PositiveBackground.densityOnInitialLabels (vDensity i)) d Vop hrep hlocalRaw

end JanetCartan.ContinuumRow.NormalizedSelection
