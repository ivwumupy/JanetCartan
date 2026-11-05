module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedMeasuredSource.ZeroGap

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.MeasuredZeroGap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.MeasuredImage
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CurrentTransfer
/-!
# Source inverse on the prescribed measured row

Carry the corrected raw caps through the actual source construction. The
incidence cover and its masks are chosen once by `RawCappedInitialization`;
every density carrier, normal comparison and inverse uses that same row.
The supplied smooth exterior in the corrected raw continuation is retained
before all source scales and densities. This closes the corresponding
producer application inside the common reference initializer, without
identifying separately selected rows.

Sources: `app:ch_background:prop:bg-normalized`,
`app:ch_background:prop:bg-inverse`, `app:ch_background:prop:bg-adjoint`,
and `new:sec:order-of-choices`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumNormal.SourceDensityLimitRealization
open ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open FullPhaseCharts ActualPhase ActualComparison
open CarrierVariation.FamilyInputs PositiveReference ProjectedStressFrame
open PositiveReference.FlowConstruction RetainedRowGeometry
open NullTransport ActualFlow FlowAmplitude CarrierSobolev GeometricProfile
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.PhaseExtension CommonMeasurement
open NormalizedBackground.SourceGeometry Pseudodifferential AmplitudeBound PeriodicLocalL2


/-- Construct the local and global source coercivity gaps on the original
measured incidence family. The source cap precedes every original density and
scale. The actual image-normal threshold and finite carrier-normal comparison
cost at most half of the smaller zero-density gap, preserving its inner radius
and exterior square. Literal test actions identify the comparison's zero
carrier with the constructed zero-density carrier; the current test and adjoint
actions remain attached to the same bounded operator. All original cover,
mask, measurement, low/high profile and scalar-domain clauses are retained.

Consumers: `ContinuumInverse` and `PositiveBackground.SourceInverse`
(`app:ch_background:eq:bg-local-bound`, `app:ch_background:eq:bg-global-bound`,
`app:ch_background:prop:bg-normalized`, `new:sec:order-of-choices`). -/
theorem exists_finite_prescribed_measured_source_gap
    {n : ℕ} {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C) (hn : 5 ≤ n) (H : FlatReference n)
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
    ∃ δ > (0 : ℝ),
    ∃ Dc : ι → CoefficientNormCharts n,
    ∃ p₀ : ι → InputVariables n, ∃ q₀ : ι → Variables n × Euclidean 2,
    ∃ ρ τ : ι → ℝ, ∃ W Bi : ι → Set (InputVariables n), ∃ It : ι → Set ℝ,
    ∃ A : ι → InputVariables n ≃L[ℝ] Variables n × Euclidean 2,
    ∃ ε gap : ι → ℝ, ∃ Qc Ωi : ι → Set (Variables n × Euclidean 2),
    ∃ βphase cJphase : ι → ℝ,
    ∃ Vphase Lphase : ι → Set (ℝ × Euclidean (n - 1)),
    ∃ Gphase : ι → (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)),
    (∀ i : ι,
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
    let D := Dc i
    let p₀ := p₀ i
    let q₀ := q₀ i
    let ρ := ρ i
    let τ := τ i
    let W := W i
    let Bi := Bi i
    let It := It i
    let A := A i
    let ε := ε i
    let gap := gap i
    let Qc := Qc i
    let Ωi := Ωi i
    let β := βphase i
    let cJ := cJphase i
    let Vphase := Vphase i
    let Lphase := Lphase i
    let G := Gphase i;
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
    (∀ σ ∈ Ioc (0 : ℝ) σ₀,
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
    (∀ ψcorrected : C(Torus n, ℝ), IsSmoothPeriodic ψcorrected →
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
              Lcorrected s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + Hhigh (s + 1) * ‖w‖)) ∧
    let Ωflow := fun i : ι ↦ Ω i.1.1.1.1 i.2 (selected i)
    let zScalar := fun i : ι ↦ zCell i.1.1.1.1 i.2 (selected i)
    let ρflow := fun i : ι ↦ ρc i.1.1.1.1 i.2 (selected i)
    let Rcflow := fun i : ι ↦ Rc i.1.1.1.1 i.2 (selected i)
    let Bflow := fun i : ι ↦ M i.1.1.1.1 i.2 (selected i)
    let τflow := fun i : ι ↦ τlead i.1.1.1.1 i.2 (selected i)
    let Lscalar := fun i : ι ↦ L i.1.1.1.1 i.2 (selected i)
    ∃ Cnorm Cpdo : ι → ℝ, (∀ i, 0 < Cnorm i) ∧ (∀ i, 0 < Cpdo i) ∧
    ∃ Bhigh : ι → ℕ → ℝ, (∀ i p, 0 < Bhigh i p) ∧
    ∃ densityCap > (0 : ℝ), densityCap ≤ σ₀ ∧ densityCap ≤ 1 / 8 ∧
    ∃ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) densityCap → (i : ι) →
      Chart (family i) (Ωflow i) (closedBall ((0 : Euclidean n), zScalar i) (ρflow i))
        ((0 : Euclidean (n - 1)), zScalar i) (Rcflow i) (Bflow i) (τflow i) (rowi i) (coli i)
        (sourceDilation H.map σ),
    (∀ σ hσ i,
      ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
          ℝ × (Euclidean (n - 1) × Euclidean 3),
        ODE.IsSmoothFlowOn (liftedDirection (family i) (current σ hσ i).Q (rowi i) (coli i))
          (0, ((0 : Euclidean (n - 1)), zScalar i)) (Rcflow i) (Rcflow i / 2)
          (existenceTime (Rcflow i) (liftedLowBound (family i) (Bflow i))) Ψ ∧
        (current σ hσ i).forward = forwardFromLift Ψ ∧
        (current σ hσ i).inverse = footpointFromLift Ψ ∧
        IsImmersionOn (sourceDilation H.map σ) U ∧
        HasFullNormalRankOn (sourceDilation H.map σ) U ∧
        cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
          ((current σ hσ i).Q.1 - fun _ ↦ cubeStress n) < δ ∧
        EqOn (current σ hσ i).forward (sourceTransportFlow (seed i).forward σ)
          (Ioo (-τflow i) (τflow i) ×ˢ
            ball ((0 : Euclidean (n - 1)), zScalar i) (Rcflow i / 8)) ∧
        EqOn (current σ hσ i).inverse (sourceTransportFlow (seed i).inverse σ)
          (current σ hσ i).D ∧
        EqOn ((current σ hσ i).scalar (fun _ ↦ σ))
          (sourceAmplitude ((seed i).scalar (fun _ ↦ 1)) σ)
          ((coordinates (adaptedCoordinates (family i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
        EqOn (fun w ↦ (current σ hσ i).scalar (fun _ ↦ σ) w •
            carrierNullvector (family i) (current σ hσ i).Q (coli i) w)
          (sourceAmplitude (fun w ↦ (seed i).scalar (fun _ ↦ 1) w •
            carrierNullvector (family i) (seed i).Q (coli i) w) σ)
          ((coordinates (adaptedCoordinates (family i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
        ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
          EqOn ((current σ hσ i).scalar (fun q ↦ σ * weight q))
            (fun w ↦ sourceAmplitude ((seed i).scalar (fun _ ↦ 1)) σ w *
              weight ((current σ hσ i).inverse (coordinates (adaptedCoordinates (family i).data.adapted) w)))
            ((coordinates (adaptedCoordinates (family i).data.adapted)) ⁻¹' (current σ hσ i).D)) ∧
      (∀ σ hσ, let current := current σ hσ
      ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4))) →
      (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4) → 0 < 1 + v i q) →
      (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8) →
        1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8))
        (2 * (n + 1) + 14) (v i) ≤ 1) →
      let e := fun i ↦ data (family i) (current i).Q (sourceDilation H.map σ) (rowi i) (coli i)
        (current i).forward (current i).inverse (fun q ↦ positiveDensityAmplitude σ (v i q))
        (ha' i) (hcell i)
        (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
        FixedCutoffs.highFrequency
      let d := fun i ↦ coefficientsOfCarrier (e i) (FixedCutoffs.physical (ha' i) 1)
      let J := fun i ↦ symbolJacobian (family i) (current i).Q
      let u := fun i ↦ symbolInverse (family i) (current i).Q (z i) (ηb i) (r i) (6 * a i)
      let Ωi := fun i ↦ symbolDomain (family i) (current i).Q (z i) (ηb i) (r i) (6 * a i)
      let S := fun i ↦ closedBall (spectatorCenter (z i)) (a' i / 2)
      ∃ hsupport : ∀ i x, (d i).measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' i,
      ∃ hbsmooth : ∀ i, ContDiff ℝ ∞
        (Function.uncurry (fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i))),
      ∃ hA : ∀ i l j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i) ξ z l j)
        (2 * (n + 1) + 1) (Cpdo i),
      ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n, (∀ i,
        ‖(Vop i)‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * (a' i)) * (Cnorm i))) ∧
        ‖(Vop i).adjoint‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * (a' i)) * (Cnorm i))) ∧
        (∀ f : carrierInitialTestSpace n,
          (Vop i) (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ (e i).outputChart → (Vop i) f x = 0) ∧
        (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ f : carrierInitialTestSpace n,
            Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) → Wop = (Vop i)) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
          (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
        (realQuadratureChannel (Vop i)).comp (realQuadratureChannel (Vop i)).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator (by have := (rowi i).isLt; omega) (4 * (a' i))
              (fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i)) (hbsmooth i)
              (fullReflectedMatrixAmplitude_supportedInCenteredBox (d i) (J i) (u i) (Ωi i) (S i) (4 * (a' i)) (hsupport i))
              (Cpdo i) (fun l j ξ is his ↦ (hA i) l j ξ is (by omega)))) ∧
        (∀ p l j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i) ξ z l j) p
          ((Bhigh i) p * (1 + cNorm (closedBall ((0 : Euclidean (n - 1)), (zScalar i)) ((Lscalar i) / 8)) p (v i)))) ∧
        ∀ {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2), 6 * b < (a' i) →
          let χ := FixedCutoffs.periodic (n := n) hb hbcell 1
          let Vb := CommonMeasurement.restrictCarrier χ (Vop i)
          let eb := data (family i) (current i).Q (sourceDilation H.map σ) (rowi i) (coli i) (current i).forward (current i).inverse
            (fun q ↦ positiveDensityAmplitude σ ((v i) q)) hb hbcell
            (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
            FixedCutoffs.highFrequency
          let db := coefficientsOfCarrier eb (FixedCutoffs.physical hb 1)
          let Aop := vectorTwoPositionL2Operator (by have := (rowi i).isLt; omega) (4 * (a' i))
            (fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i)) (hbsmooth i)
            (fullReflectedMatrixAmplitude_supportedInCenteredBox (d i) (J i) (u i) (Ωi i) (S i) (4 * (a' i)) (hsupport i))
            (Cpdo i) (fun l j ξ is his ↦ (hA i) l j ξ is (by omega))
          let multiplier := freezingVectorPhysicalMultiplier (FixedCutoffs.physical hb 1)
            (FixedCutoffs.physical hb 1).continuous (FixedCutoffs.physical hb 1).hasCompactSupport
          ‖Vb‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * (a' i)) * (Cnorm i))) ∧
          (∀ f : carrierInitialTestSpace n,
            Vb (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral eb f.val) ∧
          (∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral eb w) 2 (carrierMeasure n) ∧
            Vb.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral eb w) ∧
          (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ eb.outputChart → Vb f x = 0) ∧
          carrierChannel Vb ∘L (carrierChannel Vb).adjoint =
            realOutputCompression (transferOperator (multiplier ∘L Aop ∘L multiplier)) ∧
          db = CommonMeasurement.restrictCoefficients (d i) (FixedCutoffs.physical hb 1) ∧
          fullReflectedMatrixAmplitude db (J i) (u i) (Ωi i) (S i) =
            CommonMeasurement.restrictAmplitude (fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i))
              (FixedCutoffs.physical hb 1)) ∧
      ∀ i,
        let unit := normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
          (seed i).forward (seed i).inverse (fun _ ↦ 1) (ha' i) (hcell i)
          (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
            (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency σ
        let normalized := weightNormal unit
          (fun p ↦ Real.sqrt (1 + v i (densityFootpoint (family i) (current i).inverse p)))
        carrierKernel (e i) = carrierKernel normalized ∧
        carrierTestIntegral (e i) = carrierTestIntegral normalized ∧
        carrierAdjointIntegral (e i) = carrierAdjointIntegral normalized ∧
        (∀ f : carrierInitialTestSpace n,
          Vop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral normalized f.val) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral normalized w) 2 (carrierMeasure n) ∧
          (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalized w) ∧
        (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalized w) →
          Wop = Vop i) ∧
        (v i = (fun _ ↦ 0) → ∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral unit w) →
          Wop = Vop i) ∧
        ∀ {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2), 6 * b < a' i →
          let unitb := normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
            (seed i).forward (seed i).inverse (fun _ ↦ 1) hb hbcell
            (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
              (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency σ
          let normalizedb := weightNormal unitb
            (fun p ↦ Real.sqrt (1 + v i (densityFootpoint (family i) (current i).inverse p)))
          let Vb := CommonMeasurement.restrictCarrier (FixedCutoffs.periodic hb hbcell 1) (Vop i)
          (∀ f : carrierInitialTestSpace n,
            Vb (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral normalizedb f.val) ∧
          (∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral normalizedb w) 2 (carrierMeasure n) ∧
            Vb.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalizedb w) ∧
          (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalizedb w) →
            Wop = Vb) ∧
          (v i = (fun _ ↦ 0) → ∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral unitb w) →
            Wop = Vb ∧ ∀ f : carrierInitialTestSpace n,
              Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral unitb f.val)) ∧
    (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) densityCap) i,
      RetainedFrozen.UnitRealization.UnitCarrierOutput (family i) (current σ hσ i).Q H.map
        (rowi i) (coli i) (seed i).forward (seed i).inverse (z i) (ηb i) (r i) (a i) (r' i) (a' i)
        (hr' i) (ha' i) (hcell i) (hηb i) (2 * (n + 1)) le_rfl) ∧
    InitializedFrozenSeedGap family (fun i ↦ (seed i).Q) H.map rowi coli
      (fun i ↦ (seed i).forward) (fun i ↦ (seed i).inverse) z ηb r' a'
      hr' ha' hcell hηb zScalar Lscalar ∧
    let Qcurrent : (i : ι) → ℝ → {QF : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ QF U ∧ cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
        (QF - fun _ ↦ cubeStress n) < (family i).family.threshold} := fun i σ ↦ if hσ : σ ∈ Ioc (0 : ℝ) densityCap
      then (current σ hσ i).Q else (seed i).Q
    let μ := 2 * (n + 1)
    let angular := fun i ↦ angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1
    let d := fun i σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse (fun _ ↦ 1)
        (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency σ) (FixedCutoffs.physical (ha' i) 1)
    let J := fun i σ ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (family i))
      (normalizedTransportPosition (family i) (seed i).Q σ)
    let u := fun i σ ↦ if σ = 0 then frozenSymbolInverse (family i) (seed i).Q (z i) (ηb i) (r i) (6 * a i)
      else symbolInverse (family i) (Qcurrent i σ) (z i) (ηb i) (r i) (6 * a i)
    let S := fun i ↦ closedBall (spectatorCenter (z i)) (a' i / 2)
    let b := fun i σ (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      fullReflectedMatrixAmplitude
        {d i σ with normal := fun p ↦ Real.sqrt (1 + v
          (sourceDensityFootpointExtension (family i) (seed i).inverse (σ, p))) • (d i σ).normal p}
        (J i σ) (u i σ) (Ωi i) (S i)
    let eZero : ι → (Euclidean (n - 1) × Euclidean 3 → ℝ) → CarrierData n (embeddingDimension n) :=
      fun (i : ι) (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      SourceDensityLimitRealization.weightNormal (n := n) (N := embeddingDimension n)
        (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
          (fun _ ↦ 1) (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency 0)
        (fun p : Euclidean n × CarrierParameter ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension (family i) (seed i).inverse (0, p))))
    (let image := FrozenImageComparison.fixedPeriodicChannel hrMeasure hMeasureCell
        (FrozenCoercivity.frozenImageArrays (projectedStress H.map 0))
    ∃ g > (0 : ℝ), ∃ (rInner : ℝ) (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2),
    ∃ Mlimit ≥ (0 : ℝ), rInner ≤ rMeasure ∧
      0 < NormalAugmentation.globalGap g Mlimit ∧
      ∃ sourceCap > (0 : ℝ), ∃ hcapSource : sourceCap ≤ densityCap,
        sourceCap ≤ σ₀ ∧ sourceCap ≤ 1 ∧
      ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4))) →
      (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4) → 0 < 1 + v i q) →
      (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8) →
        1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8)) (μ + 14) (v i) ≤ 1) →
      ∃ Vzero : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i,
          (∀ f : carrierInitialTestSpace n,
            Vzero i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (eZero i (v i)) f.val) ∧
          (∀ f : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (eZero i (v i)) f) 2 (carrierMeasure n) ∧
            (Vzero i).adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral (eZero i (v i)) f) ∧
          (∀ Wzero : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ f : carrierInitialTestSpace n,
              Wzero (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (eZero i (v i)) f.val) →
              Wzero = Vzero i)) ∧
        let Wzero := fun i ↦ restrictCarrier χ (Vzero i)
        ‖physicalRow image Wzero‖ ≤ Mlimit ∧
        (∀ w : OutputL2 n,
          (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
          g * ‖w‖ ^ 2 ≤ ‖(physicalRow image Wzero).adjoint w‖ ^ 2) ∧
        (∀ w : OutputL2 n, NormalAugmentation.globalGap g Mlimit * ‖w‖ ^ 2 ≤
          inner ℝ (augmentedNormal image Wzero (innerCutoff hrInner hInnerCell) w) w) ∧
        (∀ w : OutputL2 n, NormalAugmentation.globalGap g Mlimit * ‖w‖ ^ 2 ≤
          ‖(augmentedRow image Wzero (innerCutoff hrInner hInnerCell)).adjoint w‖ ^ 2) ∧
        (∀ w : OutputL2 n, ∀ᵐ x ∂volume,
          centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
            exteriorChannel (innerCutoff hrInner hInnerCell) w x = 0) ∧
        ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) sourceCap),
        let cσ := current σ ⟨hσ.1, hσ.2.trans hcapSource⟩
        let e : ι → CarrierData n (embeddingDimension n) := fun i ↦
          data (family i) (cσ i).Q (sourceDilation H.map σ) (rowi i) (coli i)
            (cσ i).forward (cσ i).inverse (fun q ↦ positiveDensityAmplitude σ (v i q))
            (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency
        ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ Wop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ i f, Wop i (carrierInitialTestToLp f) =ᵐ[volume]
              carrierTestIntegral (e i) f.val) → Wop = Vop) ∧
          (∀ i,
            (∀ f : carrierInitialTestSpace n,
              Vop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) ∧
            (∀ w : ComplexOutputL2 n,
              MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
              (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w)) ∧
          let imageCurrent := imageChannel (coeff σ) χ χsrc
          let Wcurrent := fun i ↦ restrictCarrier χ (Vop i)
          ‖physicalRow imageCurrent Wcurrent‖ ≤ Real.sqrt
            (Mlimit ^ 2 + min g (NormalAugmentation.globalGap g Mlimit) / 2) ∧
          (∀ w : OutputL2 n,
            (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
            (g / 2) * ‖w‖ ^ 2 ≤ ‖(physicalRow imageCurrent Wcurrent).adjoint w‖ ^ 2) ∧
          (∀ w : OutputL2 n, (NormalAugmentation.globalGap g Mlimit / 2) * ‖w‖ ^ 2 ≤
            inner ℝ (augmentedNormal imageCurrent Wcurrent (innerCutoff hrInner hInnerCell) w) w) ∧
          (∀ w : OutputL2 n, (NormalAugmentation.globalGap g Mlimit / 2) * ‖w‖ ^ 2 ≤
            ‖(augmentedRow imageCurrent Wcurrent (innerCutoff hrInner hInnerCell)).adjoint w‖ ^ 2)) ∧
    ∃ Ccompare Bsource Mzero : ι → ℝ,
    (∀ i, 0 < Ccompare i) ∧ (∀ i, 0 < Bsource i) ∧ (∀ i, 0 ≤ Mzero i) ∧
    ∀ targetGap > (0 : ℝ),
    let tol := targetGap / (4 * ((Fintype.card ι : ℝ) + 1))
    ∃ cap > (0 : ℝ), ∃ hcapSource : cap ≤ densityCap, cap ≤ 1 ∧
    ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap),
    ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4))) →
      (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4) → 0 < 1 + v i q) →
      (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8) →
        1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8)) (μ + 14) (v i) ≤ 1) →
    let cσ := current σ ⟨hσ.1, hσ.2.trans hcapSource⟩
    let e : ι → CarrierData n (embeddingDimension n) := fun i ↦
      data (family i) (cσ i).Q (sourceDilation H.map σ) (rowi i) (coli i) (cσ i).forward (cσ i).inverse
        (fun q ↦ positiveDensityAmplitude σ (v i q)) (ha' i) (hcell i) (angular i)
        FixedCutoffs.highFrequency
    let pair := fun (t : Fin 2) i ↦ b i (![σ, 0] t) (v i)
    (∀ i j k, HasAmplitudeDerivativeBound (fun ξ z ↦ pair 0 i ξ z j k - pair 1 i ξ z j k) μ tol) ∧
    ∃ hb : ∀ t i, ContDiff ℝ ∞ (Function.uncurry (pair t i)),
    ∃ hs : ∀ t i ξ j k, SupportedInCenteredBox (4 * a' i) (fun z ↦ pair t i ξ z j k),
    ∃ hB : ∀ t i j k, HasAmplitudeDerivativeBound (fun ξ z ↦ pair t i ξ z j k) μ (Bsource i),
    let Aop := fun t i ↦ vectorTwoPositionL2Operator (by omega) (4 * a' i) (pair t i) (hb t i) (hs t i)
      (Bsource i) (hB t i)
    let Nop := fun t i ↦ realOutputCompression (transferOperator (Aop t i))
    ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ Wop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i f, Wop i (carrierInitialTestToLp f) =ᵐ[volume]
          carrierTestIntegral (e i) f.val) → Wop = Vop) ∧
      (∀ i, ‖Vop i‖ ≤ Real.sqrt ((n : ℝ) ^ (2 : ℕ) * (fixedBoxAmplitudeConstant n (4 * a' i) * Ccompare i))) ∧
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
  classical
  have selectedResult := exists_finite_prescribed_measured_zero_gap hD hn H hUH hbounded T I Ω hΩ
    zCell ρc Rc M τlead row col hKΩ hpatchStrong hM hτeq hΩscale
    hRc hτ hτR hbuffer hphysical c₀ htrans R V hR hRphysical hRU hV hVP hflow
    L Mforward hL hMforward hforward hRtime hlabel hcover hcap aExtra
  choose cell hcell centers εcover hεcover hcover' hdomain hgram
    t r a r' a' ht hr ha hr' ha' hlocal hηb htnorm hdir hExtraCap
    hgeometry hmask b hb hbcell hbH hbhalf hba hsampling
    δ hδ Dc p₀ q₀ ρ τ W Bi It A ε gap Qc Ωi βphase cJphase Vphase Lphase Gphase hconic
    χinitial rMeasure hrMeasure hMeasureCell hrb hrH hrhalf hra
    χcoeff hχcoeff hχrange hχcompact hχsupport hχplateau
    σ₀ hσ₀ hσ₀1 coeff Cimage Cbound Lbound hCimage hCbound hLbound
    hcoeff hzero hformula hjets hmeasured hcorrected
    Cnorm Cpdo hCnorm hCpdo Bhigh hBhigh densityCap hdensityCap hcapMeasured hcap8
    current hcurrent hcarriers hunit hseedGap hzeroGap hnormal using selectedResult
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  let family := fun i : ι ↦ T i.1.1.1.1 i.2
  let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
  let ηb := fun i : ι ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint
    (t i • i.1.1.1.2)
  let selected := fun i : ι ↦ cell i.1.1 i.2
  let seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
  let rowi := fun i : ι ↦ row i.1.1.1.1 i.2 (selected i)
  let coli := fun i : ι ↦ col i.1.1.1.1 i.2 (selected i)
  refine ⟨cell, hcell, centers, εcover, hεcover, hcover', hdomain, hgram,
    t, r, a, r', a', ht, hr, ha, hr', ha', hlocal, hηb, htnorm, hdir, hExtraCap,
    hgeometry, hmask, b, hb, hbcell, hbH, hbhalf, hba, hsampling,
    δ, hδ, Dc, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi, βphase, cJphase, Vphase, Lphase, Gphase, hconic,
    χinitial, rMeasure, hrMeasure, hMeasureCell, hrb, hrH, hrhalf, hra,
    χcoeff, hχcoeff, hχrange, hχcompact, hχsupport, hχplateau,
    σ₀, hσ₀, hσ₀1, coeff, Cimage, Cbound, Lbound, hCimage, hCbound, hLbound,
    hcoeff, hzero, hformula, hjets, hmeasured, hcorrected,
    Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh, densityCap, hdensityCap,
    hcapMeasured, hcap8, current, hcurrent, hcarriers, hunit,
    hseedGap, ?_⟩
  refine ⟨?_, hnormal⟩
  obtain ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG, hzeroCoercive⟩ := hzeroGap
  let G := NormalAugmentation.globalGap g Mlimit
  let κ := min g G
  have hκ : 0 < κ := lt_min hg hG
  obtain ⟨Ccompare, Bsource, Mzero, hCcompare, hBsource, hMzero, hcompare⟩ := hnormal
  obtain ⟨capCarrier, hcapCarrier, hcapCarrierSource, hcapCarrierOne, hcompare⟩ := hcompare κ hκ
  obtain ⟨Bimage, hBimage, himageTolerance⟩ :=
    ActualConstruction.exists_supplied_measurement_imageNormal_threshold
      H hrMeasure hMeasureCell hrhalf χcoeff hχcoeff hχsupport hχplateau (coeff 0) hzero
  obtain ⟨capImage, hcapImage, hcapImageOne, himageError⟩ :=
    himageTolerance (κ / 4) (by positivity)
  let cap := min capCarrier capImage
  have hcap : 0 < cap := lt_min hcapCarrier hcapImage
  have hcapSource : cap ≤ densityCap := (min_le_left _ _).trans hcapCarrierSource
  have hcapMeasured' : cap ≤ σ₀ := hcapSource.trans hcapMeasured
  let χ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 1
  let χsrc := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 2
  let image₀ := FrozenImageComparison.fixedPeriodicChannel hrMeasure hMeasureCell
    (FrozenCoercivity.frozenImageArrays (projectedStress H.map 0))
  refine ⟨g, hg, rInner, hrInner, hInnerCell, Mlimit, hMlimit, hrμ, hG,
    cap, hcap, hcapSource, hcapMeasured', (min_le_right _ _).trans hcapImageOne, ?_⟩
  intro v hv hpos hinterval hvnorm
  obtain ⟨Vzero, hzeroActions, hzeroBound, hzeroLocal, hzeroGlobal, hzeroAdjoint, hexterior⟩ :=
    hzeroCoercive v hv hpos hinterval hvnorm
  refine ⟨Vzero, hzeroActions, hzeroBound, hzeroLocal, hzeroGlobal, hzeroAdjoint, hexterior, ?_⟩
  intro σ hσ
  have hσCarrier : σ ∈ Ioc (0 : ℝ) capCarrier := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hσImage : σ ∈ Ioc (0 : ℝ) capImage := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hσMeasured : σ ∈ Ioc (0 : ℝ) σ₀ := ⟨hσ.1, hσ.2.trans hcapMeasured'⟩
  obtain ⟨_hsmall, _hb, _hs, _hB, Vop, huniq, _hVbound, hreal, _hsum, _hmeas,
      Vcmp, _hVcmp, hcmpActions, _hsumCmp, hmeasCmp⟩ :=
    hcompare σ hσCarrier v hv hpos hinterval hvnorm
  have hVcmp : Vcmp = Vzero := funext fun i ↦
    (hzeroActions i).2.2 (Vcmp i) (hcmpActions i).1
  have hcarrier := hmeasCmp χ (FixedCutoffs.periodic_norm_le_one hrMeasure hMeasureCell 1)
  rw [hVcmp] at hcarrier
  let imageCurrent := imageChannel (coeff σ) χ χsrc
  let Wcurrent := fun i ↦ restrictCarrier χ (Vop i)
  let Wzero := fun i ↦ restrictCarrier χ (Vzero i)
  have himage : ‖NormalPerturbation.normal imageCurrent - NormalPerturbation.normal image₀‖ ≤ κ / 4 := by
    have heq : projectedStress H.map 0 = cubeStress n :=
      funext (projectedStress_flatReference_zero H)
    dsimp only [image₀]
    rw [heq]
    exact (himageError σ hσImage (coeff σ) (hformula σ hσMeasured)).2.2.le
  let Acurrent := physicalRow imageCurrent Wcurrent
  let Azero := physicalRow image₀ Wzero
  have hcomparison : ‖NormalPerturbation.normal Acurrent - NormalPerturbation.normal Azero‖ ≤ κ / 2 := by
    dsimp only [Acurrent, Azero, NormalPerturbation.normal]
    rw [physicalRow_normal, physicalRow_normal, add_sub_add_comm, ← Finset.sum_sub_distrib]
    exact ((norm_add_le _ _).trans (add_le_add himage hcarrier)).trans (by linarith)
  have hcurrentBound : ‖Acurrent‖ ≤ Real.sqrt (Mlimit ^ 2 + κ / 2) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    have hnorm := norm_le_norm_add_norm_sub
      (NormalPerturbation.normal Azero) (NormalPerturbation.normal Acurrent)
    rw [NormalPerturbation.norm_normal, NormalPerturbation.norm_normal] at hnorm
    rw [norm_sub_rev (NormalPerturbation.normal Azero) (NormalPerturbation.normal Acurrent)] at hnorm
    have hsq : ‖Azero‖ ^ 2 ≤ Mlimit ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzeroBound 2
    linarith only [hnorm, hcomparison, hsq]
  have hlocal (w : OutputL2 n)
      (hw : ∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) :
      g / 2 * ‖w‖ ^ 2 ≤ ‖Acurrent.adjoint w‖ ^ 2 := by
    have hgapNormal : ∀ f ∈ {f : OutputL2 n | ∀ᵐ x ∂volume,
        x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → f x = 0},
        g * ‖f‖ ^ 2 ≤ RCLike.re (inner ℝ (NormalPerturbation.normal Azero f) f) := by
      intro f hf
      apply (hzeroLocal f hf).trans_eq
      simpa only [ContinuousLinearMap.adjoint_adjoint, NormalPerturbation.normal] using
        Azero.adjoint.apply_norm_sq_eq_inner_adjoint_left f
    have h := NormalPerturbation.quadratic_lower_bound_of_norm_sub_le
      (NormalPerturbation.normal Azero) (NormalPerturbation.normal Acurrent)
      {f | ∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → f x = 0}
      (g := g) (ε := g / 2) hgapNormal
      (hcomparison.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))) w hw
    have heq := Acurrent.adjoint.apply_norm_sq_eq_inner_adjoint_left w
    simp only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real,
      ContinuousLinearMap.comp_apply] at heq
    change (g - g / 2) * ‖w‖ ^ 2 ≤ inner ℝ (Acurrent (Acurrent.adjoint w)) w at h
    rw [← heq] at h
    convert h using 1
    ring
  have haugmented : ‖augmentedNormal imageCurrent Wcurrent (innerCutoff hrInner hInnerCell) -
      augmentedNormal image₀ Wzero (innerCutoff hrInner hInnerCell)‖ ≤ κ / 2 := by
    have heq : augmentedNormal imageCurrent Wcurrent (innerCutoff hrInner hInnerCell) -
        augmentedNormal image₀ Wzero (innerCutoff hrInner hInnerCell) =
        NormalPerturbation.normal Acurrent - NormalPerturbation.normal Azero := by
      rw [augmentedNormal_eq_sum, augmentedNormal_eq_sum]
      simp only [NormalPerturbation.normal, Acurrent, Azero, physicalRow_normal]
      abel
    rw [heq]
    exact hcomparison
  have hcurrentGlobal (w : OutputL2 n) : G / 2 * ‖w‖ ^ 2 ≤
      inner ℝ (augmentedNormal imageCurrent Wcurrent (innerCutoff hrInner hInnerCell) w) w :=
    augmented_half_gap_of_normal_comparison imageCurrent image₀ Wcurrent Wzero
      (innerCutoff hrInner hInnerCell) univ (fun f _ ↦ hzeroGlobal f) haugmented
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) w (mem_univ w)
  refine ⟨Vop, huniq, fun i ↦ ⟨(hreal i).1, (hreal i).2.1⟩,
    hcurrentBound, hlocal, hcurrentGlobal, ?_⟩
  intro w
  have heq := (augmentedRow imageCurrent Wcurrent
    (innerCutoff hrInner hInnerCell)).adjoint.apply_norm_sq_eq_inner_adjoint_left w
  apply (hcurrentGlobal w).trans_eq
  simpa only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real, augmentedNormal] using heq.symm


end JanetCartan.ContinuumRow.NormalizedSelection
