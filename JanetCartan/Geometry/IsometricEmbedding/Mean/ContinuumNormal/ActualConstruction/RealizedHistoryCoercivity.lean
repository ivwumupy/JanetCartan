module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.FiniteRealizedVariation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.HistoryImage
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.MeasuredPerturbation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedHistoryNeighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization

/-!
# Constructed carriers and coercivity along a retained history

Use the actual finite full-amplitude comparison and the original history
neighborhood to construct the current density carriers. The geometric history
neighborhood proves immersion, full normal rank, the low norm and the separate
metric and normal gaps. The actual image coefficients are periodized on the
supplied cutoff. Dense-test uniqueness retains the supplied positive-reference
operators, and both normal comparisons give half-gaps with the same exterior.

The reference gaps come from the positive-source coercivity construction.
Original initializer charts, selected geometry and forward bounds still have
to be instantiated on that same finite family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection NormalizedCarrierProfiles
open CarrierVariation.FamilyInputs PositiveReference PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude HamiltonPhase RetainedRowGeometry
open NormalizedBackground.SourceGeometry
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open Pseudodifferential AmplitudeBound PeriodicLocalL2 RetainedFrozen
open LeadingWave LeadingWave.JointReconstruction AmbientResponse GeometricProfile
open ProjectedStressFrame WideDensity ImageGeometry ImageGeometry.Periodization

variable {n : ℕ} {ι : Type} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    {Ω K : ι → Set (Euclidean n × Euclidean 3)}
    {z₀ : ι → Euclidean 3} {Rc B τ : ι → ℝ} {row col : ι → Fin n}

variable
  (hdomain : ∀ i, ∀ z ∈ (T i).data.localReference.stateDomain, z.1 ∈ U)
  (hgeometry : ∀ i, ∃ (R : ℝ)
    (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1)))),
    0 < R ∧ R < (T i).data.localReference.stateRadius ∧
    (∀ Q, ∀ q ∈ ball ((0 : ℝ), (T i).data.adapted.baseData) (3 * (T i).family.sourceRadius),
      ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ ((T i).family.flow Q).augmentedProjection q) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
    (∀ Q, ∀ q ∈ ((T i).family.flow Q).time ×ˢ ((T i).family.flow Q).parameters,
      (((T i).family.flow Q).position q, ((T i).family.flow Q).momentum q) ∈
        closedBall (0, (T i).data.center) R) ∧
    (∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold},
      ∀ z ∈ closedBall (0, (T i).data.center) R,
      ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, (T i).data.adapted.normal⟫_ℝ ≠ 0))

include hdomain hgeometry

/-- One frequency threshold constructs the current carriers and preserves half
the retained reference gaps for every admissible history and original positive
density. The full-amplitude, image and geometric history comparisons are applied to
their actual producers; no current immersion, rank, low norm, metric gap,
normal gap, normal identity or forward/adjoint-output record is assumed.
The actual smooth image coefficients precede the density, and the supplied
reference row is identified by its literal test action. The
source gap comes from `exists_realized_retained_incidence_source_coercivity`;
the geometric callback is the original selected joint geometry. Constants and
thresholds precede the density and history. Consumers: `CoerciveNormal` and
`ContinuumInverse` (`main:eq:displacement-budget`,
`app:ch_background:eq:bg-local-bound`, `app:ch_background:eq:bg-global-bound`). -/
theorem exists_initialScale_for_realized_retained_history_coercivity
    {c₁ C : ι → ℝ}
    (hP : ∀ i : ι, (P i).IsValid (c₁ i) (C i))
    (hΩ : ∀ i : ι, IsOpen (Ω i))
    (hK : ∀ i : ι, IsCompact (K i))
    (hKΩ : ∀ i : ι, (K i) ⊆ (Ω i))
    (hRc : ∀ i : ι, 0 < (Rc i))
    (hB : ∀ i : ι, 0 ≤ (B i))
    (hτ : ∀ i : ι, 0 < (τ i))
    (hbuffer : ∀ i : ι, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), (z₀ i))) (Rc i)) (K i))
    (hτeq : ∀ i : ι, (τ i) = existenceTime (Rc i) (liftedLowBound (T i) (B i)) / 4)
    (hKFU : ∀ i : ι, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (hKU : ∀ i : ι, (K i) ⊆ CoefficientBounds.inputDomain (T i))
    (hx : ∀ i : ι, MapsTo Prod.fst (K i) (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius))
    {zRoot : ι → Euclidean 3}
    {ηb : ι → Euclidean (n - 1)}
    {rOuter aOuter : ι → ℝ}
    (hηb : ∀ i : ι, (ηb i) ≠ 0)
    (hrOuter : ∀ i : ι, 0 < (rOuter i))
    (D : ι → CoefficientNormCharts n)
    (hSflow : ∀ i : ι, MapsTo (densityCoordinates (T i)) (D i).field.region
      (outputCylinder ((0 : Euclidean (n - 1)), (z₀ i)) (Rc i) (τ i)))
    (reference : FlatReference n)
    (c₀ : ∀ i : ι, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), (z₀ i)) (Rc i) (B i) (τ i) (row i) (col i) reference.map)
    {Rwork : ℝ} (hRwork : 0 < Rwork) (hworkChart : Rwork < reference.domain.chartRadius)
    (hUwork : U ⊆ ball 0 Rwork)
    {R : ι → ℝ}
    (hR : ∀ i : ι, 0 < (R i))
    {σ : ℝ} (hσ : 0 < σ)
    {Mc : ι → ℝ} (hMc : ∀ i, 0 < Mc i)
    (hforward₀ : ∀ i, cNorm (Icc (-(τ i)) (τ i) ×ˢ
      closedBall ((0 : Euclidean (n - 1)), z₀ i) (Rc i / 8)) 1 (c₀ i).forward ≤ Mc i)
    (hlabels : ∀ i p, p ∈ (D i).field.region → (densityCoordinates (T i) p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 64))
    (htime : ∀ i p, p ∈ (D i).field.region → |(densityCoordinates (T i) p).1| < R i / (64 * Mc i))
    (hDV : ∀ i : ι, (D i).field.region ⊆ ball (0 : Euclidean n) (T i).family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * (P i).radius / 2)))
    (p₀ : ι → InputVariables n) (q₀ : ι → Variables n × Euclidean 2)
    {ρi τi : ι → ℝ} (hρi : ∀ i, 0 < ρi i) (hτi : ∀ i, 0 < τi i)
    {W Bi : ι → Set (InputVariables n)}
    {Q Ωi : ι → Set (Variables n × Euclidean 2)}
    (hW : ∀ i : ι, IsOpen (W i))
    (hKiW : ∀ i : ι, (closedBall (p₀ i) (ρi i)) ⊆ (W i))
    (hBi : ∀ i : ι, IsCompact (Bi i))
    (hWBi : ∀ i : ι, (W i) ⊆ (Bi i))
    (hQ : ∀ i : ι, IsCompact (Q i))
    (hΩi : ∀ i : ι, IsOpen (Ωi i))
    (hQΩi : ∀ i : ι, (Q i) ⊆ (Ωi i))
    {It : ι → Set ℝ}
    (hIt : ∀ i : ι, IsOpen (It i))
    (hIIt : ∀ i : ι, Icc (0 : ℝ) 1 ⊆ (It i))
    (hsegT : ∀ i : ι, ∀ t ∈ (It i), MapsTo (transportSegmentInput n t) (W i) (D i).field.region)
    (hseg : ∀ i : ι, ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) (W i) (D i).field.carrier)
    (A : ι → InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {gap : ι → ℝ}
    (hgap : ∀ i : ι, 0 < (gap i))
    {η : ι → ℝ}
    (hη : ∀ i : ι, 0 < (η i))
    (hfreq : ∀ i : ι, ∀ p ∈ Bi i, (η i) ≤ ‖p.2.2‖)
    (hcontains : ∀ i : ι, ∀ p ∈ (closedBall (p₀ i) (ρi i)), (D i).Contains p)
    (hBiDom : ∀ i : ι, (Bi i) ⊆ symbolInputDomain (zRoot i) (ηb i) (rOuter i) (6 * (aOuter i)))
    {r rAngular : ι → ℝ}
    (hr : ∀ i : ι, 0 < (r i))
    (hcell : ∀ i : ι, 4 * (r i) < 1 / 2)
    (hrAngular : ∀ i : ι, 0 < (rAngular i))
    (hrr : ∀ i : ι, (rAngular i) ≤ (rOuter i))
    (haa : ∀ i : ι, (r i) ≤ (aOuter i))
    (har : ∀ i : ι, (r i) ≤ (rAngular i))
    (hQradius : ∀ i : ι, ∀ p ∈ (Q i), ‖p.1.2.2‖ = 1 / 4)
    (hne : ∀ i : ι, ∀ p ∈ (Ωi i), p.1.2.2 ≠ 0)
    (hscale : ∀ i : ι, ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ (Ωi i) ↔ p ∈ (Ωi i))
    {δgeometry : ι → ℝ}
    (hframe₀ : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
      (projectedStress reference.map - fun _ ↦ cubeStress n) < δgeometry i)
    (hselected : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δgeometry i →
      let QF : {QF : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ QF U ∧
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (QF - fun _ ↦ cubeStress n) < (T i).family.threshold} := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      RetainedFrozen.RetainedSpectralGeometry (T i) QF (zRoot i) (ηb i) (rOuter i) (aOuter i) ∧
      Ωi i ⊆ symbolDomain (T i) QF (zRoot i) (ηb i) (rOuter i) (6 * aOuter i) ∧
      MapsTo (fun q ↦ inverseCoordinates (symbolInverse (T i) QF (zRoot i) (ηb i) (rOuter i) (6 * aOuter i))
        (normalizeOutputRadius (1 / 4) q)) (Ωi i) (closedBall (p₀ i) (ρi i)) ∧
      (∀ p ∈ (closedBall (p₀ i) (ρi i)), ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition (T i) QF)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi i, gap i ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (transportPosition (T i) QF) p) ∧
      (∀ p ∈ conicMaskSupport (zRoot i) (ηb i) (rAngular i) (r i),
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition (T i) QF) p) ∈ Q i) ∧
      closedBall (q₀ i) (2 * τi i) ⊆ symbolDomain (T i) QF (zRoot i) (ηb i) (rOuter i) (6 * aOuter i) ∧
      MapsTo (inverseCoordinates (symbolInverse (T i) QF (zRoot i) (ηb i) (rOuter i) (6 * aOuter i)))
        (closedBall (q₀ i) (2 * τi i)) (closedBall (p₀ i) (ρi i)) ∧
      (closure (augmentedTransportGradient (transportPosition (T i) QF) ''
        conicMaskSupport (zRoot i) (ηb i) (rAngular i) (r i)) ∩ {p | p.1.2.2 ≠ 0} ⊆
          symbolDomain (T i) QF (zRoot i) (ηb i) (rOuter i) (6 * aOuter i)) ∧
      (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition (T i) QF) ''
          conicMaskSupport (zRoot i) (ηb i) (rAngular i) (r i)) → (x, v) ∈ closedBall (q₀ i) (τi i)) ∧
      (∀ p ∈ symbolDomain (T i) QF (zRoot i) (ηb i) (rOuter i) (6 * aOuter i),
        ‖(symbolInverse (T i) QF (zRoot i) (ηb i) (rOuter i) (6 * aOuter i) p).2‖ ≤ 2 * ‖p.1.2.2‖))
    {Rphysical : ι → ℝ} {V : ι → Set CarrierParameter}
    (hV : ∀ i, IsOpen (V i))
    (hVP : ∀ i, V i ⊆ parameter ⁻¹' parameterInterior (3 * (P i).radius / 2))
    (hRT : ∀ i, Rphysical i ≤ (T i).physicalRadius)
    (hRU : ∀ i, ball (0 : Euclidean n) (Rphysical i) ⊆ U)
    (hRtime : ∀ i, Rphysical i ≤ R i / (64 * Mc i))
    (hD : ∀ i, (D i).field.region ⊆ ball (0 : Euclidean n) (Rphysical i) ×ˢ V i)
    (hflow : ∀ i, MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) (Rphysical i) ×ˢ V i)
      (outputCylinder ((0 : Euclidean (n - 1)), z₀ i) (Rc i) (τ i)))
    (hlabelProduct : ∀ i p, p ∈ ball (0 : Euclidean n) (Rphysical i) ×ˢ V i →
      (densityCoordinates (T i) p).2 ∈ closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 64))
    (haR : ∀ i, 6 * aOuter i < (T i).family.radius)
    (houter : ∀ i, coefficientDomain (zRoot i) (rOuter i) (6 * aOuter i) ⊆
      ball (0 : Euclidean n) (Rphysical i) ×ˢ V i)
    (hDouter : ∀ i, (D i).field.region ⊆ coefficientDomain (zRoot i) (rOuter i) (6 * aOuter i))
    (hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (hr i) 1) ×ˢ
      carrierSupport (zRoot i) (r := r i) ⊆ (D i).field.carrier)
    {μ : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2)
    {rInner : ℝ} (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2)
    {rCoeff RCoeff : ℝ} (hrCoeff : 0 < rCoeff) (hrR : rCoeff < RCoeff)
    (hRchart : RCoeff < reference.domain.chartRadius)
    (hcoeffCell : rCoeff < 1 / 2)
    (χcoeff : Euclidean n → ℝ) (hχcoeff : ContDiff ℝ ∞ χcoeff)
    (hsCoeff : tsupport χcoeff ⊆ ball 0 rCoeff)
    (hχrange : ∀ x, χcoeff x ∈ Icc (0 : ℝ) 1)
    (coeff₀ : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hcoeff₀ : ∀ j x, coeff₀ j x = χcoeff (centeredTorusRepresentative x) *
      geometricReducedCoefficients reference.map (centeredTorusRepresentative x) j)
    {g γ Mrow : ℝ} (hg : 0 < g) (hγ : 0 < γ)
    {kMin : ℕ} (horder : displacementLoss n +
      bandExponent * ((canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    let χ := FixedCutoffs.periodic (n := n) hμ hμcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hμ hμcell 2
    let ψ := innerCutoff (n := n) hrInner hInnerCell
    let angular := fun i ↦ angularMask (zRoot i) (NormedSpace.normalize (ηb i)) (hr i)
      (angularWidth_spec (hηb i) (hrAngular i)).1
    let image₀ := imageChannel coeff₀ χ χsrc
    ∃ S : ℝ, 2 ≤ S ∧
    ∃ coeff : (R₀ : ℝ) → S ≤ R₀ → (j : ℕ) →
      (history : Fin j → Torus n → Euclidean (embeddingDimension n)) → (ell : Fin j → ℕ) →
      IsAdmissibleHistory R₀ kMin history ell → ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ R₀ hR₀ j history ell hu,
        (∀ a x, coeff R₀ hR₀ j history ell hu a x = χcoeff (centeredTorusRepresentative x) *
          geometricReducedCoefficients (finiteHistoryMap reference.map history) (centeredTorusRepresentative x) a) ∧
        ∀ a, IsSmoothPeriodic (coeff R₀ hR₀ j history ell hu a)) ∧
    ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), z₀ i) (R i / 4))) →
      (∀ i p, p ∈ ball ((0 : Euclidean (n - 1)), z₀ i) (R i / 4) → 0 < 1 + v i p) →
      (∀ i p, p ∈ closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 8) →
        1 + v i p ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 8))
        (2 * (n + 1) + 14) (v i) ≤ 1) →
    let weighted := fun i p ↦ positiveDensityAmplitude σ (v i p)
    let e₀ := fun i ↦ data (T i) (c₀ i).Q reference.map (row i) (col i) (c₀ i).forward (c₀ i).inverse
      (weighted i) (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
    ∀ U₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i w, U₀ i (carrierInitialTestToLp w) =ᵐ[volume] carrierTestIntegral (e₀ i) w.val) →
    let V₀ := fun i ↦ CommonMeasurement.restrictCarrier χ (U₀ i)
    ‖physicalRow image₀ V₀‖ ≤ Mrow →
    (∀ w : OutputL2 n, (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
      g * ‖w‖ ^ 2 ≤ ‖(physicalRow image₀ V₀).adjoint w‖ ^ 2) →
    (∀ w : OutputL2 n, γ * ‖w‖ ^ 2 ≤ inner ℝ (augmentedNormal image₀ V₀ ψ w) w) →
    ∀ R₀ (hR₀ : S ≤ R₀) (j : ℕ) (history : Fin j → Torus n → Euclidean (embeddingDimension n))
      (ell : Fin j → ℕ) (hu : IsAdmissibleHistory R₀ kMin history ell),
    let F := finiteHistoryMap reference.map history
    ∀ (current : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
        (Rc i) (B i) (τ i) (row i) (col i) F),
      (∀ i, cNorm (Icc (-(τ i)) (τ i) ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀ i) (Rc i / 8))
        1 (current i).forward ≤ Mc i) →
      let e := fun i ↦ data (T i) (current i).Q F (row i) (col i) (current i).forward (current i).inverse
        (weighted i) (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
      ∃ Ucurrent : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i, (∀ w : carrierInitialTestSpace n,
          Ucurrent i (carrierInitialTestToLp w) =ᵐ[volume] carrierTestIntegral (e i) w.val) ∧
          ∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
            (Ucurrent i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
      let image := imageChannel (coeff R₀ hR₀ j history ell hu) χ χsrc
      let Vnew := fun i ↦ CommonMeasurement.restrictCarrier χ (Ucurrent i)
      ‖NormalPerturbation.normal (physicalRow image Vnew) -
        NormalPerturbation.normal (physicalRow image₀ V₀)‖ ≤ min g γ / 2 ∧
      ‖physicalRow image Vnew‖ ≤ Real.sqrt (Mrow ^ 2 + min g γ / 2) ∧
      (∀ w : OutputL2 n, (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
        g / 2 * ‖w‖ ^ 2 ≤ ‖(physicalRow image Vnew).adjoint w‖ ^ 2) ∧
      (∀ w : OutputL2 n, γ / 2 * ‖w‖ ^ 2 ≤ inner ℝ (augmentedNormal image Vnew ψ w) w) ∧
      (∀ w : OutputL2 n, γ / 2 * ‖w‖ ^ 2 ≤ ‖(augmentedRow image Vnew ψ).adjoint w‖ ^ 2) ∧
      (∀ w : OutputL2 n, ∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
        exteriorChannel ψ w x = 0) := by
  classical
  intro χ χsrc ψ angular image₀
  let κ := min g γ
  have hκ : 0 < κ := lt_min hg hγ
  have htol : 0 < κ / 4 := by positivity
  have h8nat : 8 ≤ canonicalCarrierLowOrder n := by unfold canonicalCarrierLowOrder; omega
  have h8 : (8 : ℝ) ≤ canonicalCarrierLowOrder n := by exact_mod_cast h8nat
  have horderImage : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    dsimp only [bandExponent] at horder ⊢
    linarith only [horder, h8]
  have hτRc (i : ι) : τ i ≤ Rc i / 16 := by
    have ht := (existenceTime_le (hRc i) (liftedLowBound_nonneg (T i) (hB i))).1
    rw [hτeq i]
    linarith
  let Rbig := (Rwork + reference.domain.chartRadius) / 2
  have hworkBig : Rwork < Rbig := by dsimp only [Rbig]; linarith
  have hbigChart : Rbig < reference.domain.chartRadius := by dsimp only [Rbig]; linarith
  obtain ⟨δg, hδg, Cg, _, κg, hκg, hgeo⟩ := CurrentGeometricNeighborhood.exists_geometric_neighborhood
    reference hRwork hworkBig hbigChart (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Sg, _hSg, hnear⟩ := HistoryGeometry.exists_initialScale_for_c8_neighborhood
    reference.map Rbig horderImage hδg
  have hUbig : U ⊆ ball 0 Rbig := hUwork.trans (ball_subset_ball hworkBig.le)
  have hsub (i : ι) : closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall 0 Rwork := ((hKFU i).trans hUwork).trans ball_subset_closedBall
  have hnorm (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiff ℝ ∞ F) (i : ι) :
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 4 F ≤
        cNorm (closedBall (0 : Euclidean n) Rwork) 4 F :=
    cNorm_mono_set_of_contDiffAt (hsub i) (isCompact_closedBall _ _)
      (fun _ _ ↦ hF.contDiffAt.of_le (by simp))
  have hG := hgeo univ reference.map isOpen_univ (subset_univ _) reference.contDiff.contDiffOn
    (by simpa only [sub_self, cNorm_zero] using hδg)
  have hiRef : IsImmersionOn reference.map U := fun x hx ↦ hG.1 x (hUbig hx)
  have hrankRef : HasFullNormalRankOn reference.map U := fun x hx ↦ hG.2.1 x (hUbig hx)
  obtain ⟨δ, hδ, hcompare⟩ := exists_finite_realized_retained_density_normal_comparison
    T hdomain hgeometry hP hΩ hK hKΩ hRc hB hτ hτRc hbuffer hτeq hKFU hKU hx hηb hrOuter
    D hSflow c₀ reference.contDiff.contDiffOn hiRef hrankRef
    (M := fun _ ↦ Cg) (κmet := fun _ ↦ 1 / 4) (κnormal := fun _ ↦ κg)
    (fun _ ↦ by norm_num) (fun _ ↦ hκg)
    (fun i ↦ (hnorm _ reference.contDiff i).trans hG.2.2.1)
    (fun i x hx ↦ hG.2.2.2.1 x (hUbig (hKFU i hx)))
    (fun i x hx ↦ hG.2.2.2.2.1 x (hUbig (hKFU i hx)))
    hR hσ hMc hforward₀ hlabels htime hDV p₀ q₀ hρi hτi hW hKiW hBi hWBi hQ hΩi hQΩi
    hIt hIIt hsegT hseg A hgap hη hfreq hcontains hBiDom hr hcell hrAngular hrr haa har
    hQradius hne hscale hframe₀ hselected hV hVP hRT hRU hRtime hD hflow hlabelProduct
    haR houter hDouter hsupportD χ (FixedCutoffs.periodic_norm_le_one hμ hμcell 1) (κ / 4) htol
  obtain ⟨Sc, hSc, hclose⟩ := exists_initialScale_for_retained_normal_comparison_neighborhood
    (N := embeddingDimension n) (fun _ : ι ↦ δ) (fun _ ↦ hδ) horder
  obtain ⟨Si, hSi, himage⟩ := exists_initialScale_for_retained_image_normal_comparison reference
    hrCoeff hrR hRchart hsCoeff hχrange coeff₀ hcoeff₀ χ χsrc htol horderImage
  obtain ⟨δr, hδr, _, _, _, _, hregular⟩ :=
    exists_reference_reduced_coefficient_estimates reference hrCoeff hrR hRchart
  obtain ⟨Sr, _hSr, hrNear⟩ := HistoryGeometry.exists_initialScale_for_c8_neighborhood
    reference.map RCoeff horderImage hδr
  let S := max Sc (max Si (max Sg Sr))
  have hScS : Sc ≤ S := le_max_left _ _
  have hSiS : Si ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hSgS : Sg ≤ S := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hSrS : Sr ≤ S := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hq (R₀ : ℝ) (hR₀ : S ≤ R₀) (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
      (ell : Fin j → ℕ) (hu : IsAdmissibleHistory R₀ kMin u ell) :
      ContDiffOn ℝ ∞ (geometricReducedCoefficients (finiteHistoryMap reference.map u)) (ball 0 RCoeff) :=
    (hregular _ (hu.contDiff_finiteHistoryMap reference.contDiff)
      (hrNear R₀ (hSrS.trans hR₀) j u ell hu)).1
  let coeff := fun R₀ hR₀ j history ell hu ↦ periodicReducedCoefficients hrR hcoeffCell hχcoeff hsCoeff _
    (hq R₀ hR₀ j history ell hu)
  refine ⟨S, hSc.trans hScS, coeff, ?_, ?_⟩
  · intro R₀ hR₀ j history ell hu
    exact ⟨fun _ _ ↦ rfl, isSmoothPeriodic_cutCoefficient hrR hcoeffCell hχcoeff hsCoeff
      (hq R₀ hR₀ j history ell hu)⟩
  intro v hv hvpos hinterval hvm weighted e₀ U₀ htest₀ V₀ hM hlocal hglobal R₀ hR₀
    j history ell hu F current hforward e
  have hF : ContDiff ℝ ∞ F := hu.contDiff_finiteHistoryMap reference.contDiff
  have hFgeo := hgeo univ F isOpen_univ (subset_univ _) hF.contDiffOn
    (hnear R₀ (hSgS.trans hR₀) j history ell hu)
  have hi : IsImmersionOn F U := fun x hx ↦ hFgeo.1 x (hUbig hx)
  have hrank : HasFullNormalRankOn F U := fun x hx ↦ hFgeo.2.1 x (hUbig hx)
  obtain ⟨Uop, htest, hadj, _hsupp, huniq, _hsum, hnormals⟩ :=
    hcompare F current hF.contDiffOn hi hrank
      (fun i ↦ (hnorm F hF i).trans hFgeo.2.2.1)
      (fun i x hx ↦ hFgeo.2.2.2.1 x (hUbig (hKFU i hx)))
      (fun i x hx ↦ hFgeo.2.2.2.2.1 x (hUbig (hKFU i hx))) hforward
      (hclose R₀ (hScS.trans hR₀) reference.map
        (fun i ↦ closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius)
        (fun _ ↦ isCompact_closedBall _ _) j history ell hu)
      v hv hvpos hvm (fun i p hp ↦ (hinterval i p hp).1)
  let Wop := fun (t : Bool) i ↦ if t then Uop true i else U₀ i
  have hWop : Wop = Uop := by
    apply huniq
    intro t i
    cases t with
    | false => exact htest₀ i
    | true => exact htest true i
  have hident : Uop false = U₀ := by
    have hh := congrFun hWop false
    exact hh.symm
  refine ⟨Uop true, fun i ↦ ⟨htest true i, hadj true i⟩, ?_⟩
  intro image Vnew
  have hdiff := (hnormals image image₀ ψ).1
  dsimp only at hdiff
  rw [hident] at hdiff
  have himageDiff := (himage R₀ (hSiS.trans hR₀) j history ell hu
    (coeff R₀ hR₀ j history ell hu) (fun _ _ ↦ rfl)).2.le
  have htotal : ‖NormalPerturbation.normal (physicalRow image Vnew) -
      NormalPerturbation.normal (physicalRow image₀ V₀)‖ ≤ κ / 2 := by
    calc
      _ ≤ ‖NormalPerturbation.normal image - NormalPerturbation.normal image₀‖ + κ / 4 := hdiff
      _ ≤ κ / 4 + κ / 4 := add_le_add himageDiff (le_refl (κ / 4))
      _ = κ / 2 := by ring
  exact ⟨htotal, retained_row_half_gaps_of_physical_normal_error image image₀ Vnew V₀
    hrInner hInnerCell hg hγ hM hlocal hglobal htotal⟩

end JanetCartan.ContinuumNormal.ActualConstruction
