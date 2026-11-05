module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.RealizedHistoryCoercivity
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference

/-!
# History coercivity on the prescribed measured source row

Apply the actual history construction after the prescribed finite row has been
selected. The reference is the same source contraction on the original wide
chart. The prescribed source gap continuation supplies the source operators;
its literal-test uniqueness transfers their bounds to the source operator
already used by the inverse. All coefficient arrays and the history threshold
are chosen before the density and history. No new row or source cap is selected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumInverse
open ContinuumNormal
open ContinuumNormal.ActualConstruction
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

/-- The measured source gap implies coercivity for every admitted history on
that same selected row. The actual producer of the source continuation is
`NormalizedSelection.exists_finite_prescribed_measured_source_gap`, retained by
`exists_finite_prescribed_measured_source_raw_inverse`; its local/global gaps
are `g / 2` and `globalGap g Mlimit / 2`. The conclusion therefore has gaps
`g / 4` and `globalGap g Mlimit / 4`, with the same inner exterior cutoff.

The geometric callback is the indicated projection of the selected `hconic`
clause. The common initializer supplies the original state geometry, compact
cell, product buffers and uniform forward bound. In particular the product
buffers imply the field-region time, label and coefficient-domain premises.
The source operator is arbitrary subject to its literal test action, so the
already constructed inverse's source operator can be used unchanged.

Consumer: the prescribed-row instance of `ContinuumInverse`, then
`PreparedHistory.exists_source_density_finite_preparation_with_small_density`
(`app:ch_background:eq:bg-local-bound`, `app:ch_background:eq:bg-global-bound`,
`main:eq:displacement-budget`, `new:sec:order-of-choices`). -/
theorem exists_prescribed_source_history_coercivity
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
    (hΩpatch : ∀ i, Ω i ⊆ (U ∩ ball (0 : Euclidean n) (T i).physicalRadius) ×ˢ
      parameterInterior (3 * (P i).radius / 2))
    (hx : ∀ i : ι, MapsTo Prod.fst (K i) (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius))
    {zRoot : ι → Euclidean 3}
    {ηb : ι → Euclidean (n - 1)}
    {rOuter aOuter : ι → ℝ}
    (hηb : ∀ i : ι, (ηb i) ≠ 0)
    (hrOuter : ∀ i : ι, 0 < (rOuter i))
    (D : ι → CoefficientNormCharts n)
    (H : FlatReference n) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1)
    (cSource : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
      (Rc i) (B i) (τ i) (row i) (col i) (sourceDilation H.map σ))
    {Rwork : ℝ} (hRwork : 0 < Rwork) (hworkChart : Rwork < H.domain.chartRadius)
    (hUwork : U ⊆ ball 0 Rwork)
    {R : ι → ℝ}
    (hR : ∀ i : ι, 0 < (R i))
    {Mc : ι → ℝ} (hMc : ∀ i, 0 < Mc i)
    (hforward : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n))
      (current : Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
        (Rc i) (B i) (τ i) (row i) (col i) F),
      cNorm (Icc (-(τ i)) (τ i) ×ˢ
        closedBall ((0 : Euclidean (n - 1)), z₀ i) (Rc i / 8)) 1 current.forward ≤ Mc i)
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
    (hframeSource : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
      ((cSource i).Q.1 - fun _ ↦ cubeStress n) < δgeometry i)
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

    (hflow : ∀ i, MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) (Rphysical i) ×ˢ V i)
      (outputCylinder ((0 : Euclidean (n - 1)), z₀ i) (Rc i) (τ i)))
    (hlabelProduct : ∀ i p, p ∈ ball (0 : Euclidean n) (Rphysical i) ×ˢ V i →
      (densityCoordinates (T i) p).2 ∈ closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 64))
    (haR : ∀ i, 6 * aOuter i < (T i).family.radius)
    (houter : ∀ i, coefficientDomain (zRoot i) (rOuter i) (6 * aOuter i) ⊆
      ball (0 : Euclidean n) (Rphysical i) ×ˢ V i)
    (hDregion : ∀ i, (D i).field.region ⊆
      (ball (0 : Euclidean n) (Rphysical i) ×ˢ V i) ∩
        coefficientDomain (zRoot i) (rOuter i) (6 * aOuter i))
    (hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (hr i) 1) ×ˢ
      carrierSupport (zRoot i) (r := r i) ⊆ (D i).field.carrier)
    {μ : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2)
    {rInner : ℝ} (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2)
    (hRchart : 6 * μ < H.domain.chartRadius)
    (hcoeffCell : 6 * μ < 1 / 2)
    (χcoeff : Euclidean n → ℝ) (hχcoeff : ContDiff ℝ ∞ χcoeff)
    (hsCoeff : tsupport χcoeff ⊆ ball 0 (5 * μ))
    (hχrange : ∀ x, χcoeff x ∈ Icc (0 : ℝ) 1)
    (coeff₀ : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hcoeff₀ : ∀ j x, coeff₀ j x = χcoeff (centeredTorusRepresentative x) *
      geometricReducedCoefficients (sourceDilation H.map σ) (centeredTorusRepresentative x) j)
    {g Mlimit : ℝ} (hg : 0 < g)
    (hglobalGap : 0 < NormalAugmentation.globalGap g Mlimit)
    {kMin : ℕ} (horder : displacementLoss n +
      bandExponent * ((canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    let χ := FixedCutoffs.periodic (n := n) hμ hμcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hμ hμcell 2
    let ψ := innerCutoff (n := n) hrInner hInnerCell
    let angular := fun i ↦ angularMask (zRoot i) (NormedSpace.normalize (ηb i)) (hr i)
      (angularWidth_spec (hηb i) (hrAngular i)).1
    let image₀ := imageChannel coeff₀ χ χsrc
    let gs := g / 2
    let γs := NormalAugmentation.globalGap g Mlimit / 2
    let Ms := Real.sqrt (Mlimit ^ 2 + min g (NormalAugmentation.globalGap g Mlimit) / 2)
    (∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), z₀ i) (R i / 4))) →
      (∀ i p, p ∈ ball ((0 : Euclidean (n - 1)), z₀ i) (R i / 4) → 0 < 1 + v i p) →
      (∀ i p, p ∈ closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 8) →
        1 + v i p ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 8))
        (2 * (n + 1) + 14) (v i) ≤ 1) →
      let eSource := fun i ↦ data (T i) (cSource i).Q (sourceDilation H.map σ)
        (row i) (col i) (cSource i).forward (cSource i).inverse
        (fun q ↦ positiveDensityAmplitude σ (v i q)) (hr i) (hcell i) (angular i)
        FixedCutoffs.highFrequency
      ∃ Usource : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ Wsource : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ i f, Wsource i (carrierInitialTestToLp f) =ᵐ[volume]
            carrierTestIntegral (eSource i) f.val) → Wsource = Usource) ∧
        (∀ i,
          (∀ f : carrierInitialTestSpace n,
            Usource i (carrierInitialTestToLp f) =ᵐ[volume]
              carrierTestIntegral (eSource i) f.val) ∧
          ∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (eSource i) w) 2 (carrierMeasure n) ∧
            (Usource i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (eSource i) w) ∧
        let Vsource := fun i ↦ CommonMeasurement.restrictCarrier χ (Usource i)
        ‖physicalRow image₀ Vsource‖ ≤ Ms ∧
        (∀ w : OutputL2 n,
          (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
          gs * ‖w‖ ^ 2 ≤ ‖(physicalRow image₀ Vsource).adjoint w‖ ^ 2) ∧
        (∀ w : OutputL2 n, γs * ‖w‖ ^ 2 ≤
          inner ℝ (augmentedNormal image₀ Vsource ψ w) w) ∧
        (∀ w : OutputL2 n, γs * ‖w‖ ^ 2 ≤
          ‖(augmentedRow image₀ Vsource ψ).adjoint w‖ ^ 2)) →
    ∃ S : ℝ, 2 ≤ S ∧
    ∃ coeff : (R₀ : ℝ) → S ≤ R₀ → (j : ℕ) →
      (history : Fin j → Torus n → Euclidean (embeddingDimension n)) → (ell : Fin j → ℕ) →
      IsAdmissibleHistory R₀ kMin history ell → ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ R₀ hR₀ j history ell hu,
        (∀ a x, coeff R₀ hR₀ j history ell hu a x = χcoeff (centeredTorusRepresentative x) *
          geometricReducedCoefficients (finiteHistoryMap (sourceDilation H.map σ) history) (centeredTorusRepresentative x) a) ∧
        ∀ a, IsSmoothPeriodic (coeff R₀ hR₀ j history ell hu a)) ∧
    ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), z₀ i) (R i / 4))) →
      (∀ i p, p ∈ ball ((0 : Euclidean (n - 1)), z₀ i) (R i / 4) → 0 < 1 + v i p) →
      (∀ i p, p ∈ closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 8) →
        1 + v i p ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 8))
        (2 * (n + 1) + 14) (v i) ≤ 1) →
    let weighted := fun i p ↦ positiveDensityAmplitude σ (v i p)
    let e₀ := fun i ↦ data (T i) (cSource i).Q (sourceDilation H.map σ) (row i) (col i) (cSource i).forward (cSource i).inverse
      (weighted i) (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
    ∀ U₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i w, U₀ i (carrierInitialTestToLp w) =ᵐ[volume] carrierTestIntegral (e₀ i) w.val) →
    let V₀ := fun i ↦ CommonMeasurement.restrictCarrier χ (U₀ i)
    ∀ R₀ (hR₀ : S ≤ R₀) (j : ℕ) (history : Fin j → Torus n → Euclidean (embeddingDimension n))
      (ell : Fin j → ℕ) (hu : IsAdmissibleHistory R₀ kMin history ell),
    let F := finiteHistoryMap (sourceDilation H.map σ) history
    ∀ (current : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
        (Rc i) (B i) (τ i) (row i) (col i) F),
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
        NormalPerturbation.normal (physicalRow image₀ V₀)‖ ≤ min gs γs / 2 ∧
      ‖physicalRow image Vnew‖ ≤ Real.sqrt (Ms ^ 2 + min gs γs / 2) ∧
      (∀ w : OutputL2 n, (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
        gs / 2 * ‖w‖ ^ 2 ≤ ‖(physicalRow image Vnew).adjoint w‖ ^ 2) ∧
      (∀ w : OutputL2 n, γs / 2 * ‖w‖ ^ 2 ≤ inner ℝ (augmentedNormal image Vnew ψ w) w) ∧
      (∀ w : OutputL2 n, γs / 2 * ‖w‖ ^ 2 ≤ ‖(augmentedRow image Vnew ψ).adjoint w‖ ^ 2) ∧
      (∀ w : OutputL2 n, ∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
        exteriorChannel ψ w x = 0) := by
  classical
  intro χ χsrc ψ angular image₀ gs γs Ms hsource
  let reference := sourceDilationReference H hσ hσone
  have hKU (i : ι) : K i ⊆ CoefficientBounds.inputDomain (T i) := by
    intro p hp
    obtain ⟨hx, hz⟩ := hΩpatch i (hKΩ i hp)
    exact ⟨hx, fun j ↦ (hz j).trans_le (by linarith only [(hP i).1])⟩
  have hD (i : ι) : (D i).field.region ⊆
      ball (0 : Euclidean n) (Rphysical i) ×ˢ V i :=
    (hDregion i).trans inter_subset_left
  have hDouter (i : ι) : (D i).field.region ⊆
      coefficientDomain (zRoot i) (rOuter i) (6 * aOuter i) :=
    (hDregion i).trans inter_subset_right
  have hcyl (i : ι) := (hflow i).mono_left (hD i)
  have hlabels (i : ι) (p) (hp : p ∈ (D i).field.region) :=
    hlabelProduct i p (hD i hp)
  have htime (i : ι) (p : Euclidean n × CarrierParameter)
      (hp : p ∈ (D i).field.region) :
      |(densityCoordinates (T i) p).1| < R i / (64 * Mc i) := by
    have ht := abs_real_inner_le_norm (T i).data.adapted.normal p.1
    rw [(T i).data.adapted.normal_unit, one_mul] at ht
    change |(adaptedCoordinates (T i).data.adapted p.1).1| < R i / (64 * Mc i)
    rw [adaptedCoordinates_apply]
    exact (ht.trans_lt (mem_ball_zero_iff.mp (hD i hp).1)).trans_le (hRtime i)
  have hDV (i : ι) : (D i).field.region ⊆
      ball (0 : Euclidean n) (T i).family.radius ×ˢ
        (parameter ⁻¹' parameterInterior (3 * (P i).radius / 2)) := by
    intro p hp
    exact ⟨ball_subset_ball (haR i).le (hDouter i hp).1, hVP i (hD i hp).2⟩
  have hframe (i : ι) :
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (projectedStress reference.map - fun _ ↦ cubeStress n) < δgeometry i := by
    simpa only [reference, sourceDilationReference_map, (cSource i).frame_eq] using
      hframeSource i
  obtain ⟨S, hS, coeffHistory, hcoeffHistory, hhistory⟩ :=
    exists_initialScale_for_realized_retained_history_coercivity T hdomain hgeometry hP
      hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx
      hηb hrOuter D hcyl reference cSource hRwork hworkChart hUwork hR hσ hMc
      (fun i ↦ hforward i reference.map (cSource i)) hlabels htime hDV
      p₀ q₀ hρi hτi hW hKiW hBi hWBi hQ hΩi hQΩi hIt hIIt hsegT hseg
      A hgap hη hfreq hcontains hBiDom hr hcell hrAngular hrr haa har
      hQradius hne hscale hframe hselected
      hV hVP hRT hRU hRtime hD hflow hlabelProduct haR houter hDouter hsupportD
      hμ hμcell hrInner hInnerCell (rCoeff := 5 * μ) (RCoeff := 6 * μ)
      (by positivity) (by linarith only [hμ]) hRchart
      (by linarith only [hcoeffCell, hμ]) χcoeff hχcoeff hsCoeff hχrange coeff₀ hcoeff₀
      (half_pos hg) (half_pos hglobalGap) (Mrow := Ms) horder
  refine ⟨S, hS, coeffHistory, hcoeffHistory, ?_⟩
  intro v hv hpos hinterval hvnorm weighted e₀ U₀ htests V₀
  obtain ⟨Usource, hunique, _hraw, hrow, hlocal, hglobal, _hadjoint⟩ :=
    hsource v hv hpos hinterval hvnorm
  have heq : U₀ = Usource := hunique U₀ htests
  subst Usource
  intro R₀ hR₀ j history ell hu F current e
  exact hhistory v hv hpos hinterval hvnorm U₀ htests hrow hlocal hglobal
    R₀ hR₀ j history ell hu current (fun i ↦ hforward i F (current i))

end JanetCartan.ContinuumInverse
