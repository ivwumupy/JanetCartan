module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.RealizedSelectedVariation

/-!
# Finite comparison of constructed retained density carriers

Construct every current and reference carrier on the supplied retained charts,
then sum their literal reflected-normal differences under the common measurement.
The finite tolerance precedes the density and varying map. The exterior term
is unchanged in the augmented comparison.
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
open ProjectedStressFrame WideDensity

variable {n N : ℕ} {ι : Type} [Fintype ι]
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

/-- Apply the realized single-cell comparison on one finite selected family.
The constructed operators retain the literal test actions, adjoints, support
and uniqueness. The physical and augmented normal differences are bounded by
the actual image-normal difference plus the requested tolerance. No bounded
carrier or forward/adjoint-output record is an input. The original scalar
class and masks are retained, and reflection is counted once. Consumer:
retained-history coercivity (`app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-local-bound`, `app:ch_background:eq:bg-global-bound`). -/
theorem exists_finite_realized_retained_density_normal_comparison
    {c₁ C : ι → ℝ}
    (hP : ∀ i : ι, (P i).IsValid (c₁ i) (C i))
    (hΩ : ∀ i : ι, IsOpen (Ω i))
    (hK : ∀ i : ι, IsCompact (K i))
    (hKΩ : ∀ i : ι, (K i) ⊆ (Ω i))
    (hRc : ∀ i : ι, 0 < (Rc i))
    (hB : ∀ i : ι, 0 ≤ (B i))
    (hτ : ∀ i : ι, 0 < (τ i))
    (hτRc : ∀ i : ι, τ i ≤ Rc i / 16)
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
    {F₀ : Euclidean n → Euclidean N}
    (c₀ : ∀ i : ι, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), (z₀ i)) (Rc i) (B i) (τ i) (row i) (col i) F₀)
    (hF₀ : ContDiffOn ℝ ∞ F₀ U)
    (hi₀ : IsImmersionOn F₀ U)
    (hrank₀ : HasFullNormalRankOn F₀ U)
    {M κmet κnormal : ι → ℝ}
    (hκmet : ∀ i : ι, 0 < (κmet i))
    (hκnormal : ∀ i : ι, 0 < (κnormal i))
    (hlow₀ : ∀ i : ι, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 4 F₀ ≤ (M i))
    (hmet₀ : ∀ i : ι, ∀ x ∈ closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius,
      ∀ v, (κmet i) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ i : ι, ∀ x ∈ closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius,
      ∀ w ∈ normalSpace F₀ x,
      (κnormal i) * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
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
      (projectedStress F₀ - fun _ ↦ cubeStress n) < δgeometry i)
    (hselected : ∀ i (F : Euclidean n → Euclidean N)
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
    (χ : C(Torus n, ℝ)) (hχ : ‖χ‖ ≤ 1) :
    ∀ tol > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N)
      (current : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
        (Rc i) (B i) (τ i) (row i) (col i) F),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      (∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 4 F ≤ M i) →
      (∀ i x, x ∈ closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius →
        ∀ v, κmet i * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ i x, x ∈ closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius →
        ∀ w ∈ normalSpace F x, κnormal i * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      (∀ i, cNorm (Icc (-(τ i)) (τ i) ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀ i) (Rc i / 8))
        1 (current i).forward ≤ Mc i) →
      (∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius)
        (max 8 (max 1 (2 * (n + 1)) + 6)) (F - F₀) < δ) →
      ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), z₀ i) (R i / 4))) →
      (∀ i p, p ∈ ball ((0 : Euclidean (n - 1)), z₀ i) (R i / 4) → 0 < 1 + v i p) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 8)) (2 * (n + 1) + 14) (v i) ≤ 1) →
      (∀ i p, p ∈ closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 8) → (1 / 2 : ℝ) ≤ 1 + v i p) →
      let f := fun t : Bool ↦ if t then F else F₀
      let cp : ∀ t i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
          (Rc i) (B i) (τ i) (row i) (col i) (f t) :=
        fun t i ↦ Bool.rec (c₀ i) (current i) t
      let angular := fun i ↦ angularMask (zRoot i) (NormedSpace.normalize (ηb i)) (hr i)
        (angularWidth_spec (hηb i) (hrAngular i)).1
      let e := fun t i ↦ data (T i) (cp t i).Q (f t) (row i) (col i)
        (cp t i).forward (cp t i).inverse (fun p ↦ positiveDensityAmplitude σ (v i p))
        (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
      ∃ Uop : Bool → ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ t i w, Uop t i (carrierInitialTestToLp w) =ᵐ[volume] carrierTestIntegral (e t i) w.val) ∧
        (∀ t i (w : ComplexOutputL2 n), MemLp (carrierAdjointIntegral (e t i) w) 2 (carrierMeasure n) ∧
          (Uop t i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e t i) w) ∧
        (∀ t i w, ∀ᵐ x ∂volume, x ∉ (e t i).outputChart → Uop t i w x = 0) ∧
        (∀ Wop : Bool → ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ t i w, Wop t i (carrierInitialTestToLp w) =ᵐ[volume] carrierTestIntegral (e t i) w.val) →
          Wop = Uop) ∧
        let Vop := fun t i ↦ CommonMeasurement.restrictCarrier χ (Uop t i)
        (∑ i, ‖carrierChannel (Vop true i) ∘L (carrierChannel (Vop true i)).adjoint -
          carrierChannel (Vop false i) ∘L (carrierChannel (Vop false i)).adjoint‖) ≤ tol ∧
        ∀ (image image₀ : OutputL2 n →L[ℝ] OutputL2 n) (ψ : C(Torus n, ℝ)),
          ‖NormalPerturbation.normal (physicalRow image (Vop true)) -
            NormalPerturbation.normal (physicalRow image₀ (Vop false))‖ ≤
              ‖NormalPerturbation.normal image - NormalPerturbation.normal image₀‖ + tol ∧
          ‖augmentedNormal image (Vop true) ψ - augmentedNormal image₀ (Vop false) ψ‖ ≤
            ‖NormalPerturbation.normal image - NormalPerturbation.normal image₀‖ + tol := by
  classical
  intro tol htol
  let ε := tol / ((Fintype.card ι : ℝ) + 1)
  have hε : 0 < ε := div_pos htol (by positivity)
  let factor (i : ι) := (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * r i) * 4)
  have hfactor (i : ι) : 0 ≤ factor i :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (fixedBoxAmplitudeConstant_nonneg _ _) (by norm_num))
  let εlocal (i : ι) := ε / (factor i + 1)
  have hεlocal (i : ι) : 0 < εlocal i := div_pos hε (by linarith [hfactor i])
  have hlocal (i : ι) := exists_realized_retained_density_normal_comparison
    (T i) (hdomain i) (hgeometry i) (hP i) (hΩ i) (hK i) (hKΩ i) (hRc i) (hB i) (hτ i) (hτRc i)
    (hbuffer i) (hτeq i) (hKFU i) (hKU i) (hx i) (hηb i) (hrOuter i)
    (D i) (hSflow i) (c₀ i) hF₀ hi₀ hrank₀ (hκmet i) (hκnormal i)
    (hlow₀ i) (hmet₀ i) (hnormal₀ i) (hR i) hσ
    (hMc i) (hforward₀ i) (hlabels i) (htime i) (hDV i)
    (p₀ i) (q₀ i) (hρi i) (hτi i) (hW i) (hKiW i) (hBi i) (hWBi i) (hQ i) (hΩi i) (hQΩi i)
    (hIt i) (hIIt i) (hsegT i) (hseg i) (A i) (hgap i) (hη i) (hfreq i)
    (hcontains i) (hBiDom i) (hr i) (hcell i) (hrAngular i) (hrr i) (haa i) (har i)
    (hQradius i) (hne i) (hscale i) (hframe₀ i) (hselected i)
    (hV i) (hVP i) (hRT i) (hRU i) (hRtime i) (hD i) (hflow i) (hlabelProduct i)
    (haR i) (houter i) (hDouter i) (hsupportD i) (εlocal i) (hεlocal i)
  choose δ hδ hcompare using hlocal
  obtain ⟨δ₀, hδ₀, hδ₀δ⟩ := Pi.exists_forall_pos_add_lt hδ
  refine ⟨δ₀, hδ₀, ?_⟩
  intro F current hF him hrank hlow hmet hnormal hforward hsmall v hv hvpos hvm hpos
    f cp angular e
  have hrealize (i : ι) := hcompare i F (current i) hF him hrank (hlow i) (hmet i)
    (hnormal i) (hforward i) ((hsmall i).trans (by simpa only [zero_add] using hδ₀δ i))
    (v i) (hv i) (hvpos i) (hvm i) (hpos i)
  choose Uop htest hadj hsupp huniq hnormaldiff using hrealize
  let Urow := fun t i ↦ Uop i t
  refine ⟨Urow, (fun t i ↦ htest i t), (fun t i ↦ hadj i t), (fun t i ↦ hsupp i t), ?_, ?_⟩
  · intro Wop hWop
    have heq (i : ι) := huniq i (fun t ↦ Wop t i) (fun t ↦ hWop t i)
    funext t i
    exact congrFun (heq i) t
  · intro Vop
    have hchannel (i : ι) :
        ‖carrierChannel (Vop true i) ∘L (carrierChannel (Vop true i)).adjoint -
          carrierChannel (Vop false i) ∘L (carrierChannel (Vop false i)).adjoint‖ ≤ ε := by
      apply (hnormaldiff i χ hχ).trans
      have hcancel : (factor i + 1) * εlocal i = ε := mul_div_cancel₀ ε (by linarith [hfactor i])
      calc
        _ = factor i * εlocal i := by dsimp only [factor]; ring
        _ ≤ ε := by nlinarith [hεlocal i]
    have hcost : (Fintype.card ι : ℝ) * ε ≤ tol := by
      have he : ((Fintype.card ι : ℝ) + 1) * ε = tol := mul_div_cancel₀ tol (by positivity)
      nlinarith [hε.le]
    have hsum : (∑ i, ‖carrierChannel (Vop true i) ∘L (carrierChannel (Vop true i)).adjoint -
        carrierChannel (Vop false i) ∘L (carrierChannel (Vop false i)).adjoint‖) ≤ tol :=
      (Finset.sum_le_sum (fun i _ ↦ hchannel i)).trans
        (by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hcost)
    refine ⟨hsum, ?_⟩
    intro image image₀ ψ
    have hbound : ‖(NormalPerturbation.normal image - NormalPerturbation.normal image₀) +
        ∑ i, (carrierChannel (Vop true i) ∘L (carrierChannel (Vop true i)).adjoint -
          carrierChannel (Vop false i) ∘L (carrierChannel (Vop false i)).adjoint)‖ ≤
        ‖NormalPerturbation.normal image - NormalPerturbation.normal image₀‖ + tol :=
      (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans hsum))
    constructor
    · have heq : NormalPerturbation.normal (physicalRow image (Vop true)) -
          NormalPerturbation.normal (physicalRow image₀ (Vop false)) =
          (NormalPerturbation.normal image - NormalPerturbation.normal image₀) +
            ∑ i, (carrierChannel (Vop true i) ∘L (carrierChannel (Vop true i)).adjoint -
              carrierChannel (Vop false i) ∘L (carrierChannel (Vop false i)).adjoint) := by
        simp only [NormalPerturbation.normal, physicalRow_normal, Finset.sum_sub_distrib]
        abel
      rw [heq]
      exact hbound
    · have heq : augmentedNormal image (Vop true) ψ - augmentedNormal image₀ (Vop false) ψ =
          (NormalPerturbation.normal image - NormalPerturbation.normal image₀) +
            ∑ i, (carrierChannel (Vop true i) ∘L (carrierChannel (Vop true i)).adjoint -
              carrierChannel (Vop false i) ∘L (carrierChannel (Vop false i)).adjoint) := by
        rw [augmentedNormal_eq_sum, augmentedNormal_eq_sum]
        simp only [Finset.sum_sub_distrib, NormalPerturbation.normal]
        abel
      rw [heq]
      exact hbound

end JanetCartan.ContinuumNormal.ActualConstruction
