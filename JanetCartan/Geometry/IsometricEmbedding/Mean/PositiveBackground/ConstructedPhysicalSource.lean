module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedPhysicalSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.NormalizedMeanMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.SourceFamily

/-!
# The physical source on constructed retained source charts

Construct the current charts from the original finite seed family and apply
the retained mean-source theorem on the entire original external-weight
support. One physical buffer precedes every smaller measurement radius. The
current charts retain their actual ODE lifts and prescribed source scalars.

Scalar uniqueness identifies the affine physical mean for every density with
the normalized carrier data used by the prescribed-mask adjoint. The original
detector-support plateau also identifies the kernel and both literal integrals.
In particular,
the source and buffered residual are the same L² elements. The uncorrected raw
correction and factor-four density therefore remain literally the same for
each supplied row and exterior. Their bounds require
no current-chart existence premise and no inverse estimate. The finite seed
selection and the uniform operator gap and inverse estimates remain separate
construction obligations.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PositiveBackground
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormal.FrozenModel
open PositiveReference PositiveReference.FlowConstruction ContinuumRow CanonicalCarrier LeadingPrimitive
open NormalizedBackground NormalizedBackground.SourceGeometry HamiltonPhase
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
open ProjectedStressFrame UniformStep.Periodization RetainedAssembly.ExternalWeights
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- Construct the SAME retained source charts and their literal fixed-source
bounds, then identify their full physical affine mean with the normalized data
for every density. The original external weights, including their full collars,
remain in one flow buffer chosen before the measurement radius and source scale.
The returned scale cap, positive normal-field lower bound, smooth normalized
field extension through zero and all-order Sobolev/jet constants precede the
varying scale. The two L² identities retain the source
factor `-1/2` and the measurement buffer used by `uncorrectedDensity`.

The chart-existence input of `exists_retained_weight_physical_source_bounds`
is discharged using `NormalizedChartFamily.exists_finite_source_charts_with_lifts`.
The remaining inputs are the original finite seed/weight selection, coefficient
contraction and retained comparison geometry. Consumers are `SourceInverse`
and the prescribed-mask normalized adjoint, followed by `PreparedHistory` and
`Current` (`app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-affine-mean`, `app:ch_background:eq:bg-current-raising`). -/
theorem exists_constructed_retained_physical_source
    {n : ℕ} (hn : 5 ≤ n) {A : Type} [Fintype A] (G : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U} (h0U : (0 : Euclidean n) ∈ U)
    (hUG : U ⊆ G.domain.chart n) (hbounded : Bornology.IsBounded U)
    {P : A → Patch n} {cP CP : ℝ} (hP : ∀ a, (P a).IsValid cP CP)
    (T : (a : A) → PatchQuantitativeFamily (P a) U hU)
    {Ω : A → Set (Euclidean n × Euclidean 3)} (hΩ : ∀ a, IsOpen (Ω a))
    {z₀ : A → Euclidean 3} {ρ Rc M τ L rcomp δcomp σcover τfull δgeometry : A → ℝ}
    {row col : A → Fin n}
    (hKΩ : ∀ a, closedBall ((0 : Euclidean n), z₀ a) (ρ a) ⊆ Ω a)
    (hpatch : ∀ a, Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius))
    (hΩU : ∀ a w, w ∈ Ω a → w.1 ∈ U)
    (hΩscale : ∀ a σ, σ ∈ Ioc (0 : ℝ) 1 →
      MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) (Ω a) (Ω a))
    (hL : ∀ a, 0 < L a) (hRc : ∀ a, 0 < Rc a) (hM : ∀ a, 0 ≤ M a)
    (hτeq : ∀ a, τ a = existenceTime (Rc a) (liftedLowBound (T a) (M a)) / 4)
    (hδgeometry : ∀ a, 0 < δgeometry a)
    (hbuffer : ∀ a, MapsTo (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀ a)) (Rc a))
      (closedBall ((0 : Euclidean n), z₀ a) (ρ a)))
    (hphysical : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ U)
    (seed : (a : A) → Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
      ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a) G.map)
    (htrans : ∀ a, ∀ q ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU (seed a).Q.1 (seed a).Q.2.1).hp q,
        (T a).data.adapted.normal⟫_ℝ ≠ 0)
    (hσcover : ∀ a, 0 < σcover a)
    (hcompRadius : ∀ a, 8 * rcomp a ≤ Rc a / 32)
    (E : A → Set (Euclidean n × CarrierParameter)) (hE : ∀ a, IsOpen (E a))
    (hcomp : ∀ a, MapsTo (densityCoordinates (T a)) (E a)
      (Ioo (-δcomp a) (δcomp a) ×ˢ
        ball ((0 : Euclidean (n - 1)), z₀ a) (rcomp a)))
    (hgraph : ∀ a, MapsTo (carrierGraph (T a)) (E a)
      (ball ((0 : Euclidean n), (z₀ a, (T a).reference.spatialPatch (z₀ a))) (σcover a)))
    (hworking : ∀ a,
      closedBall ((0 : Euclidean n), (z₀ a, (T a).reference.spatialPatch (z₀ a)))
        (2 * σcover a) ⊆
      (coordinates (adaptedCoordinates (T a).data.adapted)).symm ''
        (Icc (-τfull a / 2) (τfull a / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)),
            (z₀ a, (T a).reference.spatialPatch (z₀ a))) (L a / 64)))
    (χ : A → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχcompact : ∀ a, HasCompactSupport (χ a))
    (hχE : ∀ a, tsupport (χ a) ⊆ carrierNeighborhood (E a))
    {physicalCap : ℝ} (hphysicalCap : 0 < physicalCap) :
    ∃ radiusCap > (0 : ℝ), 4 * radiusCap < 1 / 2 ∧
      12 * radiusCap < physicalCap ∧ 12 * radiusCap < 1 / 2 ∧
      closedBall (0 : Euclidean n) (12 * radiusCap) ⊆ U ∧
    ∃ V : A → Set CarrierParameter,
      (∀ a, IsOpen (V a)) ∧ (∀ a, tsupport (χ a) ⊆ V a) ∧
      (∀ a, closedBall (0 : Euclidean n) (12 * radiusCap) ×ˢ V a ⊆ E a) ∧
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧
    ∃ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (a : A) →
      Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
        ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a)
        (sourceDilation G.map σ),
      (∀ σ hσ a,
        ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
            ℝ × (Euclidean (n - 1) × Euclidean 3),
          ODE.IsSmoothFlowOn (liftedDirection (T a) (current σ hσ a).Q (row a) (col a))
            (0, ((0 : Euclidean (n - 1)), z₀ a)) (Rc a) (Rc a / 2)
            (existenceTime (Rc a) (liftedLowBound (T a) (M a))) Ψ ∧
          (current σ hσ a).forward = forwardFromLift Ψ ∧
          (current σ hσ a).inverse = footpointFromLift Ψ ∧
          cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
            ((current σ hσ a).Q.1 - fun _ ↦ cubeStress n) < δgeometry a ∧
          EqOn ((current σ hσ a).scalar (fun _ ↦ σ))
            (sourceAmplitude ((seed a).scalar (fun _ ↦ 1)) σ)
            ((coordinates (adaptedCoordinates (T a).data.adapted)) ⁻¹' (current σ hσ a).D) ∧
          ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
            EqOn ((current σ hσ a).scalar (fun q ↦ σ * weight q))
              (fun w ↦ sourceAmplitude ((seed a).scalar (fun _ ↦ 1)) σ w *
                weight ((current σ hσ a).inverse
                  (coordinates (adaptedCoordinates (T a).data.adapted) w)))
              ((coordinates (adaptedCoordinates (T a).data.adapted)) ⁻¹' (current σ hσ a).D)) ∧
    ∀ (r : ℝ) (hr : 0 < r), r ≤ radiusCap →
    ∀ (angular : A → CarrierParameter → Euclidean (n - 1) → ℝ) (high : A → ℝ → ℝ),
    ∃ hcell : 4 * r < 1 / 2,
    let d : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → A → CarrierData n (embeddingDimension n) :=
      fun σ hσ a ↦ data (T a) (current σ hσ a).Q (sourceDilation G.map σ)
      (row a) (col a) (current σ hσ a).forward (current σ hσ a).inverse (fun _ ↦ σ)
      hr hcell (angular a) (high a)
    let e : ℝ → A → CarrierData n (embeddingDimension n) :=
      fun σ a ↦ normalizedCarrierData (T a) (seed a).Q G.map
      (row a) (col a) (seed a).forward (seed a).inverse (fun _ ↦ 1)
      hr hcell (angular a) (high a) σ
    let H₀ : MetricTensor n := carrierMean (fun _ ↦ volume.prod volume) (fun a z ↦ χ a z ^ 2)
      (fun a ↦ (seed a).normal (fun _ ↦ 1)) (fun a ↦ covector (seed a)) 0
    let H : ℝ → MetricField n := fun σ ↦ physicalDensityMean (e σ) χ 0
    let Q : ℝ → Euclidean n → Fin n → MetricTensor n :=
      fun σ ↦ projectedStress (sourceDilation G.map σ)
    let R : ℝ → MetricField n := fun σ ↦ referenceMeanResidual (sourceDilation G.map σ) H₀ (H σ)
    let J := fun a q ↦ (normalizedPullback (unitAmplitude (seed a)) q,
      normalizedPullback (covector (seed a)) q,
      normalizedPullback ((seed a).normal (fun _ ↦ 1)) q)
    H₀.PosSemidef ∧
      (∀ σ hσ v, EqOn (physicalDensityMean (d σ hσ) χ v)
        (physicalDensityMean (e σ) χ v) (ball 0 (5 * r))) ∧
      ((∀ a z η, angular a z η ≠ 0 → χ a z = 1) → ∀ σ hσ a,
        carrierKernel (d σ hσ a) = carrierKernel (e σ a) ∧
        carrierTestIntegral (d σ hσ a) = carrierTestIntegral (e σ a) ∧
        carrierAdjointIntegral (d σ hσ a) = carrierAdjointIntegral (e σ a)) ∧
    ∃ hQ : ∀ σ ∈ Ioc (0 : ℝ) cap, ContDiffOn ℝ ∞ (Q σ) (ball 0 (4 * r)),
    ∃ hR : ∀ σ ∈ Ioc (0 : ℝ) cap, ContDiffOn ℝ ∞ (R σ) (ball 0 (4 * r)),
    ∃ hRphysical : ∀ σ hσ, ContDiffOn ℝ ∞
        (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
        (ball 0 (4 * r)),
      (∀ σ hσ,
        fixedSourceToL2 hr hcell (Q σ)
            (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
            (hQ σ hσ) (hRphysical σ hσ) =
          fixedSourceToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ) ∧
        fixedResidualToL2 hr hcell (Q σ)
            (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
            (hQ σ hσ) (hRphysical σ hσ) =
          fixedResidualToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ) ∧
        ∀ (image : OutputL2 n →L[ℝ] OutputL2 n)
          (B : A → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)),
          let residualPhysical := fixedResidualToL2 hr hcell (Q σ)
            (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
            (hQ σ hσ) (hRphysical σ hσ)
          let residualNormalized := fixedResidualToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ)
          uncorrectedRawCorrection image B ψ (FixedCutoffs.periodic hr hcell 0) residualPhysical =
            uncorrectedRawCorrection image B ψ (FixedCutoffs.periodic hr hcell 0) residualNormalized ∧
          uncorrectedDensity (d σ hσ) image B ψ (FixedCutoffs.periodic hr hcell 0) residualPhysical =
            uncorrectedDensity (e σ) image B ψ (FixedCutoffs.periodic hr hcell 0) residualNormalized) ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ cap ∧ ∃ cNormal > (0 : ℝ),
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      (∀ a, ContDiffOn ℝ ∞ (J a)
        (Ioo (-2 * σ₀) (2 * σ₀) ×ˢ ball 0 (4 * r) ×ˢ V a)) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ → ∀ s,
        (periodicSobolevScale n (Euclidean n)).gradeNorm s
          (fixedSourceToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ)) ≤ C s * σ ∧
        cNorm (closedBall 0 (4 * r)) s (fun x ↦ H σ x - H₀) ≤ C s * σ ∧
        ∀ a x, x ∈ closedBall 0 (4 * r) → ∀ z ∈ tsupport (χ a),
          ‖iteratedFDeriv ℝ s (J a) (σ, (x, z))‖ ≤ C s) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ → ∀ a x,
        x ∈ closedBall 0 (4 * r) → ∀ z ∈ tsupport (χ a),
          cNormal ≤ ‖(current σ hσ a).normal (fun _ ↦ σ) (x, z)‖ ∧
          cNormal ≤ ‖(e σ a).normalField x z‖) ∧
      (∀ a x z, z ∈ tsupport (χ a) → cNormal ≤ ‖(e 0 a).normalField x z‖) ∧
      (∀ σ ∈ Ioc (0 : ℝ) cap, EqOn (R σ) (fun x ↦ H σ x - H₀) (ball 0 (5 * r))) := by
  classical
  have hτ (a : A) : 0 < τ a := by
    rw [hτeq a]
    exact div_pos (existenceTime_pos (hRc a) (liftedLowBound_nonneg (T a) (hM a))) (by norm_num)
  have hτR (a : A) : τ a ≤ Rc a / 16 := by
    have hh := (existenceTime_le (hRc a) (liftedLowBound_nonneg (T a) (hM a))).1
    rw [hτeq a]
    linarith
  have hpatch' (a : A) : Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterCube (2 * (P a).radius) :=
    fun p hp ↦ ⟨(hpatch a hp).1, fun j ↦ ((hpatch a hp).2 j).le⟩
  obtain ⟨physicalRadius, hphysicalRadius, hphysicalRadii⟩ :=
    Pi.exists_forall_pos_add_lt (fun a ↦ (T a).physicalRadius_pos)
  obtain ⟨radiusCap, hradiusCap, hcapcell, hrCap, hrhalf, hrU, V, hV, hχV, hproduct, hflow⟩ :=
    exists_retained_weight_flow_buffer h0U T z₀ seed hL hRc hτ hσcover
      hcompRadius E hE hcomp hgraph hworking χ hχcompact hχE
      (lt_min hphysicalCap hphysicalRadius)
  obtain ⟨cap, hcap, hcap1, current, hcurrent⟩ :=
    NormalizedChartFamily.exists_finite_source_charts_with_lifts G hUG hbounded T Ω hΩ
      z₀ ρ Rc M τ δgeometry row col hRc hM hδgeometry hτeq hKΩ hpatch'
      hΩU hΩscale hphysical hbuffer seed htrans
  refine ⟨radiusCap, hradiusCap, hcapcell, hrCap.trans_le (min_le_left _ _), hrhalf,
    hrU, V, hV, hχV, hproduct, cap, hcap, hcap1, current, ?_, ?_⟩
  · intro σ hσ a
    obtain ⟨Ψ, hΨ, hf, hy, _, _, hsmall, _, _, hscalar, _, hweight⟩ := hcurrent σ hσ a
    exact ⟨Ψ, hΨ, hf, hy, hsmall, hscalar, hweight⟩
  intro r hr hrr angular high
  have hcell : 4 * r < 1 / 2 := by linarith
  refine ⟨hcell, ?_⟩
  intro d e H₀ H Q R J
  let Hphysical : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → MetricField n :=
    fun σ hσ ↦ carrierMean (fun _ ↦ volume.prod volume) (fun a z ↦ χ a z ^ 2)
    (fun a ↦ (current σ hσ a).normal (fun _ ↦ σ)) (fun a ↦ covector (current σ hσ a))
  let Rphysical : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → MetricField n :=
    fun σ hσ ↦ referenceMeanResidual (sourceDilation G.map σ) H₀ (Hphysical σ hσ)
  let W := fun a ↦ ball (0 : Euclidean n) (12 * radiusCap) ×ˢ V a
  have h6U : closedBall (0 : Euclidean n) (6 * r) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hrU
  have h6W (a : A) : closedBall (0 : Euclidean n) (6 * r) ×ˢ V a ⊆ W a :=
    prod_mono (closedBall_subset_ball (by linarith)) Subset.rfl
  have hseed (a : A) : MapsTo (densityCoordinates (T a)) (W a) (seed a).D :=
    (hflow a).2.2.2 G.map (seed a)
  have hcurrentDomain (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (a : A) :
      MapsTo (densityCoordinates (T a)) (W a) (current σ hσ a).D :=
    (hflow a).2.2.2 (sourceDilation G.map σ) (current σ hσ a)
  have hχpatch (a : A) (z) (hz : z ∈ tsupport (χ a)) :
      parameter z ∈ parameterInterior (2 * (P a).radius) := by
    have hh := (seed a).domain_coefficients (hseed a
      (show ((0 : Euclidean n), z) ∈ W a from ⟨mem_ball_self (by positivity), hχV a hz⟩))
    change (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (coordinates (adaptedCoordinates (T a).data.adapted) (0, parameter z)) ∈ Ω a at hh
    rw [ContinuousLinearEquiv.symm_apply_apply] at hh
    exact (hpatch a hh).2
  have h5W (a : A) : ball (0 : Euclidean n) (5 * r) ⊆ ball 0 (T a).physicalRadius := by
    apply ball_subset_ball
    have hh : physicalRadius < (T a).physicalRadius := by simpa using hphysicalRadii a
    have hh' := hrCap.trans_le (min_le_right _ _)
    linarith
  have hmean (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (v : A → CarrierVariable n → ℝ) :
      EqOn (physicalDensityMean (d σ hσ) χ v) (physicalDensityMean (e σ) χ v)
        (ball 0 (5 * r)) := by
    have hscalar (a : A) (x : Euclidean n) (hx : x ∈ ball 0 (5 * r))
        (z : CarrierParameter) (hz : z ∈ tsupport (χ a)) :
        carrierScalarAmplitude (T a) (current σ hσ a).Q (sourceDilation G.map σ)
          (row a) (col a) (current σ hσ a).forward (current σ hσ a).inverse (fun _ ↦ σ)
          (x, parameter z) =
        sourceAmplitude (carrierScalarAmplitude (T a) (seed a).Q G.map
          (row a) (col a) (seed a).forward (seed a).inverse (fun _ ↦ 1)) σ (x, parameter z) := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hs, _, _⟩ := hcurrent σ hσ a
      have hp : (x, z) ∈ W a :=
        ⟨(ball_subset_ball (by linarith)) hx, hχV a hz⟩
      exact @hs (x, parameter z) (hcurrentDomain σ hσ a hp)
    exact physicalDensityMean_eq_normalized_of_scalar_transport T
      (fun a ↦ (seed a).Q) (fun a ↦ (current σ hσ a).Q) G.map row col
      (fun a ↦ (seed a).forward) (fun a ↦ (seed a).inverse)
      (fun a ↦ (current σ hσ a).forward) (fun a ↦ (current σ hσ a).inverse)
      hr hcell angular high χ hP hχpatch G.contDiff
      (fun x hx ↦ G.fullNormalRank x (hUG hx)) hphysical (fun a ↦ (seed a).frame_eq)
      htrans hσ.1 (hσ.2.trans hcap1) (fun a ↦ (current σ hσ a).frame_eq) h5W hscalar v
  have hzero (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) :
      EqOn (Hphysical σ hσ) (H σ) (ball 0 (5 * r)) := by
    simpa only [d, physicalDensityMean_retainedChart_zero] using hmean σ hσ 0
  have hresidual (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) :
      EqOn (Rphysical σ hσ) (R σ) (ball 0 (5 * r)) := by
    intro x hx
    change _ + Hphysical σ hσ x = _ + H σ x
    rw [hzero σ hσ hx]
  obtain ⟨hpos, hQ, hRphysical, σ₀, hσ₀, hσcap, cNormal, hcNormal, C, hC,
    hJ, hbound, hnormal, hfields, hres⟩ :=
    exists_retained_fixedSource_sobolev_bounds hn G hUG hP hΩ hKΩ hpatch hRc hτ hτR
      hbuffer hphysical χ hχ hχcompact W hr hcell h6U V hV hχV h6W seed hseed
      htrans hcap hcap1 current hcurrentDomain
  have h45 : ball (0 : Euclidean n) (4 * r) ⊆ ball 0 (5 * r) := ball_subset_ball (by linarith)
  have hR (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) : ContDiffOn ℝ ∞ (R σ) (ball 0 (4 * r)) :=
    (hRphysical σ hσ).congr (fun x hx ↦ (hresidual σ hσ (h45 hx)).symm)
  have hRliteral (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) : ContDiffOn ℝ ∞
      (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
      (ball 0 (4 * r)) := by
    simpa only [d, physicalDensityMean_retainedChart_zero] using hRphysical σ hσ
  refine ⟨hpos, hmean, ?_, hQ, hR, hRliteral, ?_, σ₀, hσ₀, hσcap,
    cNormal, hcNormal, C, hC, hJ, ?_, ?_, ?_, ?_⟩
  · intro hdetector σ hσ a
    have hsupport (x : Torus n) (z : CarrierParameter) (η : Euclidean (n - 1))
        (hx : FixedCutoffs.periodic hr hcell 1 x ≠ 0) (hz : angular a z η ≠ 0) :
        densityCoordinates (T a) (AmplitudeBound.centeredTorusRepresentative x, z) ∈
          Ioo (-τ a) (τ a) ×ˢ ball ((0 : Euclidean (n - 1)), z₀ a) (Rc a / 32) := by
      apply (outputCylinder_spec (hRc a) (hτ a)).2
      apply (hflow a).1
      have hzχ : χ a z ≠ 0 := by rw [hdetector a z η hz]; norm_num
      refine ⟨?_, hχV a (subset_tsupport (χ a) hzχ)⟩
      exact closedBall_subset_ball (by linarith : 4 * r < 12 * radiusCap)
        (FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hx))
    have hdomain : (coordinates (adaptedCoordinates (T a).data.adapted)) ⁻¹'
        (current σ hσ a).D ⊆ ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius) := by
      intro w hw
      have hh := (current σ hσ a).domain_coefficients hw
      change (coordinates (adaptedCoordinates (T a).data.adapted)).symm
        (coordinates (adaptedCoordinates (T a).data.adapted) w) ∈ Ω a at hh
      rw [ContinuousLinearEquiv.symm_apply_apply] at hh
      exact hpatch a hh
    obtain ⟨_, _, _, _, _, _, _, _, _, hscalar, _, _⟩ := hcurrent σ hσ a
    have hk := NormalizedSelection.carrierKernel_eq_normalized_of_scalar_transport
      (T a) (seed a).Q (current σ hσ a).Q G.contDiff
      (fun x hx ↦ G.fullNormalRank x (hUG hx)) (hphysical a) (seed a).frame_eq (htrans a)
      hσ.1 (hσ.2.trans hcap1) (current σ hσ a).frame_eq (row a) (col a)
      (seed a).forward (seed a).inverse (current σ hσ a).forward (current σ hσ a).inverse
      (fun _ ↦ 1) (fun _ ↦ σ) (hP a) hr hcell (angular a) (high a) hdomain
      (fun x z η hx hz ↦ (current σ hσ a).small_subset (hsupport x z η hx hz)) hscalar
    change carrierKernel (d σ hσ a) = carrierKernel (e σ a) at hk
    refine ⟨hk, ?_, ?_⟩
    · funext v x
      simp only [carrierTestIntegral, hk]
    · funext w u
      simp only [carrierAdjointIntegral, hk]
  · intro σ hσ
    have heq : EqOn
        (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
        (R σ) (ball 0 (4 * r)) := by
      simpa only [d, physicalDensityMean_retainedChart_zero] using
        (hresidual σ hσ).mono h45
    have hs := fixedSourceToL2_eq_of_residual_eqOn hr hcell (Q σ) (hQ σ hσ)
      (hRliteral σ hσ) (hR σ hσ) heq
    have hb := fixedResidualToL2_eq_of_residual_eqOn hr hcell (Q σ) (hQ σ hσ)
      (hRliteral σ hσ) (hR σ hσ) heq
    refine ⟨hs, hb, ?_⟩
    intro image B ψ
    dsimp only
    rw [hb]
    exact ⟨rfl, rfl⟩
  · intro σ hσ hs s
    have hb := (hbound σ hσ hs s).1
    rw [fixedSourceToL2_eq_of_residual_eqOn hr hcell (Q σ) (hQ σ hσ)
      (hRphysical σ hσ) (hR σ hσ) ((hresidual σ hσ).mono h45)] at hb
    refine ⟨hb, ?_, (hbound σ hσ hs s).2.2⟩
    have heq : cNorm (closedBall 0 (4 * r)) s (fun x ↦ Hphysical σ hσ x - H₀) =
        cNorm (closedBall 0 (4 * r)) s (fun x ↦ H σ x - H₀) := by
      unfold cNorm
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      apply Set.image_congr
      intro x hx
      have he : (fun y ↦ Hphysical σ hσ y - H₀) =ᶠ[nhds x] (fun y ↦ H σ y - H₀) := by
        filter_upwards [isOpen_ball.mem_nhds
          (closedBall_subset_ball (by linarith : 4 * r < 5 * r) hx)] with y hy
        rw [hzero σ hσ hy]
      exact congrArg norm ((he.iteratedFDeriv ℝ j).eq_of_nhds)
    rw [← heq]
    exact (hbound σ hσ hs s).2.1
  · intro σ hσ hs a x hx z hz
    have hn' := hnormal σ hσ hs a x hx z hz
    refine ⟨hn', ?_⟩
    change cNormal ≤ ‖normalizedPullback ((seed a).normal (fun _ ↦ 1)) (σ, (x, z))‖
    rw [← (hfields σ hσ a x hx z hz).1]
    exact hn'
  · intro a x z hz
    have hσ : σ₀ ∈ Ioc (0 : ℝ) cap := ⟨hσ₀, hσcap⟩
    have hx : (0 : Euclidean n) ∈ closedBall 0 (4 * r) := mem_closedBall_self (by positivity)
    have hn' := hnormal σ₀ hσ le_rfl a 0 hx z hz
    rw [(hfields σ₀ hσ a 0 hx z hz).1] at hn'
    change cNormal ≤ ‖normalizedPullback ((seed a).normal (fun _ ↦ 1)) (0, (x, z))‖
    simpa only [normalizedPullback, smul_zero, zero_smul] using hn'
  · intro σ hσ x hx
    exact (hresidual σ hσ hx).symm.trans
      ((hres σ hσ hx).trans (congrArg (· - H₀) (hzero σ hσ hx)))

end JanetCartan.PositiveBackground
