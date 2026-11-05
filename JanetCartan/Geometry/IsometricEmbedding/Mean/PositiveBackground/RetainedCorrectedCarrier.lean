module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CorrectedPositiveInverse.CanonicalTransport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedDensityMean
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedCharts

/-!
# The retained positive scalar realizes the corrected normalized carrier

The source inverse constructs a density on the original normalized row.
The wider-density normal construction realizes the canonical carrier with
initial scalar `σ * sqrt (1 + v)`. Here the retained Hamilton/ODE footpoint
identity identifies that carrier with `correctedCarrierData`, before taking
either integral action. The second theorem also applies source-flow uniqueness
to the supplied seed and current chart, so the original normalized data is kept.

The concrete consumer is the literal test-action clause of
`PositiveBackground.exists_uncorrectedDensity_and_correctedQ0_with_exterior`.
`ActualConstruction.exists_finite_seed_source_normal_realizations` constructs
the canonical positive carrier and its adjoint; these identities transfer those
actions without choosing another operator or identifying independent charts.
The uniform positive gap and elliptic estimates remain separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PositiveBackground
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier CanonicalConic ContinuumAdjoint.Canonical
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedChartMean
open CurrentMean.PreparationTransportPrimitives CorrectedPositiveInverse

/-- The canonical carrier with the SAME retained chart and positive initial
scalar has exactly the kernel, test integral and adjoint integral of the
corrected original carrier. The footpoint identity follows from the chart's
ODE and Hamilton equations on the full supplied detector support; it is not
an additional analytic premise. No density regularity or positivity is needed
for this algebraic identification (`app:ch_background:eq:bg-T`,
`app:ch_background:eq:bg-affine-mean`, `app:ch_background:prop:bg-positive`).

This supplies the literal corrected-carrier action required by
`CorrectedSourceInverse.hwide` from a retained canonical realization. -/
theorem retained_positiveScalar_kernel_and_integrals
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω Kc : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {Rc M τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (chart : Chart T Ω Kc p₀ Rc M τ row col F)
    {cP CP : ℝ} (hP : P.IsValid cP CP)
    (hF : ContDiffOn ℝ ∞ F U) (hrank : HasFullNormalRankOn F U) (hτ : 0 < τ)
    (hΩ : Ω ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ parameterInterior (3 * P.radius / 2))
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hflow : MapsTo (densityCoordinates T)
      (closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport z₀ (r := a)) chart.D)
    (high : ℝ → ℝ) (σ : ℝ) (v : CarrierVariable n → ℝ) :
    let angular := angularMask z₀ θ₀ ha hb
    let d := data T chart.Q F row col chart.forward chart.inverse (fun _ ↦ σ)
      hr hcell angular high
    let dpositive := data T chart.Q F row col chart.forward chart.inverse
      (fun q ↦ positiveDensityAmplitude σ (densityOnInitialLabels v q))
      hr hcell angular high
    carrierKernel dpositive = carrierKernel (correctedCarrierData d v) ∧
      carrierTestIntegral dpositive = carrierTestIntegral (correctedCarrierData d v) ∧
      carrierAdjointIntegral dpositive = carrierAdjointIntegral (correctedCarrierData d v) := by
  intro angular d dpositive
  have hgeom : coordinates (adaptedCoordinates T.data.adapted) ⁻¹' chart.D ⊆
      (ball 0 T.physicalRadius ∩ interior U) ×ˢ parameterInterior (3 * P.radius / 2) := by
    intro q hq
    have hqΩ : q ∈ Ω := by
      have hh := chart.domain_coefficients hq
      simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hh
    have hh := hΩ hqΩ
    exact ⟨⟨hh.1.2, by simpa only [hU.interior_eq] using hh.1.1⟩, hh.2⟩
  have hkernel : carrierKernel dpositive = carrierKernel (correctedCarrierData d v) := by
    apply (canonical_kernel_same_density T chart.Q F row col chart.forward chart.inverse
      σ v hr hcell angular high ?_).symm
    intro x hx u _hm hu
    obtain ⟨hs, hv, _⟩ := angularMask_nonzero z₀ θ₀ ha hb hu
    have hz : u.1 ∈ carrierSupport z₀ (r := a) :=
      ⟨ball_subset_closedBall hs, ball_subset_closedBall hv⟩
    have hp : densityCoordinates T (AmplitudeBound.centeredTorusRepresentative x, u.1) ∈
        chart.D := @hflow (AmplitudeBound.centeredTorusRepresentative x, u.1) ⟨hx, hz⟩
    exact retainedChart_footpoint_eq chart hP hF hrank (Subset.rfl : U ⊆ U) hτ hgeom
      (p := (AmplitudeBound.centeredTorusRepresentative x, u.1)) hp
  refine ⟨hkernel, ?_, ?_⟩
  · funext f x
    simp only [carrierTestIntegral, hkernel]
  · funext w u
    simp only [carrierAdjointIntegral, hkernel]

/-- The actual positive scalar on a supplied contracted chart realizes
`correctedCarrierData` of the SAME normalized seed row. Source-flow uniqueness
identifies the uncorrected kernel, and Hamilton scaling identifies the density's
transported label on the complete detector support. Both literal integral
actions follow with their original measures and masks. The result applies to
any supplied current chart with the retained seed/domain/minor data; it does
not equate independently chosen charts or choose another density
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:eq:bg-density-four`,
`app:ch_background:prop:bg-normalized`, `app:ch_background:prop:bg-frame`).

Consumer: the normalized `CorrectedSourceInverse.hwide` test action, using the
canonical carriers and literal adjoints of
`ActualConstruction.exists_finite_seed_source_normal_realizations`.
The original finite-low density class and its high profiles are unchanged. -/
theorem retained_source_positiveScalar_kernel_and_integrals
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {cP CP : ℝ} (hP : P.IsValid cP CP)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc M τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hpatch : Ω ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc M τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (current : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc M τ row col (sourceDilation F σ))
    (hrankσ : HasFullNormalRankOn (sourceDilation F σ) U)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hflow : MapsTo (densityCoordinates T)
      (closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport z₀ (r := a))
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    (high : ℝ → ℝ) (v : CarrierVariable n → ℝ) (hv : ∀ p, 0 ≤ 1 + v p) :
    let angular := angularMask z₀ θ₀ ha hb
    let e := ContinuumNormal.FrozenModel.normalizedCarrierData T seed.Q F row col
      seed.forward seed.inverse (fun _ ↦ 1) hr hcell angular high σ
    let dpositive := data T current.Q (sourceDilation F σ) row col current.forward current.inverse
      (fun q ↦ positiveDensityAmplitude σ (densityOnInitialLabels v q))
      hr hcell angular high
    carrierKernel dpositive = carrierKernel (correctedCarrierData e v) ∧
      carrierTestIntegral dpositive = carrierTestIntegral (correctedCarrierData e v) ∧
      carrierAdjointIntegral dpositive = carrierAdjointIntegral (correctedCarrierData e v) := by
  intro angular e dpositive
  let d := data T current.Q (sourceDilation F σ) row col current.forward current.inverse
    (fun _ ↦ σ) hr hcell angular high
  have hflowCurrent : MapsTo (densityCoordinates T)
      (closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport z₀ (r := a)) current.D :=
    (hflow.mono_right (outputCylinder_spec hRc hτ).2).mono_right current.small_subset
  have hpatch₂ : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius) := by
    intro p hp
    exact ⟨(hpatch hp).1.2, fun j ↦ ((hpatch hp).2 j).trans (by linarith only [hP.1])⟩
  have hsupport (x : Torus n) (z : CarrierParameter) (η : Euclidean (n - 1))
      (hm : FixedCutoffs.periodic hr hcell 1 x ≠ 0) (hz : angular z η ≠ 0) :
      densityCoordinates T (AmplitudeBound.centeredTorusRepresentative x, z) ∈
        Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), zCell) (Rc / 32) := by
    obtain ⟨hs, ht, _⟩ := angularMask_nonzero z₀ θ₀ ha hb hz
    exact (outputCylinder_spec hRc hτ).2 (@hflow (AmplitudeBound.centeredTorusRepresentative x, z)
      ⟨FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hm),
        ball_subset_closedBall hs, ball_subset_closedBall ht⟩)
  have hunc : carrierKernel d = carrierKernel e :=
    (NormalizedSelection.retained_chart_normalized_kernel_and_integrals T hP hΩ
      hKΩ hpatch₂ hRc hτ hτR hbuffer hF hrank hphysical seed htrans hflat
      hr hcell angular high hsupport hσ hσ1 current).1
  have hpositive : carrierKernel dpositive = carrierKernel (correctedCarrierData d v) :=
    (retained_positiveScalar_kernel_and_integrals current hP
      (contDiff_sourceDilation hF).contDiffOn hrankσ hτ hpatch
      hr hcell z₀ θ₀ ha hb hflowCurrent high σ v).1
  have hkernel : carrierKernel dpositive = carrierKernel (correctedCarrierData e v) := by
    rw [hpositive]
    funext x u
    rw [carrierKernel_corrected d v hv, carrierKernel_corrected e v hv,
      congrFun (congrFun hunc x) u]
    by_cases hm : FixedCutoffs.periodic hr hcell 1 x = 0
    · have hz : carrierKernel e x u = 0 := CommonMeasurement.carrierKernel_zero_of_measurement e hm u
      simp only [hz, smul_zero]
    by_cases ha₀ : angular u.1 (‖u.2‖⁻¹ • u.2) = 0
    · have hz : carrierKernel e x u = 0 := by
        simp [carrierKernel, carrierAmplitude, e,
          ContinuumNormal.FrozenModel.normalizedCarrierData, data, ha₀]
      simp only [hz, smul_zero]
    have hp := current.small_subset (hsupport x u.1 (‖u.2‖⁻¹ • u.2) hm ha₀)
    have hpΩ : (AmplitudeBound.centeredTorusRepresentative x, parameter u.1) ∈ Ω := by
      have hh := current.domain_coefficients hp
      change (coordinates (adaptedCoordinates T.data.adapted)).symm
        (coordinates (adaptedCoordinates T.data.adapted)
          (AmplitudeBound.centeredTorusRepresentative x, parameter u.1)) ∈ Ω at hh
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
    have htAll := (SourceMatching.current_transportPosition_source_dilation_on_patch
      T seed.Q current.Q hF hrank hphysical seed.frame_eq htrans hσ hσ1 current.frame_eq).1
    have hpoint := @hpatch₂ (AmplitudeBound.centeredTorusRepresentative x, parameter u.1) hpΩ
    have ht : transportPosition T current.Q (AmplitudeBound.centeredTorusRepresentative x, u.1) =
        ContinuumNormal.FrozenModel.normalizedTransportPosition T seed.Q σ
          (AmplitudeBound.centeredTorusRepresentative x, u.1) :=
      @htAll (AmplitudeBound.centeredTorusRepresentative x, u.1) ⟨hpoint.1, hpoint.2⟩
    change (1 + v (u.1, transportPosition T current.Q
      (AmplitudeBound.centeredTorusRepresentative x, u.1))) • carrierKernel e x u = _
    rw [ht]
    rfl
  refine ⟨hkernel, ?_, ?_⟩
  · funext f x
    simp only [carrierTestIntegral, hkernel]
  · funext w u
    simp only [carrierAdjointIntegral, hkernel]

end JanetCartan.PositiveBackground
