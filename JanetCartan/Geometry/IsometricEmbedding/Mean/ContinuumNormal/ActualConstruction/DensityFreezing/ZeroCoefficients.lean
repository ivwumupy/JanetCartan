module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityFreezing
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourcePrimitives
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.NormalizedCarrierBaseline.DensityControls

/-!
# The original density class on both zero-scale coefficient fields

The spatial-freezing comparison uses the actual divided-footpoint zero slice
and the frozen-label zero slice. Apply the normalized seed coefficient bounds
and the original-density composition estimate to these literal fields. The
same coefficient charts and all masks are retained. Both constants precede
the density, whose original `L/4` domain, `L/8` interval and `μ+14` budget are
unchanged. No coefficient norm or label norm is an input.

Consumer: the `μ+1` full-amplitude budgets in
`exists_sourceDensityLimit_frozen_error_constant` and hence the local gap in
`app:ch_background:prop:bg-frame`. The supplied seed, ODE identities and
original source range are the outputs of the retained normalized selection.
This file does not select another row or assert its bounded realization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport ContinuumNormalReduction.TransportSymbol NormalizedBackground.SourceGeometry
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity

/-- Both zero-scale labels are smooth and stay in the original `L/16` ball
on the whole supplied physical/carrier product. For the frozen label this
follows by evaluating the actual source label at the spatial origin, not by
identifying the two labels away from the origin. Consumers: the literal
zero-scale density coefficient and primitive bounds
(`app:ch_background:eq:bg-Nsigma`, `bg-full-complex-amplitude`). -/
theorem source_zero_density_labels_regular
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16))) :
    let gActual := fun p ↦ sourceDensityFootpointExtension T Y (0, p)
    let gFrozen := fun p : Euclidean n × CarrierParameter ↦
      ((0 : Euclidean (n - 1)), parameter p.2)
    ContDiffOn ℝ ∞ gActual (ball 0 R ×ˢ V) ∧
      MapsTo gActual (ball 0 R ×ˢ V)
        (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16)) ∧
      ContDiffOn ℝ ∞ gFrozen (ball 0 R ×ˢ V) ∧
      MapsTo gFrozen (ball 0 R ×ˢ V)
        (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
  obtain ⟨hActual, hActualRange⟩ :=
    NormalizedNormalLimit.source_footpoint_original_domain_regular T hR hV
      hY hzero hparam hs₀ hsource 0
      ⟨le_rfl, le_min hs₀.le (by norm_num)⟩
  refine ⟨hActual, hActualRange,
    (contDiff_const.prodMk (parameter.contDiff.comp contDiff_snd)).contDiffOn, ?_⟩
  intro p hp
  have h := hActualRange (show ((0 : Euclidean n), p.2) ∈ ball 0 R ×ˢ V from
    ⟨mem_ball_self hR, hp.2⟩)
  simpa only [sourceDensityFootpointExtension_zero_at_origin] using h

/-- Construct common `μ+1` coefficient controls for the literal transported
and frozen-label density weights on the SAME normalized unit seed at zero.
The seed coefficient producer and the original source-footpoint producer
discharge all unweighted coefficient, label regularity, range and norm inputs.
The constants precede every permitted nonconstant initial density; no smaller
density interval or stronger density norm is imposed. Consumer:
`exists_sourceDensityLimit_frozen_error_constant`, via the existing primitive
full-amplitude theorem (`app:ch_background:prop:bg-frame`, `bg-Nsigma`,
`bg-mixed-input`, `bg-commutator`). -/
theorem exists_source_zero_density_coefficient_controls
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (measurement : Euclidean n → ℝ)
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hm : ContDiffOn ℝ ∞ measurement D.measurement.region)
    (ha : ContDiffOn ℝ ∞ (fun p ↦ angular p.1 p.2) D.angular.region)
    (hh : ContDiffOn ℝ ∞ high D.high.region) :
    let a := TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high 0) measurement
    ∃ M > (0 : ℝ), ∃ B ≥ (1 : ℝ),
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) →
      (∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) →
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8),
        1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
        (2 * (n + 1) + 14) v ≤ 1 →
      D.Controls (2 * (n + 1) + 1) M B 1
        {a with normal := fun p ↦
          Real.sqrt (1 + v (sourceDensityFootpointExtension T Y (0, p))) • a.normal p} ∧
      D.Controls (2 * (n + 1) + 1) M B 1
        {a with normal := fun p ↦ Real.sqrt (1 + v (0, parameter p.2)) • a.normal p} := by
  let μ := 2 * (n + 1)
  obtain ⟨M₀, hM₀, _, _, _, hbase, _⟩ :=
    exists_normalizedCarrierData_coefficient_controls T Q₀ F row col Φ Y (fun _ ↦ 1)
      hr hcell angular high measurement hP hseed hF hi hrank hR hRT hRU hV hVP hb
      D hD hm ha hh μ
  obtain ⟨hActual, hActualRange, hFrozen, hFrozenRange⟩ :=
    source_zero_density_labels_regular T hR hV hY hzero hparam hs₀ hsource
  let gActual := fun p ↦ sourceDensityFootpointExtension T Y (0, p)
  let gFrozen := fun p : Euclidean n × CarrierParameter ↦
    ((0 : Euclidean (n - 1)), parameter p.2)
  let G := cNorm D.field.carrier (μ + 1) gActual +
    cNorm D.field.carrier (μ + 1) gFrozen
  have hG : 0 ≤ G := add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..)
  have hActualG : cNorm D.field.carrier (μ + 1) gActual ≤ G :=
    le_add_of_nonneg_right (cNorm_nonneg ..)
  have hFrozenG : cNorm D.field.carrier (μ + 1) gFrozen ≤ G :=
    le_add_of_nonneg_left (cNorm_nonneg ..)
  have hsmall : closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16) ⊆
      ball ((0 : Euclidean (n - 1)), zCell) (L / 4) :=
    closedBall_subset_ball (by linarith)
  have hsmall' : closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16) ⊆
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8) :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨M, hM, B, hB, hcontrols⟩ :=
    ContinuumCommutator.NormalizedCarrierBaseline.exists_original_density_normal_controls
      (N := N) D ((0 : Euclidean (n - 1)), zCell) hL hM₀.le
      (by linarith : 1 ≤ M₀ + 1) hG
  refine ⟨M, hM, B, hB, ?_⟩
  intro v hv hpos hinterval hvnorm
  constructor
  · exact hcontrols _ gActual hbase (hActual.mono hD)
      (fun p hp ↦ hsmall (hActualRange (hD hp)))
      (fun p hp ↦ hsmall' (hActualRange (hD (D.field.ball_subset hp))))
      hActualG v hv hpos hinterval hvnorm
  · exact hcontrols _ gFrozen hbase (hFrozen.mono hD)
      (fun p hp ↦ hsmall (hFrozenRange (hD hp)))
      (fun p hp ↦ hsmall' (hFrozenRange (hD (D.field.ball_subset hp))))
      hFrozenG v hv hpos hinterval hvnorm

end JanetCartan.ContinuumNormal.ActualConstruction
