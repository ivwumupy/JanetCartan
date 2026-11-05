module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedCarrierProfiles.SeedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedCarrierProfiles.DensityCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedCarrierProfiles.SourceFootpoint

/-!
# All-order controls of the actual normalized positive-density carrier

The existing source matching identifies the physical carrier with the seed
normalization on the supplied primitive chart. Apply the all-order seed and
ODE-footpoint profiles before varying the density. The original `μ+14` class
gives the separate low `μ+1` bound; the high estimate retains one `C^p` norm.
These controls feed the actual full reflected matrix amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedCarrierProfiles
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport CanonicalCarrier
open ContinuumNormal.FrozenModel ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference NormalizedBackground.SourceGeometry SourceMatching
open ContinuumNormalReduction.TransportSymbol

/-- Actual source matching on the open primitive buffer preserves every
control with its original high factor (`app:ch_background:eq:bg-Nsigma`). -/
private theorem primitive_controls_of_eqOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : PrimitiveNormChart E} {p : ℕ} {M B H : ℝ} {f g : E → F}
    (h : D.Controls p M B H f) (heq : EqOn g f D.region) :
    D.Controls p M B H g := by
  have hn (j) : cNorm D.carrier j g = cNorm D.carrier j f := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ j
    intro x hx
    filter_upwards [D.isOpen_region.mem_nhds (D.ball_subset hx)] with y hy
    exact heq hy
  exact ⟨h.smooth.congr (fun x hx ↦ heq hx), (hn 1).trans_le h.low,
    by rw [hn]; exact h.high⟩

/-- The scalar source identity supplied by the retained initializer identifies
both nonconstant coefficient fields for its SAME actual carrier. The seed
initial scalar is arbitrary but fixed; no new null flow is chosen. This is the
connection from `NormalizedSelection.exists_retained_source_carrier_integrals`
to uniform reflected-amplitude bounds (`app:ch_background:eq:bg-Nsigma`). -/
theorem coefficientsOfCarrier_current_eq_normalized_of_scalar_transport
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (row col : Fin n)
    (Φ Y Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial initialσ : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {p : Euclidean n × CarrierParameter}
    (hx : p.1 ∈ ball (0 : Euclidean n) T.physicalRadius)
    (hz : parameter p.2 ∈ parameterInterior (2 * P.radius))
    (hscalar : carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ initialσ
        (p.1, parameter p.2) =
      sourceAmplitude (carrierScalarAmplitude T Q₀ F row col Φ Y initial)
        σ (p.1, parameter p.2)) :
    let a := TransportKernel.coefficientsOfCarrier
      (data T Qσ (sourceDilation F σ) row col Φσ Yσ initialσ hr hcell angular high)
      (FixedCutoffs.physical hr 1)
    let b := TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y initial hr hcell angular high σ)
      (FixedCutoffs.physical hr 1)
    a.normal p = b.normal p ∧ a.reduced p = b.reduced p := by
  have hsx := (convex_ball (0 : Euclidean n) T.physicalRadius).smul_mem_of_zero_mem
    (mem_ball_self T.physicalRadius_pos) hx ⟨hσ.le, hσ1⟩
  have hzC : parameter p.2 ∈ parameterCube (2 * P.radius) := fun i ↦ (hz i).le
  have hxU := (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
    (T.target_contains_closed hsx hzC)).1
  have hgrad := current_carrierGradient_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled hx hzC
  have hnull := current_carrierNullvector_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled col hx hzC
  have hn := coefficientsOfCarrier_normalizedCarrierData_eq_source T Q₀ F row col Φ Y
    initial hr hcell angular high (FixedCutoffs.physical hr 1) hP hseed hsx hz
  have hs := normalizedSourceCoefficients_eq_sourceDilation hF
    (fun q ↦ T.carrierGradient Q₀ q.1 (parameter q.2))
    (fun q ↦ carrierScalarAmplitude T Q₀ F row col Φ Y initial (q.1, parameter q.2) •
      carrierNullvector T Q₀ col (q.1, parameter q.2))
    (FixedCutoffs.physical hr 1) (fun q ↦ angular q.1 q.2) high hσ p (hrank _ hxU)
  dsimp only
  constructor
  · rw [hn.1, hs.1]
    change normalField T Qσ (sourceDilation F σ) row col Φσ Yσ initialσ p.1 p.2 = _
    simp only [normalField, hgrad, hscalar, hnull, sourceAmplitude, smul_smul, smul_eq_mul]
  · rw [hn.2, hs.2, coefficientsOfCarrier_data]
    change (quadratic (Qσ.1 p.1) (T.carrierGradient Qσ p.1 (parameter p.2))).ofLp = _
    rw [hscaled, hgrad]

/-- Actual source-carrier coefficients with initial scalar
`σ * sqrt (1 + v)` have all-order bounds on one common scale interval.
Their constants precede the varying scale, its matched actual ODE maps,
and the density. The two matching identities are exactly the output of
`exists_retained_seed_matched_unit_transport`; no coefficient or footpoint
norm is assumed. The original density balls, masks and detector are retained
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:eq:bg-mixed-input`,
`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_actual_source_density_all_order_controls
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {c C : ℝ} (hP : P.IsValid c C)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiff ℝ ∞ F) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius)
    (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hm : ContDiffOn ℝ ∞ (FixedCutoffs.physical hr 1) D.measurement.region)
    (ha : ContDiffOn ℝ ∞ (fun p ↦ angular p.1 p.2) D.angular.region)
    (hh : ContDiffOn ℝ ∞ high D.high.region)
    (p₀ : Euclidean (n - 1) × Euclidean 3) {Rinitial : ℝ} (hRinitial : 0 < Rinitial) :
    ∃ M > (0 : ℝ), ∃ B : ℕ → ℝ, (∀ p, 1 ≤ B p) ∧
      ∀ σ ∈ Ioc (0 : ℝ) (1 / 8),
      ∀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ) →
      ∀ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
        D.field.region →
      EqOn (fun p : Euclidean n × CarrierParameter ↦
        carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ)
          (p.1, parameter p.2) • carrierNullvector T Qσ col (p.1, parameter p.2))
        (fun p ↦ sourceAmplitude (fun w ↦
          carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) w •
            carrierNullvector T Q₀ col w) σ (p.1, parameter p.2)) D.field.region →
      MapsTo (densityFootpoint T Yσ) D.field.region (ball p₀ (Rinitial / 4)) →
      MapsTo (densityFootpoint T Yσ) D.field.carrier (closedBall p₀ (Rinitial / 8)) →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball p₀ (Rinitial / 4)) →
      (∀ q ∈ ball p₀ (Rinitial / 4), 0 < 1 + v q) →
      (∀ q ∈ closedBall p₀ (Rinitial / 8), 1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall p₀ (Rinitial / 8)) (2 * (n + 1) + 14) v ≤ 1 →
      let d := TransportKernel.coefficientsOfCarrier
        (data T Qσ (sourceDilation F σ) row col Φσ Yσ
          (fun q ↦ positiveDensityAmplitude σ (v q)) hr hcell angular high)
        (FixedCutoffs.physical hr 1)
      (∀ p, D.Controls p M (B p) (1 + cNorm (closedBall p₀ (Rinitial / 8)) p v) d) ∧
        D.Controls (2 * (n + 1) + 1) M (2 * B (2 * (n + 1) + 1)) 1 d := by
  obtain ⟨M₀, hM₀, B₀, hB₀, hcoeff⟩ := exists_normalizedCarrierData_all_order_controls
    T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high (FixedCutoffs.physical hr 1)
    hP hseed hF.contDiffOn hi hrank hR hRT hRU hV hVP hb D hD hm ha hh
  obtain ⟨G, _, hfoot⟩ := exists_source_densityFootpoint_profiles
    T Y hR hV hY hzero hparam D.field hD
  obtain ⟨M, hM, B, hB, hweight⟩ := exists_density_weighted_coefficient_controls
    T D p₀ hRinitial G hM₀.le B₀ hB₀
  refine ⟨M, hM, B, hB, ?_⟩
  intro σ hσ Qσ hscaled Φσ Yσ hflow hnull hrange hcompact v hv hpos hinterval hvnorm
  have hσ1 : σ ≤ 1 := hσ.2.trans (by norm_num)
  let a := TransportKernel.coefficientsOfCarrier
    (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ)
    (FixedCutoffs.physical hr 1)
  obtain ⟨hg, hgG⟩ := hfoot σ hσ Yσ hflow
  obtain ⟨hhigh, hlow⟩ := hweight a (hcoeff σ ⟨hσ.1.le, hσ1⟩)
    Yσ hg hrange hcompact hgG v hv hpos hinterval hvnorm
  have heq (q : Euclidean n × CarrierParameter) (hq : q ∈ D.field.region) :=
    coefficientsOfCarrier_current_eq_normalized hP T Q₀ Qσ hF hrank hphysical
      hseed htrans hσ.1 hσ1 hscaled row col Φ Y Φσ Yσ hr hcell angular high
      (ball_subset_ball hRT (hD hq).1)
      (fun i ↦ (hVP (hD hq).2 i).trans (by linarith only [hP.1])) (hnull hq)
  have hnormal : EqOn
      (fun q : Euclidean n × CarrierParameter ↦ normalField T Qσ (sourceDilation F σ)
        row col Φσ Yσ (fun y ↦ positiveDensityAmplitude σ (v y)) q.1 q.2)
      (fun q ↦ Real.sqrt (1 + v (densityFootpoint T Yσ q)) • a.normal q) D.field.region := by
    intro q hq
    change normalField T Qσ (sourceDilation F σ) row col Φσ Yσ
      (fun y ↦ (fun _ ↦ σ) y * Real.sqrt (1 + v y)) q.1 q.2 = _
    rw [normalField_initial_mul T Qσ (sourceDilation F σ) row col Φσ Yσ
      (fun _ ↦ σ) (fun y ↦ Real.sqrt (1 + v y))]
    exact congrArg (fun z ↦ Real.sqrt (1 + v (densityFootpoint T Yσ q)) • z) (heq q hq).1
  constructor
  · intro p
    exact ⟨(hhigh p).measurement, (hhigh p).angular, (hhigh p).high,
      primitive_controls_of_eqOn (hhigh p).normal hnormal,
      primitive_controls_of_eqOn (hhigh p).reduced (fun q hq ↦ (heq q hq).2)⟩
  · exact ⟨hlow.measurement, hlow.angular, hlow.high,
      primitive_controls_of_eqOn hlow.normal hnormal,
      primitive_controls_of_eqOn hlow.reduced (fun q hq ↦ (heq q hq).2)⟩

/-- Uniform primitive bounds for the actual carrier retained by scalar source
matching. The seed scalar is fixed before the constants, and the current
scalar is allowed to be the initializer's exact scaled scalar. This uses the
literal principal-normal scaling and normalized second-jet coefficients;
it does not reselect the row or either ODE map. Consumer: the fixed-scalar
full reflected-amplitude bounds for the normalized row
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_actual_source_carrier_all_order_controls
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {c C : ℝ} (hP : P.IsValid c C)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiff ℝ ∞ F) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius)
    (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y initial (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hm : ContDiffOn ℝ ∞ (FixedCutoffs.physical hr 1) D.measurement.region)
    (ha : ContDiffOn ℝ ∞ (fun p ↦ angular p.1 p.2) D.angular.region)
    (hh : ContDiffOn ℝ ∞ high D.high.region) :
    ∃ M > (0 : ℝ), ∃ B : ℕ → ℝ, (∀ p, 1 ≤ B p) ∧
      ∀ σ ∈ Ioc (0 : ℝ) 1,
      ∀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ) →
      ∀ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      ∀ initialσ : Euclidean (n - 1) × Euclidean 3 → ℝ,
      EqOn (fun p : Euclidean n × CarrierParameter ↦
        carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ initialσ
          (p.1, parameter p.2))
        (fun p ↦ sourceAmplitude (carrierScalarAmplitude T Q₀ F row col Φ Y initial)
          σ (p.1, parameter p.2)) D.field.region →
      ∀ p, D.Controls p M (B p) 1
        (TransportKernel.coefficientsOfCarrier
          (data T Qσ (sourceDilation F σ) row col Φσ Yσ initialσ hr hcell angular high)
          (FixedCutoffs.physical hr 1)) := by
  obtain ⟨M, hM, B, hB, hcoeff⟩ := exists_normalizedCarrierData_all_order_controls
    T Q₀ F row col Φ Y initial hr hcell angular high (FixedCutoffs.physical hr 1)
    hP hseed hF.contDiffOn hi hrank hR hRT hRU hV hVP hb D hD hm ha hh
  refine ⟨M, hM, B, hB, ?_⟩
  intro σ hσ Qσ hscaled Φσ Yσ initialσ hscalar p
  have hc := hcoeff σ ⟨hσ.1.le, hσ.2⟩ p
  have heq (q : Euclidean n × CarrierParameter) (hq : q ∈ D.field.region) :=
    coefficientsOfCarrier_current_eq_normalized_of_scalar_transport hP T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ.1 hσ.2 hscaled row col Φ Y Φσ Yσ initial initialσ
      hr hcell angular high (ball_subset_ball hRT (hD hq).1)
      (fun i ↦ (hVP (hD hq).2 i).trans (by linarith only [hP.1])) (hscalar hq)
  exact ⟨hc.measurement, hc.angular, hc.high,
    primitive_controls_of_eqOn hc.normal (fun q hq ↦ (heq q hq).1),
    primitive_controls_of_eqOn hc.reduced (fun q hq ↦ (heq q hq).2)⟩

end JanetCartan.ContinuumRow.NormalizedCarrierProfiles
