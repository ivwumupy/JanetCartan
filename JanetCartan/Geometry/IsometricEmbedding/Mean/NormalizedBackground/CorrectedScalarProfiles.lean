module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.InitialScalar
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.SupportedData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedCorrectedCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalSourceLabels
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.DensityScalar

/-!
# The corrected scalar on the original normalized carrier

The original positive density class supplies the scalar extension and its
reserve profiles for the raw-adjoint endpoint. Source-flow uniqueness and
Hamilton geometry identify its kernel with the corrected carrier on the same
normalized seed row. Neither the detector masks nor the measurement radius
are selected again. The original density high norms remain explicit.

These are concrete scalar and kernel inputs of
`PositiveBackground.CorrectedSourceInverse.hwide`. The same-family corrected
raw-adjoint application and the original initialized positive-background
construction remain separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.NormalizedBackground
open ContinuumRow PositiveBackground CorrectedPositiveInverse
open ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.AmplitudeProfiles
open ActualCarriers FrozenMenu CurrentFullPhase

/-- Apply the original positive-density class to the existing scalar extension
and reserve interpolation. This constructs its global real/complex smoothness,
compact support and every derivative profile. Constants precede the density
and source scale, the finite-low class remains `2*(n+1)+14`, and the high
budget is the actual density norm on the SAME `L/8` label ball. The source
factor is retained in the unit normal, so the normalized scalar here is
`sqrt (1+v)` (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:prop:bg-normalized`, `app:ch_waves:eq:joint-tame`).

Consumer: the `A₀` scalar input of the uniform scalar-transport raw-adjoint
endpoint, for `PositiveBackground.CorrectedSourceInverse.hwide`. This proves
the scalar input and does not assert the completed corrected raw estimate. -/
theorem exists_corrected_initial_scalar_reserve_profiles
    {n : ℕ} (zCell : Euclidean 3) {L : ℝ} (hL : 0 < L) :
    ∃ A : ℕ → ℕ → ℝ, (∀ s i, 0 ≤ A s i) ∧
      ∀ (v : CarrierVariable n → ℝ), ContDiff ℝ ∞ v →
        (∀ q, 1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
        cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
          (2 * (n + 1) + 14) (densityOnInitialLabels v) ≤ 1 →
      let a := extendedInitialScalar zCell hL
        (fun q ↦ positiveDensityAmplitude 1 (densityOnInitialLabels v q))
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ (fun q ↦ (a q : ℂ)) ∧
        HasCompactSupport a ∧
        ∀ s (H : ℝ), 1 + cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
          (s + 2 * (n + 1) + 14) (densityOnInitialLabels v) ≤ H →
        ∀ p i, i ≤ s + 2 * (n + 1) →
          ‖iteratedFDeriv ℝ i (fun q ↦ (a q : ℂ)) p‖ ≤
            A s i * H ^ (((i - 2 * (n + 1) : ℕ) : ℝ) / (max s 1 : ℕ)) := by
  obtain ⟨C, hC, hscalar⟩ := LeadingPrimitive.DensityScalar.exists_initial_scalar_tame_bounds
    n ((0 : Euclidean (n - 1)), zCell) hL
  choose A₀ hA₀ hprofile using fun s : ℕ ↦
    exists_extendedInitialScalar_profile (n := n) zCell hL (2 * C (2 * (n + 1))) s
  let A := fun s i ↦ A₀ s i * (1 + C (s + 2 * (n + 1))) ^
    (((i - 2 * (n + 1) : ℕ) : ℝ) / (max s 1 : ℕ))
  have hfactor (s : ℕ) : 0 < 1 + C (s + 2 * (n + 1)) := by linarith [hC (s + 2 * (n + 1))]
  refine ⟨A, fun s i ↦ mul_nonneg (hA₀ s i) (Real.rpow_nonneg (hfactor s).le _), ?_⟩
  intro v hv hinterval hlow a
  let initial := fun q ↦ positiveDensityAmplitude 1 (densityOnInitialLabels v q)
  have hvlabel := contDiff_densityOnInitialLabels hv
  have hpos (q : Euclidean (n - 1) × Euclidean 3) : 0 < 1 + densityOnInitialLabels v q :=
    lt_of_lt_of_le (by norm_num) (hinterval _).1
  have hinitial : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) :=
    contDiffOn_positiveDensityAmplitude 1 hvlabel.contDiffOn (fun q _ ↦ hpos q)
  have hnorm (j : ℕ) : cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) j initial ≤
      C j * (1 + cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) j
        (densityOnInitialLabels v)) := by
    simpa only [one_mul] using hscalar 1 zero_le_one (densityOnInitialLabels v)
      hvlabel.contDiffOn (fun q _ ↦ hpos q) (fun q _ ↦ hinterval _) j
  have hlo : cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (2 * (n + 1)) initial ≤
      2 * C (2 * (n + 1)) := by
    have hvlow := (cNorm_mono_order (f := densityOnInitialLabels v)
      (s := closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
      (by omega : 2 * (n + 1) ≤ 2 * (n + 1) + 14)).trans hlow
    exact (hnorm _).trans (by nlinarith [hC (2 * (n + 1))])
  have hsmooth : ContDiff ℝ ∞ a := extendedInitialScalar_contDiff zCell hL initial
    (hinitial.mono (ball_subset_ball (by linarith)))
  refine ⟨hsmooth, Complex.ofRealCLM.contDiff.comp hsmooth,
    extendedInitialScalar_hasCompactSupport zCell hL initial, ?_⟩
  intro s H hH p i hi
  have hHone : 1 ≤ H := le_trans (le_add_of_nonneg_right (cNorm_nonneg ..)) hH
  have hhigh : 1 + cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
      (s + 2 * (n + 1)) initial ≤ (1 + C (s + 2 * (n + 1))) * H := by
    have hvhigh : 1 + cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
        (s + 2 * (n + 1)) (densityOnInitialLabels v) ≤ H :=
      (add_le_add (le_refl (1 : ℝ)) (cNorm_mono_order (by omega))).trans hH
    have hb := (hnorm (s + 2 * (n + 1))).trans
      (mul_le_mul_of_nonneg_left hvhigh (hC _).le)
    nlinarith
  have hb := hprofile s initial hinitial hlo ((1 + C (s + 2 * (n + 1))) * H) hhigh p i hi
  rw [Real.mul_rpow (hfactor s).le (zero_le_one.trans hHone)] at hb
  exact hb.trans_eq (by dsimp [A]; ring)

open ContinuumAdjoint.DerivativeKernels ContinuumAdjoint.Canonical.PhaseExtension
open CanonicalCarrier CanonicalConic


/-- The supported scalar decomposition preserves the original carrier kernel
(`app:ch_background:eq:bg-T`, `app:ch_background:prop:bg-adjoint`). -/
private theorem corrected_carrier_scalarTransportData_kernel
    {n N : ℕ} (d : CarrierData n N)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hpoint : d.chartPoint = AmplitudeBound.centeredTorusRepresentative)
    (hmeasure : d.measurementCutoff = FixedCutoffs.periodic hr hcell 1)
    (zRoot : Euclidean 3) (θ : Euclidean (n - 1)) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hra : r ≤ a)
    (hangular : d.angularCutoff = angularMask zRoot θ ha hb)
    (zCell : Euclidean 3) {L : ℝ} (hL : 0 < L)
    (hlabel : ∀ p ∈ closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport zRoot (r := a),
      (d.transportedPosition p.1 p.2, parameter p.2) ∈
        ball ((0 : Euclidean (n - 1)), zCell) (L / 16))
    (Yext : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (hYext : EqOn Yext (fun p ↦ d.transportedPosition p.1 p.2)
      (closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport zRoot (r := a)))
    (v : CarrierVariable n → ℝ) :
    let scalar := extendedInitialScalar zCell hL
      (fun q ↦ positiveDensityAmplitude 1 (densityOnInitialLabels v q))
    let ν := fun p : AdjointJetPoint n ↦ chartBump zRoot ha (p.2, p.1) • d.normalField p.2 p.1
    carrierKernel (scalarTransportData d Yext scalar (fun _ ↦ 1) ν) =
      carrierKernel (correctedCarrierData d v) := by
  intro scalar ν
  apply carrierKernel_scalarTransportData_eq (correctedCarrierData d v) Yext scalar (fun _ ↦ 1) ν
  intro x _hx hm z θ' hθ
  have hm' : FixedCutoffs.periodic hr hcell 1 x ≠ 0 := by
    change d.measurementCutoff x ≠ 0 at hm
    rwa [hmeasure] at hm
  have hθ' : angularMask zRoot θ ha hb z θ' ≠ 0 := by
    change d.angularCutoff z θ' ≠ 0 at hθ
    rwa [hangular] at hθ
  obtain ⟨hz, ht, _⟩ := angularMask_nonzero zRoot θ ha hb hθ'
  have hx : d.chartPoint x ∈ closedBall (0 : Euclidean n) (4 * r) := by
    rw [hpoint]
    exact FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hm')
  have hp : (d.chartPoint x, z) ∈
      closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport zRoot (r := a) :=
    ⟨hx, ball_subset_closedBall hz, ball_subset_closedBall ht⟩
  refine ⟨hYext hp, ?_⟩
  have hbump : chartBump zRoot ha (d.chartPoint x, z) = (1 : ℝ) :=
    (chartBump_eventuallyEq_one (n := n) zRoot ha (p := (d.chartPoint x, z))
      ⟨closedBall_subset_closedBall (by linarith : 4 * r ≤ 4 * a) hx,
        ball_subset_closedBall hz, ball_subset_closedBall ht⟩).eq_of_nhds
  have hscalar : scalar (z, d.transportedPosition (d.chartPoint x) z) =
      Real.sqrt (1 + v (z, d.transportedPosition (d.chartPoint x) z)) := by
    have hh := (extendedInitialScalar_eventuallyEq zCell hL
      (fun q ↦ positiveDensityAmplitude 1 (densityOnInitialLabels v q))
      (p := (z, d.transportedPosition (d.chartPoint x) z)) (hlabel (d.chartPoint x, z) hp)).eq_of_nhds
    rw [initialScalar_positiveDensityAmplitude_labels] at hh
    simpa only [scalar, positiveDensityAmplitude, one_mul] using hh
  change (scalar (z, Yext (d.chartPoint x, z)) * 1) •
      (chartBump zRoot ha (d.chartPoint x, z) • d.normalField (d.chartPoint x) z) =
        Real.sqrt (1 + v (z, d.transportedPosition (d.chartPoint x) z)) •
          d.normalField (d.chartPoint x) z
  rw [hYext hp, hscalar, hbump, mul_one, one_smul]


open NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedLeading RetainedRowGeometry
open CurrentMean.PreparationTransportPrimitives ContinuumNormal.FrozenModel

/-- Realize the SAME corrected normalized seed carrier as the scalar-transport
kernel used by the raw-adjoint calculation. The original forward-flow bound
and source-dilation uniqueness put its actual inverse labels inside the fixed
`L/16` plateau; the Hamilton/ODE identity then identifies that label with the
transported position. No label-range or kernel-equality conclusion is assumed.
The test integral, adjoint integral and geometric amplitude component retain
the supplied measurement and angular masks, phase extension and unit normal.
The incidence center and original scalar center remain distinct
(`app:ch_background:eq:bg-T`, `app:ch_background:prop:bg-adjoint`,
`app:ch_background:prop:bg-normalized`).

Consumer: the literal kernel and scalar decomposition of the uniform
scalar-transport raw-adjoint endpoint for `CorrectedSourceInverse.hwide`.
The supplied phase extension comes from the original normalized adjoint
selection. Its analytic profiles and the normal-coordinate inputs must be
applied on these SAME masks; this identity does not construct that operator. -/
theorem retained_source_corrected_scalarTransportData_kernel_and_integrals
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
    {L Mc : ℝ} (hL : 0 < L) (hMc : 0 < Mc)
    (hforward : cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8))
      1 seed.forward ≤ Mc)
    {R : ℝ} (hRtime : R ≤ L / (64 * Mc)) (V : Set CarrierParameter)
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (current : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc M τ row col (sourceDilation F σ))
    (hrankσ : HasFullNormalRankOn (sourceDilation F σ) U)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (zRoot : Euclidean 3) (θ : Euclidean (n - 1)) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hra : r ≤ a) (high : ℝ → ℝ)
    (hsupport : closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport zRoot (r := a) ⊆
      ball (0 : Euclidean n) R ×ˢ V)
    (Yext : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (hYext : EqOn Yext (transportPosition T current.Q)
      (closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport zRoot (r := a)))
    (v : CarrierVariable n → ℝ) (hv : ∀ p, 0 ≤ 1 + v p) :
    let angular := angularMask zRoot θ ha hb
    let d := data T current.Q (sourceDilation F σ) row col current.forward current.inverse
      (fun _ ↦ σ) hr hcell angular high
    let unit := normalizedCarrierData T seed.Q F row col seed.forward seed.inverse
      (fun _ ↦ 1) hr hcell angular high σ
    let scalar := extendedInitialScalar zCell hL
      (fun q ↦ positiveDensityAmplitude 1 (densityOnInitialLabels v q))
    let ν := fun p : AdjointJetPoint n ↦ chartBump zRoot ha (p.2, p.1) • d.normalField p.2 p.1
    let extended := scalarTransportData d Yext scalar (fun _ ↦ 1) ν
    carrierKernel extended = carrierKernel (correctedCarrierData unit v) ∧
      carrierTestIntegral extended = carrierTestIntegral (correctedCarrierData unit v) ∧
      carrierAdjointIntegral extended = carrierAdjointIntegral (correctedCarrierData unit v) ∧
      ∀ j, carrierChartGeometryComponent extended (FixedCutoffs.physical hr 1) ν j =
        carrierChartGeometryComponent d (FixedCutoffs.physical hr 1) ν j := by
  intro angular d unit scalar ν extended
  have hpatch₂ : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius) := by
    intro p hp
    exact ⟨(hpatch hp).1.2, fun j ↦ ((hpatch hp).2 j).le.trans (by linarith only [hP.1])⟩
  obtain ⟨_, hfoot, _, _, _⟩ := retained_charts_source_dilation T hΩ hKΩ hpatch₂
    hRc hτ hτR hbuffer hF hrank hphysical seed htrans hflat hσ hσ1 current
  have hgeom : coordinates (adaptedCoordinates T.data.adapted) ⁻¹' current.D ⊆
      (ball 0 T.physicalRadius ∩ interior U) ×ˢ parameterInterior (3 * P.radius / 2) := by
    intro p hp
    have hpΩ : p ∈ Ω := by
      have hh := current.domain_coefficients hp
      simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hh
    exact ⟨⟨(hpatch hpΩ).1.2, by simpa only [hU.interior_eq] using (hpatch hpΩ).1.1⟩,
      (hpatch hpΩ).2⟩
  have hflowMeasured : MapsTo (densityCoordinates T)
      (closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport zRoot (r := a))
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ) := hflow.mono_left hsupport
  have hlabels : ∀ p ∈ closedBall (0 : Euclidean n) (4 * r) ×ˢ carrierSupport zRoot (r := a),
      (d.transportedPosition p.1 p.2, parameter p.2) ∈
        ball ((0 : Euclidean (n - 1)), zCell) (L / 16) := by
    intro p hp
    have hpD := current.small_subset ((outputCylinder_spec hRc hτ).2 (hflowMeasured hp))
    have he := retainedChart_footpoint_eq current hP (contDiff_sourceDilation hF).contDiffOn
      hrankσ (Subset.rfl : U ⊆ U) hτ hgeom (p := p) hpD
    change densityFootpoint T current.inverse p = (transportPosition T current.Q p, parameter p.2) at he
    change (transportPosition T current.Q p, parameter p.2) ∈ _
    rw [← he]
    have hmatch : densityFootpoint T current.inverse p =
        densityFootpoint T (SourceGeometry.sourceTransportFlow seed.inverse σ) p := hfoot hpD
    rw [hmatch]
    apply sourceDensityFootpoint_mem_original_ball_of_forward_cNorm T hL hRc hτ hMc
      seed hforward (hflowMeasured hp) (hlabel p (hsupport hp)) _ hσ hσ1
    change |(adaptedCoordinates T.data.adapted p.1).1| < L / (64 * Mc)
    rw [adaptedCoordinates_apply]
    have ht := abs_real_inner_le_norm T.data.adapted.normal p.1
    rw [T.data.adapted.normal_unit, one_mul] at ht
    exact (ht.trans_lt (mem_ball_zero_iff.mp (hsupport hp).1)).trans_le hRtime
  have hext : carrierKernel extended = carrierKernel (correctedCarrierData d v) :=
    corrected_carrier_scalarTransportData_kernel d hr hcell rfl rfl zRoot θ ha hb hra rfl
      zCell hL hlabels Yext hYext v
  have hcanonical := retained_positiveScalar_kernel_and_integrals current hP
    (contDiff_sourceDilation hF).contDiffOn hrankσ hτ hpatch hr hcell zRoot θ ha hb
    ((hflowMeasured.mono_right (outputCylinder_spec hRc hτ).2).mono_right current.small_subset) high σ v
  have hnormalized := retained_source_positiveScalar_kernel_and_integrals T hP hΩ hKΩ hpatch
    hRc hτ hτR hbuffer hF hrank hphysical seed htrans hflat hσ hσ1 current hrankσ hr hcell
    zRoot θ ha hb hflowMeasured high v hv
  have hkernel : carrierKernel extended = carrierKernel (correctedCarrierData unit v) :=
    hext.trans (hcanonical.1.symm.trans hnormalized.1)
  exact ⟨hkernel, carrierTestIntegral_congr_kernel hkernel,
    carrierAdjointIntegral_congr_kernel hkernel, fun _ ↦ rfl⟩

end JanetCartan.NormalizedBackground
