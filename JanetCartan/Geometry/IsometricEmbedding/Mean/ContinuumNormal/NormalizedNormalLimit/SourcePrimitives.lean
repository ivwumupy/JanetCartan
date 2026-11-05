module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceCoefficientBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalSourceConicDensity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SliceCoordinates

/-!
# Concrete source limits for the normalized reflected-normal comparison

Apply the coefficient, conic-inverse/Jacobian and original-domain ODE-label
producers to the SAME supplied seed and inverse. The resulting primitive
error is independent of the density. Its derivative order is precisely the
PDO reserve `2 * (n + 1)`. No coefficient or inverse convergence is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity CarrierVariation.FamilyInputs.RetainedRowGeometry

/-- Instantiate the actual source-coefficient and transport limits, together
with both inverse-substituted ODE-label limits on the ORIGINAL `L/8` scalar
ball. The same fixed masks, field chart, compact conic target and genuine
inverse occur throughout. The error includes only primitive differences,
and tends to zero before any density is chosen. Absolute coefficient
controls and original-domain label ranges use one common cap.

Consumer: `exists_source_fullAmplitude_sqrtFootpoints_tolerance`, at the
exact reserve `μ = 2 * (n + 1)`. Sources:
`app:ch_background:prop:bg-normalized`, `bg-Nsigma`, `bg-Psi`, and
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_original_domain_source_primitive_limit
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
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
    (ha : ContDiffOn ℝ ∞ (fun p ↦ angular p.1 p.2) D.angular.region)
    (hh : ContDiffOn ℝ ∞ high D.high.region)
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hrange : ∀ p ∈ K, D.Contains p)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
        (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (normalizedTransportPosition T Q₀ σ)
        (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p)) :
    let μ := 2 * (n + 1)
    let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ)
      (FixedCutoffs.physical hr 1)
    let Z := normalizedTransportPosition T Q₀
    let J := fun σ ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) (Z σ)
    let g := fun σ side p ↦ sourceDensityFootpointExtension T Y
      (σ, densityEndpoint side (inverseCoordinates (u σ) p))
    let error := fun σ ↦
      cNorm D.field.carrier μ ((a σ).normal - (a 0).normal) +
      cNorm D.field.carrier μ ((a σ).reduced - (a 0).reduced) +
      (cNorm K μ (augmentedTransportGradient (Z σ) - augmentedTransportGradient (Z 0)) +
        cNorm Q μ (inverseCoordinates (u σ) - inverseCoordinates (u 0)) +
        cNorm K μ (J σ - J 0) +
        cNorm K μ ((fun p ↦ (J σ p)⁻¹) - (fun p ↦ (J 0 p)⁻¹))) +
      cNorm Q μ (g σ false - g 0 false) + cNorm Q μ (g σ true - g 0 true)
    Tendsto error (𝓝 0) (𝓝 0) ∧
      ∃ M > 0, ∃ cap > 0, cap ≤ 1 ∧ cap < e ∧
        D.Controls (μ + 1) M (M + 1) 1 (a 0) ∧
        ∀ σ ∈ Icc (0 : ℝ) cap,
          D.Controls μ M (M + 1) 1 (a σ) ∧
          ∀ side, (∀ p ∈ Q, ContDiffAt ℝ ∞ (g σ side) p) ∧
            MapsTo (g σ side) Q (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) := by
  let μ := 2 * (n + 1)
  obtain ⟨M, hM, sc, hsc, hsc1, hbase, hcoeff⟩ :=
    exists_normalizedCarrierData_coefficient_controls T Q₀ F row col Φ Y (fun _ ↦ 1)
      hr hcell angular high (FixedCutoffs.physical hr 1) hP hseed hF hi hrank
      hR hRT hRU hV hVP hb D hD (FixedCutoffs.physical hr 1).contDiff.contDiffOn ha hh μ
  obtain ⟨hn, hq⟩ := tendsto_normalizedCarrierData_coefficients_sub_cNorm
    T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high (FixedCutoffs.physical hr 1)
      hP hseed hF hi hrank hR hRT hRU hV hVP hb D
        (fun p hp ↦ (hD (D.field.ball_subset hp)).2) μ
  have hend (side : Bool) : MapsTo (densityEndpoint side) K (ball (0 : Euclidean n) R ×ˢ V) := by
    intro p hp
    apply hD
    apply D.field.ball_subset
    cases side
    · exact (hrange p hp).2.2.2.2.1
    · exact (hrange p hp).2.2.2.2.2
  obtain ⟨hg, sg, hsg, _, hlabels⟩ := exists_retained_source_conic_footpoint_primitives
    T hR hV hY hzero hparam hL hs₀ hsource hK hconv hW hKW hQ hΩ hQΩ hend A he hjoint
      (fun σ hσ ↦ ⟨(hfamily σ hσ).1, (hfamily σ hσ).2.1,
        (hfamily σ hσ).2.2.1, (hfamily σ hσ).2.2.2.1⟩)
  have hj := tendsto_conic_inverse_jacobian_sub_cNorm hK hconv hW hKW hQ hΩ hQΩ
    A (CanonicalConic.adaptedSliceCoordinates T) he hδ hjoint hfamily μ
  refine ⟨?_, M, hM, min sc (min sg (e / 2)),
    lt_min hsc (lt_min hsg (half_pos he)), (min_le_left _ _).trans hsc1,
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self he), hbase, ?_⟩
  · simpa only [add_zero] using (((hn.add hq).add hj).add (hg μ false)).add (hg μ true)
  · intro σ hσ
    exact ⟨hcoeff σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩,
      hlabels σ ⟨hσ.1, hσ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩⟩

/-- The divided ODE footpoint is smooth on the WHOLE supplied physical/carrier
product and keeps the original scalar range, including scale zero. Only the
source cap changes; no part of the detector domain is removed. The positive
range is the output of `exists_original_source_density_region`, and the zero
range follows from its already proved continuous extension.

Consumer: primitive regularity of the actual density-weighted full amplitude
in `exists_source_fullAmplitude_sqrtFootpoints_tolerance`. Sources:
`app:ch_background:eq:bg-Nsigma` and `app:ch_background:prop:bg-normalized`. -/
theorem source_footpoint_original_domain_regular
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
    ∀ σ ∈ Icc (0 : ℝ) (min s₀ (1 / 8)),
      ContDiffOn ℝ ∞ (fun p ↦ sourceDensityFootpointExtension T Y (σ, p)) (ball 0 R ×ˢ V) ∧
      MapsTo (fun p ↦ sourceDensityFootpointExtension T Y (σ, p)) (ball 0 R ×ˢ V)
        (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
  intro σ hσ
  have hσeight : σ ≤ 1 / 8 := hσ.2.trans (min_le_right _ _)
  have hσone : σ ≤ 1 := hσeight.trans (by norm_num)
  have hσI : σ ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) := by
    constructor <;> linarith [hσ.1]
  refine ⟨(sourceDensityFootpointExtension_contDiffOn T hV hY).comp
    (contDiffOn_const.prodMk contDiffOn_id) (fun p hp ↦ ⟨hσI, hp⟩), ?_⟩
  by_cases hσ0 : σ = 0
  · subst σ
    exact sourceDensityFootpointExtension_zero_mem_original_closedBall T hR hV hY
      hzero hparam Subset.rfl hs₀ hsource
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ.1 (Ne.symm hσ0)
    intro p hp
    change sourceDensityFootpointExtension T Y (σ, p) ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16)
    have hscaled : (σ • p.1, p.2) ∈ ball (0 : Euclidean n) R ×ˢ V := by
      exact ⟨(convex_ball (0 : Euclidean n) R).smul_mem_of_zero_mem
        (mem_ball_self hR) hp.1 ⟨hσ.1, hσone⟩, hp.2⟩
    rw [sourceDensityFootpointExtension_eq T hR hY hzero hparam hσ0 hscaled]
    exact ball_subset_closedBall (hsource σ ⟨hσpos, hσ.2.trans (min_le_left _ _)⟩ hp)

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
