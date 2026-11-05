module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.NormalizedSourceSobolev

/-!
# The compact source of the supplied retained mean

Construct the source in `app:ch_background:eq:bg-current-raising` from the
literal current charts supplied by `FamilyInputs.InitializedSourceCharts`.
The seed and current charts, selected minors, external weights and carrier
measures are the same throughout. In the positive-background application,
`μ a = volume.prod volume` and `w a = χ a ^ 2`; the already proved
`PositiveBackground.CarrierMeasure` coordinate change relates these labels
to Euclidean three-dimensional Lebesgue measure.

`RetainedChartMean.exists_current_mean_bounds` supplies the field and mean
identities. Normal smoothness is derived from the seed chart and its canonical
normal completion. `PositiveBackground.exists_normalized_referenceSource_sobolev_bounds`
then supplies one compact smooth source, with one L² representative in all
Sobolev levels, on an interval fixed before all orders.

The only relative geometric inputs are the stated product-domain inclusions
`hflow₀` and `hflowσ`, with an open physical neighborhood `W` containing `D`.
Their producer is `jc-family-retained-row-support-geometry`. Original weights
and their detector plateaux come from `ExternalWeights`; original physical
cutoffs supply `hθ`, `hθD` and `hθsupport`. The positive-background parent must
instantiate these inputs on the same family before applying
`PositiveBackground.exists_small_uncorrectedDensity_of_normal_estimates`.
This deduction does not select another seed cover or prove that parent theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.RetainedAssembly.NormalizedMeanSource

open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction ContinuumRow CanonicalCarrier
open NormalizedBackground NormalizedBackground.SourceGeometry HamiltonPhase
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
open PositiveBackground ProjectedStressFrame UniformStep.Periodization

/-- The actual supplied retained mean gives the literal compact inverse source
of `app:ch_background:eq:bg-current-raising`. Its field identities hold on an
open neighborhood of the entire cutoff support, and its cut source equals the
normalized-pullback source globally. A single positive interval precedes all
orders, and a single L² element has all Sobolev norms `O_s(σ)` as required by
`app:ch_background:eq:bg-positive-profile`. No mean-error or source estimate is
an input; the original fixed weights and measures are retained. -/
theorem exists_current_referenceSource_sobolev_bounds
    {n : ℕ} (hn : 5 ≤ n) {A : Type} [Fintype A] (G : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U} (hUG : U ⊆ G.domain.chart n)
    {P : A → Patch n} {cP CP : ℝ} (hP : ∀ a, (P a).IsValid cP CP)
    {T : (a : A) → PatchQuantitativeFamily (P a) U hU}
    {Ω : A → Set (Euclidean n × Euclidean 3)}
    (hΩ : ∀ a, IsOpen (Ω a))
    {z₀ : A → Euclidean 3} {ρ Rc M τ : A → ℝ} {row col : A → Fin n}
    (hKΩ : ∀ a, closedBall ((0 : Euclidean n), z₀ a) (ρ a) ⊆ Ω a)
    (hpatch : ∀ a, Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius))
    (hRc : ∀ a, 0 < Rc a) (hτ : ∀ a, 0 < τ a) (hτR : ∀ a, τ a ≤ Rc a / 16)
    (hbuffer : ∀ a, MapsTo (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀ a)) (Rc a))
      (closedBall ((0 : Euclidean n), z₀ a) (ρ a)))
    (hphysical : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ U)
    (c₀ : (a : A) → Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
      ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a) G.map)
    (htrans : ∀ a, ∀ q ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU (c₀ a).Q.1 (c₀ a).Q.2.1).hp q,
        (T a).data.adapted.normal⟫_ℝ ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) (hcap1 : cap ≤ 1)
    (cσ : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (a : A) →
      Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
        ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a)
        (sourceDilation G.map σ))
    {U₀ D W : Set (Euclidean n)} (hU₀ : IsOpen U₀) (h0 : (0 : Euclidean n) ∈ U₀)
    (hU₀G : U₀ ⊆ G.domain.chart n) (hD : IsCompact D) (hW : IsOpen W) (hDW : D ⊆ W)
    (μ : A → Measure CarrierParameter) (K V : A → Set CarrierParameter)
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (hflow₀ : ∀ a, MapsTo (densityCoordinates (T a)) (U₀ ×ˢ V a) (c₀ a).D)
    (hflowσ : ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) a,
      MapsTo (densityCoordinates (T a)) (W ×ˢ K a) (cσ σ hσ a).D)
    (w : A → CarrierParameter → ℝ)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a)) (hwpos : ∀ a z, 0 ≤ w a z)
    (hsupp : ∀ a z, z ∉ K a → w a z = 0)
    {r : ℝ} (hr : 0 < r) (hcell : r < 1 / 2)
    {θ : Euclidean n → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθD : tsupport θ ⊆ D) (hθsupport : tsupport θ ⊆ closedBall 0 r) :
    let ν := fun a ↦ (c₀ a).normal (fun _ ↦ 1)
    let ξ := fun a ↦ covector (c₀ a)
    let H := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ carrierMean μ w
      (fun a ↦ (cσ σ hσ a).normal (fun _ ↦ σ)) (fun a ↦ covector (cσ σ hσ a))
    let H₀ := carrierMean μ w ν ξ 0
    let e := fun σ hσ ↦ cutReducedSource θ (projectedStress (sourceDilation G.map σ))
      (referenceMeanResidual (sourceDilation G.map σ) H₀ (H σ hσ))
    ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ cap ∧
      H₀.PosSemidef ∧
      (∀ x, normalizedCarrierMean μ w ν ξ 0 x = H₀) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) a x, x ∈ B → ∀ z ∈ K a,
        (cσ σ hσ a).normal (fun _ ↦ σ) (x, z) = normalizedPullback (ν a) (σ, (x, z)) ∧
        covector (cσ σ hσ a) (x, z) = normalizedPullback (ξ a) (σ, (x, z))) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) x, x ∈ B →
        H σ hσ x = normalizedCarrierMean μ w ν ξ σ x ∧
        H σ hσ x = carrierMean μ w ν ξ (σ • x)) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap),
        EqOn (referenceMeanResidual (sourceDilation G.map σ) H₀ (H σ hσ))
          (fun x ↦ H σ hσ x - H₀) B) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), e σ hσ =
        cutReducedSource θ (projectedStress (sourceDilation G.map σ))
          (referenceMeanResidual (sourceDilation G.map σ) H₀
            (normalizedCarrierMean μ w ν ξ σ))) ∧
      (∀ s : ℕ, ∃ C > 0, ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ →
        cNorm D s (fun x ↦ H σ hσ x - H₀) ≤ C * σ) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ →
        ContDiff ℝ ∞ (e σ hσ) ∧ HasCompactSupport (e σ hσ) ∧
          tsupport (e σ hσ) ⊆ tsupport θ) ∧
      ∃ hep : ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ →
          IsSmoothPeriodic (vectorPeriodization (e σ hσ)),
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) (hsmall : σ ≤ σ₀) (s : ℕ),
          sourceToL2 (e σ hσ) (hep σ hσ hsmall) ∈ periodicSobolevLevel n (Euclidean n) s) ∧
        (∀ s : ℕ, ∃ C > 0, ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap) (hsmall : σ ≤ σ₀),
          (periodicSobolevScale n (Euclidean n)).gradeNorm s
            (sourceToL2 (e σ hσ) (hep σ hσ hsmall)) ≤ C * σ) ∧
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ → ∀ x ∈ fundamentalCell n,
          periodicLift (vectorPeriodization (e σ hσ)) =ᶠ[nhds x] e σ hσ) := by
  classical
  let ν := fun a ↦ (c₀ a).normal (fun _ ↦ 1)
  let ξ := fun a ↦ covector (c₀ a)
  let H := fun σ (hσ : σ ∈ Ioc (0 : ℝ) cap) ↦ carrierMean μ w
    (fun a ↦ (cσ σ hσ a).normal (fun _ ↦ σ)) (fun a ↦ covector (cσ σ hσ a))
  let H₀ := carrierMean μ w ν ξ 0
  let e := fun σ hσ ↦ cutReducedSource θ (projectedStress (sourceDilation G.map σ))
    (referenceMeanResidual (sourceDilation G.map σ) H₀ (H σ hσ))
  let en := fun σ ↦ cutReducedSource θ (projectedStress (sourceDilation G.map σ))
    (referenceMeanResidual (sourceDilation G.map σ) H₀ (normalizedCarrierMean μ w ν ξ σ))
  obtain ⟨B, hB, hDB, σ₁, hσ₁, hσ₁cap, _hJ, hpos, hzero, hfields, hmean, _hlo, hmeanBound⟩ :=
    exists_current_mean_bounds hn G hUG hP hΩ hKΩ hpatch hRc hτ hτR hbuffer hphysical
      c₀ htrans hcap hcap1 cσ hU₀ h0 hU₀G hD hW hDW μ K V hV hK hKV hflow₀ hflowσ
      w hw hwpos hsupp
  have hpatch₀ (a : A) : MapsTo
      (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (U₀ ×ˢ V a) (ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius)) := by
    intro p hp
    apply hpatch a
    have hh := (c₀ a).domain_coefficients (hflow₀ a hp)
    change (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (coordinates (adaptedCoordinates (T a).data.adapted) (p.1, parameter p.2)) ∈ Ω a at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  have hf (a : A) := seed_fields_properties (c₀ a) (hP a) (hτ a) (hflow₀ a) (hpatch₀ a)
  have hrank : HasFullNormalRankOn G.map U₀ := fun x hx ↦ G.fullNormalRank x (hU₀G hx)
  have himm : IsImmersionOn G.map U₀ := isImmersionOn_of_isIsometricOn
    (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ G.inducedMetric_eq_one x)
  have hν (a : A) : ContDiffOn ℝ ∞ (ν a) (U₀ ×ˢ V a) :=
    contDiffOn_canonicalPrincipalNormal hU₀ G.contDiff.contDiffOn himm hrank
      (fun _ hp ↦ hp.1) (hf a).1 (hf a).2.1
  obtain ⟨σ₂, hσ₂, _hσ₂1, hsmooth, hnp, _hmem, hbound, hjet⟩ :=
    exists_normalized_referenceSource_sobolev_bounds G.contDiff hU₀ h0
      (fun x _ ↦ G.inducedMetric_eq_one x) hrank μ K V hV hK hKV w ν ξ hw hwpos hν
      (fun a ↦ (hf a).1) hsupp hr hcell hθ hθsupport
  let σ₀ := min σ₁ σ₂
  have hsmall {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) cap) (hs : σ ≤ σ₀) :
      σ ∈ Ioc (0 : ℝ) σ₂ := ⟨hσ.1, hs.trans (min_le_right _ _)⟩
  have heq (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) : e σ hσ = en σ := by
    funext x
    by_cases hx : θ x = 0
    · simp [e, en, cutReducedSource, hx]
    · have hm := (hmean σ hσ x (hDB (hθD (subset_tsupport θ hx)))).1
      simp only [e, en, H, H₀, ν, ξ, cutReducedSource, referenceMeanResidual,
        Pi.add_apply, hm]
  have hep (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (hs : σ ≤ σ₀) :
      IsSmoothPeriodic (vectorPeriodization (e σ hσ)) := by
    rw [heq σ hσ]
    exact hnp σ (hsmall hσ hs)
  refine ⟨B, hB, hDB, σ₀, lt_min hσ₁ hσ₂, (min_le_left _ _).trans hσ₁cap,
    hpos, hzero, hfields, hmean, ?_, heq, ?_, ?_, hep,
    fun σ hσ hs s ↦ sourceToL2_mem (e σ hσ) (hep σ hσ hs) s, ?_, ?_⟩
  · intro σ hσ
    have hmetric (x : Euclidean n) (_hx : x ∈ B) :
        inducedMetric (sourceDilation G.map σ) x = 1 := by
      rw [inducedMetric_sourceDilation hσ.1 (G.contDiff.differentiable (by simp) _)]
      exact G.inducedMetric_eq_one _
    exact referenceMeanResidual_eq_sub hB (contDiff_sourceDilation G.contDiff).contDiffOn
      (isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1)
        (fun _ _ ↦ Matrix.PosDef.one) hmetric)
      hmetric H₀ hpos.isHermitian.isSymm (H σ hσ)
  · intro s
    obtain ⟨C, hC, hb⟩ := hmeanBound s
    exact ⟨C, hC, fun σ hσ hs ↦ (hb σ hσ (hs.trans (min_le_left _ _))).1⟩
  · intro σ hσ hs
    change ContDiff ℝ ∞ (e σ hσ) ∧ HasCompactSupport (e σ hσ) ∧
      tsupport (e σ hσ) ⊆ tsupport θ
    rw [heq σ hσ]
    exact hsmooth σ (hsmall hσ hs)
  · intro s
    obtain ⟨C, hC, hb⟩ := hbound s
    refine ⟨C, hC, fun σ hσ hs ↦ ?_⟩
    rw [sourceToL2_gradeNorm]
    change periodicSobolevNorm s (vectorPeriodization (e σ hσ)) ≤ _
    rw [heq σ hσ]
    simpa only [sourceToL2_gradeNorm] using hb σ (hsmall hσ hs)
  · intro σ hσ hs x hx
    change periodicLift (vectorPeriodization (e σ hσ)) =ᶠ[nhds x] e σ hσ
    rw [heq σ hσ]
    exact hjet σ (hsmall hσ hs) x hx

end JanetCartan.RetainedAssembly.NormalizedMeanSource
