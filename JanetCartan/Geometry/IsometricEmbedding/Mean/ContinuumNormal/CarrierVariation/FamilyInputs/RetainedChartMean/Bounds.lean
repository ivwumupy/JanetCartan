module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean.Fields
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedGeometry

/-!
# Normalization bounds for the supplied finite retained seed charts

This instantiates the analytic mean theorem with the literal unit scalars and
selected columns. The consuming construction is the parent `FamilyInputs`
simultaneous source/row/mean assembly. Its retained chart/row geometry must
instantiate `hflow` and `hpatch` on product neighborhoods of the ORIGINAL
supports. These are domain inclusions, not scalar or normal estimates.
No independently selected `SeedMean` scalar is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
open ActualCarriers FrozenMenu CurrentFullPhase
open PositiveReference PositiveReference.FlowConstruction ContinuumRow CanonicalCarrier
open NormalizedBackground NormalizedBackground.SourceGeometry

/-- On the original compact supports, the supplied retained unit charts have
a smooth normalized extension, a uniform positive normal bound, a constant
positive-semidefinite limit mean, and the all-order `O(σ)` estimate of
`app:ch_background:eq:bg-Hsigma` and `app:ch_background:prop:bg-normalized`.
All analytic seed premises are discharged from the charts and flat reference.
Only their product-domain inclusions remain relative geometric inputs. -/
theorem exists_normalized_mean_bounds
    {n : ℕ} (hn : 5 ≤ n) {A : Type} [Fintype A] (G : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    {P : A → Patch n} {cP CP : ℝ} (hP : ∀ a, (P a).IsValid cP CP)
    {T : (a : A) → PatchQuantitativeFamily (P a) U hU}
    {Ω Kc : A → Set (Euclidean n × Euclidean 3)}
    {p₀ : A → Euclidean (n - 1) × Euclidean 3}
    {Rc M τ : A → ℝ} {row col : A → Fin n}
    (c₀ : (a : A) → Chart (T a) (Ω a) (Kc a) (p₀ a)
      (Rc a) (M a) (τ a) (row a) (col a) G.map)
    (hτ : ∀ a, 0 < τ a)
    {U₀ D : Set (Euclidean n)} (hU₀ : IsOpen U₀) (h0 : (0 : Euclidean n) ∈ U₀)
    (hU₀G : U₀ ⊆ G.domain.chart n) (hD : IsCompact D)
    (μ : A → Measure CarrierParameter) (K V : A → Set CarrierParameter)
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (hflow : ∀ a, MapsTo (densityCoordinates (T a)) (U₀ ×ˢ V a) (c₀ a).D)
    (hpatch : ∀ a, MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (U₀ ×ˢ V a) (Metric.ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius)))
    (w : A → CarrierParameter → ℝ)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a)) (hwpos : ∀ a z, 0 ≤ w a z)
    (hsupp : ∀ a z, z ∉ K a → w a z = 0) :
    let ν := fun a ↦ (c₀ a).normal (fun _ ↦ 1)
    let ξ := fun a ↦ covector (c₀ a)
    let J := fun a q ↦ (normalizedPullback (unitAmplitude (c₀ a)) q,
      normalizedPullback (ξ a) q, normalizedPullback (ν a) q)
    ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      (∀ σ ∈ Ioo (-2 * σ₀) (2 * σ₀), ∀ x ∈ B, ∀ t ∈ Ioo (-1 : ℝ) 2,
        (t * σ) • x ∈ U₀) ∧
      (∀ a, ContDiffOn ℝ ∞ (J a) (Ioo (-2 * σ₀) (2 * σ₀) ×ˢ B ×ˢ V a)) ∧
      (∃ c > 0, ∀ a, ∀ σ ∈ Icc (0 : ℝ) σ₀, ∀ x ∈ D, ∀ z ∈ K a,
        c ≤ ‖normalizedPullback (ν a) (σ, (x, z))‖) ∧
      (carrierMean μ w ν ξ 0).PosSemidef ∧
      (∀ x, normalizedCarrierMean μ w ν ξ 0 x = carrierMean μ w ν ξ 0) ∧
      (∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ x ∈ B,
        PositiveBackground.referenceMeanResidual (sourceDilation G.map σ)
          (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ σ) x =
          normalizedCarrierMean μ w ν ξ σ x - carrierMean μ w ν ξ 0) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ σ ∈ Icc (0 : ℝ) σ₀,
        cNorm D s (fun x ↦ normalizedCarrierMean μ w ν ξ σ x - carrierMean μ w ν ξ 0) ≤ C * σ ∧
        ∀ a x, x ∈ D → ∀ z ∈ K a, ‖iteratedFDeriv ℝ s (J a) (σ, (x, z))‖ ≤ C := by
  have hf (a : A) := seed_fields_properties (c₀ a) (hP a) (hτ a) (hflow a) (hpatch a)
  have hrank : HasFullNormalRankOn G.map U₀ := fun x hx ↦ G.fullNormalRank x (hU₀G hx)
  obtain ⟨B, hB, hDB, σ₀, hσ₀, hσ₀1, hseg, hJ, hlo, hpos, hres, hbound⟩ :=
    exists_common_source_geometry_bounds hU₀ h0 hD G.contDiff
      (fun x _ ↦ G.inducedMetric_eq_one x) hrank (flatReference_projectedStress_basis hn G)
      μ K V hV hK hKV w (fun a ↦ covector (c₀ a)) (fun a ↦ unitAmplitude (c₀ a))
      hw hwpos hsupp (fun a ↦ (hf a).1) (fun a ↦ (hf a).2.1)
      (fun a z hz ↦ ((hf a).2.2 (0, z) ⟨h0, hKV a hz⟩).1)
      (fun a z hz ↦ ((hf a).2.2 (0, z) ⟨h0, hKV a hz⟩).2.1)
      (fun a z hz ↦ ((hf a).2.2 (0, z) ⟨h0, hKV a hz⟩).2.2)
  refine ⟨B, hB, hDB, σ₀, hσ₀, hσ₀1, hseg, hJ, hlo, hpos,
    fun x ↦ normalizedCarrierMean_zero _ _ _ _ x, ?_, ?_⟩
  · intro σ hσ x hx
    simpa only [unit_normal_eq, normalizedCarrierMean_zero] using hres σ hσ x hx
  · intro s
    simpa only [unit_normal_eq, normalizedCarrierMean_zero] using hbound s

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
