module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Source
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.StressScaling

/-!
# The actual flat-reference source

This connects the compact source to the SAME normalized mean and literal
projected stress of `sourceDilation F ρ` in `app:ch_background:prop:bg-positive`.
The seed fields may be those of the common normalized/history reference;
there is no new choice of seed, carrier measure, or source scale here.

This downstream leaf imports SourceGeometry, whose residual theorem imports
the base PositiveBackground module. It is therefore imported explicitly by
assemblers, rather than introducing an import cycle in that base module.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PositiveBackground
open NormalizedBackground NormalizedBackground.SourceGeometry ProjectedStressFrame

variable {n N : ℕ}

/-- The source formed from the literal scaled principal-normal mean is the
source formed from its normalized pullback, for the same phase, amplitude,
weights and original measure (`app:ch_background:eq:bg-current-raising`).
This applies SourceGeometry's actual normal/phase scaling, rather than
identifying two independently selected means. -/
theorem cutReducedSource_sourcePrincipalMean
    {F : Euclidean n → Euclidean N} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : ContDiff ℝ ∞ F) {Ω U : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (hrank : HasFullNormalRankOn F Ω) (hdom : MapsTo (fun x ↦ ρ • x) U Ω)
    {θ : Euclidean n → ℝ} (hsupp : tsupport θ ⊆ U)
    {A Z : Type} [Fintype A] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    (μ : A → Measure Z) (K V : A → Set Z) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (S : A → Euclidean n × Z → ℝ)
    (b : A → Euclidean n × Z → Euclidean n)
    (hwSupport : ∀ a z, z ∉ K a → w a z = 0)
    (hS : ∀ a, ContDiffOn ℝ ∞ (S a) (Ω ×ˢ V a)) (H₀ : MetricTensor n) :
    let ξ := fun a p ↦ gradient (fun y ↦ S a (y, p.2)) p.1
    let ν := fun a p ↦ LeadingWave.principalNormal
      (AmbientResponse.canonicalNormalCompletion F p.1) (ξ a p) (b a p)
    cutReducedSource θ (projectedStress (sourceDilation F ρ))
      (referenceMeanResidual (sourceDilation F ρ) H₀ (sourcePrincipalMean F μ w S b ρ)) =
    cutReducedSource θ (projectedStress (sourceDilation F ρ))
      (referenceMeanResidual (sourceDilation F ρ) H₀ (normalizedCarrierMean μ w ν ξ ρ)) := by
  dsimp only
  funext x
  by_cases hx : θ x = 0
  · simp [cutReducedSource, hx]
  · have he := sourcePrincipalMean_eq_normalizedCarrierMean hΩ hF hrank μ K V hKV
      w S b hwSupport hS hρ (hdom (hsupp (subset_tsupport θ hx)))
    simp only [cutReducedSource, referenceMeanResidual, Pi.add_apply, he]

/-- Exact identification of the compact source with the normalized mean
difference, using the actual projected-stress scaling and flat tangent strain
(`app:ch_background:eq:bg-current-raising`). Equality holds globally because
the fixed source cutoff vanishes outside the common geometric domain. -/
theorem cutReducedSource_referenceMeanResidual_sourceDilation
    {F : Euclidean n → Euclidean N} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : ContDiff ℝ ∞ F) {Ω U : Set (Euclidean n)} (hU : IsOpen U)
    (hflat : ∀ x ∈ Ω, inducedMetric F x = 1) (hrank : HasFullNormalRankOn F Ω)
    (hdom : MapsTo (fun x ↦ ρ • x) U Ω)
    {θ : Euclidean n → ℝ} (hsupp : tsupport θ ⊆ U)
    {A Z T : Type} [Fintype A] [MeasurableSpace Z] [NormedAddCommGroup T]
    (μ : A → Measure Z) (w : A → Z → ℝ)
    (ν : A → Euclidean n × Z → T) (ξ : A → Euclidean n × Z → Euclidean n)
    (hw : ∀ a z, 0 ≤ w a z)
    (hi : ∀ a i j, Integrable (fun z ↦ w a z * ‖ν a (0, z)‖ ^ 2 *
      (ξ a (0, z) i * ξ a (0, z) j)) (μ a)) :
    cutReducedSource θ (projectedStress (sourceDilation F ρ))
      (referenceMeanResidual (sourceDilation F ρ)
        (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ)) =
    cutReducedSource θ (fun x ↦ projectedStress F (ρ • x))
      (fun x ↦ normalizedCarrierMean μ w ν ξ ρ x - normalizedCarrierMean μ w ν ξ 0 x) := by
  funext x
  by_cases hx : θ x = 0
  · simp [cutReducedSource, hx]
  · have hxU := hsupp (subset_tsupport θ hx)
    have hres := referenceMeanResidual_sourceDilation hρ hF hU hflat hdom
      μ w ν ξ hw hi x hxU
    have hQ := funext (projectedStress_sourceDilation hρ hF x (hrank _ (hdom hxU)))
    simp only [cutReducedSource, hres, hQ]

/-- Construct the smooth compact source and its all-order `O(ρ)` bounds for
the actual flat-reference residual, not an assumed small source
(`app:ch_background:prop:bg-positive`, `app:ch_background:eq:bg-positive-profile`).
The source uses the same original carrier measure as the normalized mean.
Its common positive scale interval is chosen before the derivative order.
The seed normal/covector fields remain those supplied by SourceGeometry;
the continuum inverse and density estimates are subsequent obligations. -/
theorem exists_normalized_referenceSource_bounds
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω) (h0 : (0 : Euclidean n) ∈ Ω)
    (hflat : ∀ x ∈ Ω, inducedMetric F x = 1) (hrank : HasFullNormalRankOn F Ω)
    {A Z T : Type} [Fintype A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    (μ : A → Measure Z) (K V : A → Set Z)
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a)) (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (ν : A → Euclidean n × Z → T)
    (ξ : A → Euclidean n × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a)) (hwpos : ∀ a z, 0 ≤ w a z)
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (Ω ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (Ω ×ˢ V a))
    (hwSupport : ∀ a z, z ∉ K a → w a z = 0)
    {r : ℝ} (hr : 0 < r) {θ : Euclidean n → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hsupp : tsupport θ ⊆ closedBall 0 r) :
    let e := fun ρ ↦ cutReducedSource θ (projectedStress (sourceDilation F ρ))
      (referenceMeanResidual (sourceDilation F ρ)
        (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ))
    ∃ ρ₀ > 0, ρ₀ ≤ 1 ∧
      (∀ ρ ∈ Ioc (0 : ℝ) ρ₀, ContDiff ℝ ∞ (e ρ) ∧ HasCompactSupport (e ρ) ∧
        tsupport (e ρ) ⊆ tsupport θ) ∧
      ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Ioc (0 : ℝ) ρ₀,
        cNorm (closedBall 0 r) s (e ρ) ≤ C * ρ := by
  dsimp only
  have himm : IsImmersionOn F Ω :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one) hflat
  have hQ : ContDiffOn ℝ ∞ (projectedStress F) Ω :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hΩ hF.contDiffOn himm hrank)
  obtain ⟨ρ₀, hρ₀, hρ₀1, hsmooth, hbound⟩ :=
    exists_normalized_cutReducedSource_bounds μ K V hΩ h0 hV hK hKV w ν ξ
      hw hν hξ hwSupport hQ hr hθ hsupp
  have hint := integrable_carrierMean_entries_of_weight_support μ K V hK hKV
    w ν ξ hw hν hξ hwSupport h0
  have heq (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) ρ₀) :
      cutReducedSource θ (projectedStress (sourceDilation F ρ))
        (referenceMeanResidual (sourceDilation F ρ)
          (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ)) =
      cutReducedSource θ (fun x ↦ projectedStress F (ρ • x))
        (fun x ↦ normalizedCarrierMean μ w ν ξ ρ x - normalizedCarrierMean μ w ν ξ 0 x) := by
    have hopen : IsOpen ((fun x : Euclidean n ↦ ρ • x) ⁻¹' Ω) :=
      hΩ.preimage (continuous_id.const_smul ρ)
    exact cutReducedSource_referenceMeanResidual_sourceDilation hρ.1 hF hopen hflat hrank
      (fun _ hx ↦ hx) (fun x hx ↦ (hsmooth ρ ⟨hρ.1.le, hρ.2⟩).1 (hsupp hx))
      μ w ν ξ hwpos hint
  refine ⟨ρ₀, hρ₀, hρ₀1, ?_, ?_⟩
  · intro ρ hρ
    have hs := cutReducedSource_tsupport θ (projectedStress (sourceDilation F ρ))
      (referenceMeanResidual (sourceDilation F ρ)
        (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ))
    refine ⟨?_, (isCompact_closedBall (0 : Euclidean n) r).of_isClosed_subset
      (isClosed_tsupport _) (hs.trans hsupp), hs⟩
    rw [heq ρ hρ]
    exact (hsmooth ρ ⟨hρ.1.le, hρ.2⟩).2
  · intro s
    obtain ⟨C, hC, hCbound⟩ := hbound s
    refine ⟨C, hC, fun ρ hρ ↦ ?_⟩
    rw [heq ρ hρ]
    exact hCbound ρ ⟨hρ.1.le, hρ.2⟩

end JanetCartan.PositiveBackground
