module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.SeedIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedPhase

/-!
# The literal fields of a supplied retained chart

These fields use the unit scalar and selected column of the supplied chart.
The consumer is `RetainedChartMean.exists_normalized_mean_bounds`, for
`app:ch_background:eq:bg-Nsigma` and `app:ch_background:prop:bg-normalized`.
The product inclusions are relative geometric inputs: the retained chart/row
geometry must cover the original carrier supports when the parent instantiates
this deduction. No transport solution, minor, or support is selected here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open PositiveReference PositiveReference.FlowConstruction ContinuumRow CanonicalCarrier
open NormalizedBackground NormalizedBackground.SourceGeometry HamiltonPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU} {Ω K : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}

/-- The actual Hamilton covector in the original carrier variables
(`app:ch_background:eq:bg-Nsigma`). -/
def covector (c : Chart T Ω K p₀ Rc B τ row col F) :
    Euclidean n × CarrierParameter → Euclidean n :=
  fun p ↦ T.carrierGradient c.Q p.1 (parameter p.2)

/-- The unit scalar of this retained flow times its selected null column
(`app:ch_background:eq:bg-Nsigma`). -/
def unitAmplitude (c : Chart T Ω K p₀ Rc B τ row col F) :
    Euclidean n × CarrierParameter → Euclidean n :=
  fun p ↦ c.scalar (fun _ ↦ 1) (p.1, parameter p.2) •
    carrierNullvector T c.Q col (p.1, parameter p.2)

/-- The normal used in the mean is literally the chart's canonical normal
(`app:ch_background:eq:bg-Hsigma`). -/
theorem unit_normal_eq (c : Chart T Ω K p₀ Rc B τ row col F) :
    c.normal (fun _ ↦ 1) = fun p ↦ LeadingWave.principalNormal
      (AmbientResponse.canonicalNormalCompletion F p.1) (covector c p) (unitAmplitude c p) := rfl

/-- Smoothness, nonzero covector/amplitude and the pencil-null identity follow
from this chart's scalar theorem and Hamilton domain. The only additional
inputs locate the product domain in the retained flow and Hamilton patch
(`app:ch_background:prop:bg-normalized`). -/
theorem seed_fields_properties (c : Chart T Ω K p₀ Rc B τ row col F)
    {cP CP : ℝ} (hP : P.IsValid cP CP) (hτ : 0 < τ)
    {U₀ : Set (Euclidean n)} {V : Set CarrierParameter}
    (hflow : MapsTo (densityCoordinates T) (U₀ ×ˢ V) c.D)
    (hpatch : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (U₀ ×ˢ V) (ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius))) :
    ContDiffOn ℝ ∞ (covector c) (U₀ ×ˢ V) ∧
    ContDiffOn ℝ ∞ (unitAmplitude c) (U₀ ×ˢ V) ∧
    ∀ p ∈ U₀ ×ˢ V,
      pencil (ProjectedStressFrame.projectedStress F p.1) (covector c p) *ᵥ
        (fun j ↦ unitAmplitude c p j) = 0 ∧
      covector c p ≠ 0 ∧ unitAmplitude c p ≠ 0 := by
  have hs := c.scalar_spec hτ (fun _ ↦ 1) contDiffOn_const (fun _ _ ↦ zero_lt_one)
  have hm : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      (p.1, parameter p.2)) := contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  have hξ := (T.carrierGradient_smooth hP c.Q).comp hm.contDiffOn hpatch
  have hflow' : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (U₀ ×ˢ V) (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c.D) := hflow
  have hb := hs.2.1.comp hm.contDiffOn hflow'
  refine ⟨hξ, hb, ?_⟩
  intro p hp
  have hf := hflow hp
  have hΩp : (p.1, parameter p.2) ∈ Ω := by
    have hh := c.domain_coefficients hf
    change (coordinates (adaptedCoordinates T.data.adapted)).symm
      (coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) ∈ Ω at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  refine ⟨?_, retained_carrierGradient_ne_zero T c.Q (hpatch hp).1 (hpatch hp).2,
    smul_ne_zero (ne_of_gt (hs.2.2.2.1 _ hf)) (c.null_spec _ hΩp).1⟩
  change pencil (ProjectedStressFrame.projectedStress F p.1)
    (T.carrierGradient c.Q p.1 (parameter p.2)) *ᵥ _ = 0
  rw [← c.frame_eq]
  exact hs.2.2.2.2.2.2.1 _ hf

/-- The actual positive-scale chart has the normalized seed normal and
covector on its full retained domain. This reuses the SAME-minor source-flow
uniqueness theorem (`app:ch_background:eq:bg-Nsigma`). -/
theorem current_fields_eq_normalized
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {z₀ : Euclidean 3} {ρ : ℝ}
    (hKΩ : closedBall ((0 : Euclidean n), z₀) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc)
      (closedBall ((0 : Euclidean n), z₀) ρ))
    (hF : ContDiff ℝ ∞ F) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
      ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (cσ : Chart T Ω (closedBall ((0 : Euclidean n), z₀) ρ)
      ((0 : Euclidean (n - 1)), z₀) Rc B τ row col (sourceDilation F σ)) :
    EqOn (cσ.normal (fun _ ↦ σ))
      (fun p ↦ normalizedPullback (c₀.normal (fun _ ↦ 1)) (σ, p))
      (densityCoordinates T ⁻¹' cσ.D) ∧
    EqOn (covector cσ) (fun p ↦ normalizedPullback (covector c₀) (σ, p))
      (densityCoordinates T ⁻¹' cσ.D) := by
  obtain ⟨_, _, _, _, hn⟩ := RetainedLeading.retained_charts_source_dilation T
    hΩ hKΩ hpatch hRc hτ hτR hbuffer hF hrank hphysical c₀ htrans hflat hσ hσ1 cσ
  constructor
  · intro p hp
    exact (hn (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1) p hp).symm
  · intro p hp
    have hh := cσ.domain_coefficients hp
    have hΩp : (p.1, parameter p.2) ∈ Ω := by
      change (coordinates (adaptedCoordinates T.data.adapted)).symm
        (coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) ∈ Ω at hh
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
    exact SourceMatching.current_carrierGradient_source_dilation T c₀.Q cσ.Q hF hrank
      hphysical c₀.frame_eq htrans hσ hσ1 cσ.frame_eq (hpatch hΩp).1 (hpatch hΩp).2

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
