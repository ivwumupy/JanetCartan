module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.NormalizedSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.SourceSobolev

/-!
# Sobolev smallness of the actual normalized reference source

The inverse input in `app:ch_background:eq:bg-current-raising` is constructed
from the literal projected stress, flat tangent strain and normalized carrier
mean. The geometric source theorem proves its smoothness and physical `O_s(ρ)`
bounds; periodization gives a single L² representative in every actual Sobolev
level, with `O_s(ρ)` norms. The seed fields and weights are unchanged, so this
leaf applies to the retained normalized/history seed. Actual instantiation of
that seed and of the SAME continuum row remains with the final assembly.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PositiveBackground
open NormalizedBackground ProjectedStressFrame UniformStep.Periodization

variable {n N : ℕ}

/-- The literal normalized residual produces an actual all-Sobolev source of
size `O_s(ρ)`. The positive source interval is chosen before the order, and the
SAME L² element works at every order. Source smallness, periodic smoothness and
Sobolev membership are conclusions, not analytic premises
(`app:ch_background:eq:bg-current-raising`, `app:ch_background:eq:bg-positive-profile`). -/
theorem exists_normalized_referenceSource_sobolev_bounds
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
    {r : ℝ} (hr : 0 < r) (hcell : r < 1 / 2)
    {θ : Euclidean n → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hsupp : tsupport θ ⊆ closedBall 0 r) :
    let e := fun ρ ↦ cutReducedSource θ (projectedStress (sourceDilation F ρ))
      (referenceMeanResidual (sourceDilation F ρ)
        (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ))
    ∃ ρ₀ > 0, ρ₀ ≤ 1 ∧
      (∀ ρ ∈ Ioc (0 : ℝ) ρ₀, ContDiff ℝ ∞ (e ρ) ∧ HasCompactSupport (e ρ) ∧
        tsupport (e ρ) ⊆ tsupport θ) ∧
      ∃ hep : ∀ ρ ∈ Ioc (0 : ℝ) ρ₀, IsSmoothPeriodic (vectorPeriodization (e ρ)),
        (∀ (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) ρ₀) (s : ℕ),
          sourceToL2 (e ρ) (hep ρ hρ) ∈ periodicSobolevLevel n (Euclidean n) s) ∧
        (∀ s : ℕ, ∃ C > 0, ∀ (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) ρ₀),
          (periodicSobolevScale n (Euclidean n)).gradeNorm s
            (sourceToL2 (e ρ) (hep ρ hρ)) ≤ C * ρ) ∧
        (∀ ρ ∈ Ioc (0 : ℝ) ρ₀, ∀ x ∈ fundamentalCell n,
          periodicLift (vectorPeriodization (e ρ)) =ᶠ[nhds x] e ρ) := by
  let e := fun ρ ↦ cutReducedSource θ (projectedStress (sourceDilation F ρ))
    (referenceMeanResidual (sourceDilation F ρ)
      (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ))
  obtain ⟨ρ₀, hρ₀, hρ₀1, hsmooth, hbound⟩ :=
    exists_normalized_referenceSource_bounds hF hΩ h0 hflat hrank μ K V hV hK hKV
      w ν ξ hw hwpos hν hξ hwSupport hr hθ hsupp
  have hsupport (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) ρ₀) :
      tsupport (e ρ) ⊆ closedBall 0 r := (hsmooth ρ hρ).2.2.trans hsupp
  have hbox (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) ρ₀) :
      tsupport (e ρ) ⊆ {x | ∀ i, |x i| ≤ r} := by
    intro x hx i
    exact (PiLp.norm_apply_le x i).trans (mem_closedBall_zero_iff.mp (hsupport ρ hρ hx))
  have hep (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) ρ₀) :
      IsSmoothPeriodic (vectorPeriodization (e ρ)) :=
    isSmoothPeriodic_vectorPeriodization hcell (hbox ρ hρ) (hsmooth ρ hρ).1
  refine ⟨ρ₀, hρ₀, hρ₀1, hsmooth, hep,
    fun ρ hρ s ↦ sourceToL2_mem (e ρ) (hep ρ hρ) s, ?_, ?_⟩
  · intro s
    obtain ⟨C, hC, hCbound⟩ := hbound s
    let M := Real.sqrt (s.factorial : ℝ) * Real.sqrt (sobolevMultiindices n s).card
    have hM : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    refine ⟨M * C + 1, by positivity, fun ρ hρ ↦ ?_⟩
    calc
      _ ≤ M * cNorm (closedBall 0 r) s (e ρ) :=
        sourceToL2_gradeNorm_le hcell (hsmooth ρ hρ).1 (hsupport ρ hρ) (hep ρ hρ) s
      _ ≤ M * (C * ρ) := mul_le_mul_of_nonneg_left (hCbound ρ hρ) hM
      _ ≤ (M * C + 1) * ρ := by nlinarith [hρ.1]
  · exact fun ρ hρ _ hx ↦ vectorPeriodization_eventuallyEq hcell (hbox ρ hρ) hx

end JanetCartan.PositiveBackground
