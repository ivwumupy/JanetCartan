module

public import JanetCartan.Iteration.PhysicalBackground.SourceBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.NormalizedSource

/-!
# Reference source baseline at the literal measurement cutoff

This is the pre-σ source producer used by task24.  It is the existing
normalized-reference estimate applied at the SAME principal-mean/reference
residual, then converted to the v2 measured source with cutoff index one and
factor two.  No frozen density is substituted for the current density, and no
new carrier, row, flow, or exterior is selected here.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace JanetCartan.PhysicalBackground
open ContinuumRow PositiveBackground NormalizedBackground NormalizedBackground.SourceGeometry
open ProjectedStressFrame

variable {n N : ℕ}

/-- The normalized reference residual supplies an all-order `O(ρ)` measured
source at the literal v2 measurement cutoff.  The smooth projected-frame and
mean fields are supplied by the SAME retained normalized-reference tuple; the
normalization theorem itself supplies the compact source profile. -/
theorem exists_normalized_reference_measuredSource_bounds
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω) (h0 : (0 : Euclidean n) ∈ Ω)
    (hflat : ∀ x ∈ Ω, inducedMetric F x = 1)
    (hrank : HasFullNormalRankOn F Ω)
    {A Z T : Type} [Fintype A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    (μ : A → Measure Z) (K V : A → Set Z)
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a))
    (hKV : ∀ a, K a ⊆ V a)
    (w : A → Z → ℝ) (ν : A → Euclidean n × Z → T)
    (ξ : A → Euclidean n × Z → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hwpos : ∀ a z, 0 ≤ w a z)
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (Ω ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (Ω ×ˢ V a))
    (hwSupport : ∀ a z, z ∉ K a → w a z = 0)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hQ : ∀ ρ, ρ ∈ Ioc (0 : ℝ) 1 →
      ContDiffOn ℝ ∞ (projectedStress (sourceDilation F ρ)) (ball 0 (4 * r)))
    (hR : ∀ ρ, ρ ∈ Ioc (0 : ℝ) 1 →
      ContDiffOn ℝ ∞
        (referenceMeanResidual (sourceDilation F ρ)
          (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ))
        (ball 0 (4 * r))) :
    ∃ ρ₀ > (0 : ℝ), ρ₀ ≤ 1 ∧
      ∀ s : ℕ, ∃ C > (0 : ℝ),
        ∀ (ρ : ℝ) (_hρ : ρ ∈ Ioc (0 : ℝ) ρ₀)
          (hρ1 : ρ ∈ Ioc (0 : ℝ) 1),
          (periodicSobolevScale n (Euclidean n)).gradeNorm s
            (measuredSourceToL2 hr hcell
              (projectedStress (sourceDilation F ρ))
              (referenceMeanResidual (sourceDilation F ρ)
                (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ))
              (hQ ρ hρ1) (hR ρ hρ1)) ≤ C * ρ := by
  have hr4 : 0 < 4 * r := by positivity
  have hθ : ContDiff ℝ ∞ (FixedCutoffs.physical (n := n) hr 1) :=
    (FixedCutoffs.physical hr 1).contDiff
  have hsupp4 : tsupport (FixedCutoffs.physical (n := n) hr 1) ⊆
      closedBall (0 : Euclidean n) (4 * r) :=
    FixedCutoffs.physical_tsupport_four hr 1
  obtain ⟨ρ₀, hρ₀, hρ₀1, _hsmooth, hbound⟩ :=
    exists_normalized_referenceSource_bounds hF hΩ h0 hflat hrank μ K V hV hK hKV
      w ν ξ hw hwpos hν hξ hwSupport hr4 hθ hsupp4
  refine ⟨ρ₀, hρ₀, hρ₀1, ?_⟩
  intro s
  obtain ⟨C, hC, hCb⟩ := hbound s
  let M := 2 * Real.sqrt (s.factorial : ℝ) * Real.sqrt (sobolevMultiindices n s).card
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨1 + M * C, by positivity, ?_⟩
  intro ρ hρ hρ1
  have hm := measuredSourceToL2_gradeNorm_le hr hcell
    (projectedStress (sourceDilation F ρ))
    (referenceMeanResidual (sourceDilation F ρ)
      (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ))
    (hQ ρ hρ1) (hR ρ hρ1) s
  calc
    _ ≤ M * cNorm (closedBall 0 (4 * r)) s
        (cutReducedSource (FixedCutoffs.physical hr 1)
          (projectedStress (sourceDilation F ρ))
          (referenceMeanResidual (sourceDilation F ρ)
            (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ))) := hm
    _ ≤ M * (C * ρ) := by
      exact mul_le_mul_of_nonneg_left (hCb ρ hρ) hM
    _ = (M * C) * ρ := by ring
    _ ≤ (1 + M * C) * ρ := by
      have hMC : 0 ≤ M * C := mul_nonneg hM (le_of_lt hC)
      have hstep : M * C ≤ 1 + M * C := by linarith
      exact mul_le_mul_of_nonneg_right hstep (le_of_lt hρ.1)

end JanetCartan.PhysicalBackground
