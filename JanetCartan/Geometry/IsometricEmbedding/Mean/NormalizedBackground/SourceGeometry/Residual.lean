module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Mean
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Scaling
import Mathlib.Algebra.Order.Star.Real

/-!
# The flat source reference residual

The exact uncorrected residual in `app:ch_background:prop:bg-positive`, for the
same fixed mean as `app:ch_background:eq:bg-Hsigma`. The positive-background
owner must still construct and estimate the subsequent density correction.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

/-- The flat source dilation and the same frozen mean give exactly `Hρ-H₀`
on the physical core (`app:ch_background:prop:bg-positive`). -/
theorem referenceMeanResidual_sourceDilation {n N : ℕ}
    {F : Euclidean n → Euclidean N} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : ContDiff ℝ ∞ F) {Ω U : Set (Euclidean n)} (hU : IsOpen U)
    (hflat : ∀ x ∈ Ω, inducedMetric F x = 1)
    (hdom : MapsTo (fun x ↦ ρ • x) U Ω)
    {A Z T : Type} [Fintype A] [MeasurableSpace Z] [NormedAddCommGroup T]
    (μ : A → Measure Z) (w : A → Z → ℝ)
    (ν : A → Euclidean n × Z → T) (ξ : A → Euclidean n × Z → Euclidean n)
    (hw : ∀ a z, 0 ≤ w a z)
    (hi : ∀ a i j, MeasureTheory.Integrable (fun z ↦ w a z * ‖ν a (0, z)‖ ^ 2 *
      (ξ a (0, z) i * ξ a (0, z) j)) (μ a)) (x : Euclidean n) (hx : x ∈ U) :
    PositiveBackground.referenceMeanResidual (sourceDilation F ρ)
      (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ) x =
      normalizedCarrierMean μ w ν ξ ρ x - normalizedCarrierMean μ w ν ξ 0 x := by
  have hmetric (y : Euclidean n) (hy : y ∈ U) :
      inducedMetric (sourceDilation F ρ) y = 1 := by
    rw [inducedMetric_sourceDilation hρ (hF.differentiable (by simp) _)]
    exact hflat _ (hdom hy)
  have himm : IsImmersionOn (sourceDilation F ρ) U :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      hmetric
  rw [normalizedCarrierMean_zero]
  exact PositiveBackground.referenceMeanResidual_eq_sub hU
    (contDiff_sourceDilation hF).contDiffOn himm hmetric
    (carrierMean μ w ν ξ 0) (carrierMean_posSemidef μ w ν ξ 0 hw hi).isHermitian.isSymm
    (normalizedCarrierMean μ w ν ξ ρ) hx

end JanetCartan.NormalizedBackground.SourceGeometry
