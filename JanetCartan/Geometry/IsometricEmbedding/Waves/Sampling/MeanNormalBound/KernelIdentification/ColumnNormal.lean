module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.Reassembly
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Bochner normal of the actual Euclidean columns

The compact-kernel Fubini argument for `app:ch_waves:eq:sampling-prefix-normal`
uses an operator-valued integral of rank-one columns. This identity is proved
from the constructed forward kernel and its derived Hilbert adjoint. It is
used to disintegrate each reassembled wide band over the carrier slice.
-/

@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap InnerProductSpace

namespace JanetCartan.Sampling.MeanNormalBound
open SamplingKernelBounds

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {k : X → H}

omit [CompleteSpace H] in
/-- Square-integrable columns give an operator-norm integrable rank-one normal,
the Bochner prerequisite for `app:ch_waves:eq:sampling-prefix-normal`. -/
theorem integrable_rankOne_column (hk : MemLp k 2 μ) :
    Integrable (fun x ↦ rankOne ℂ (k x) (k x)) μ := by
  have hc : Continuous (fun v : H ↦ rankOne ℂ v v) :=
    isBoundedBilinearMap_smulRight.continuous.comp
      ((innerSL ℂ).continuous.prodMk continuous_id)
  apply (hk.integrable_norm_pow (by decide : 2 ≠ 0)).mono'
    (hc.comp_aestronglyMeasurable hk.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x ↦ by simp [pow_two])

/-- The actual normal is the integral of its column outer products. No normal
identity is an input to this deduction (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem kernelSynthesis_normal_eq_integral_rankOne [NormedSpace ℝ H]
    (hk : MemLp k 2 μ) :
    atomNormal (kernelSynthesis hk) = ∫ x, rankOne ℂ (k x) (k x) ∂μ := by
  ext1 v
  rw [atomNormal, comp_apply, kernelSynthesis_apply,
    integral_apply (integrable_rankOne_column hk) v]
  apply integral_congr_ae
  filter_upwards [kernelSynthesis_hasAdjointKernel hk v] with x hx
  simp only [hx, rankOne_apply]

end JanetCartan.Sampling.MeanNormalBound
