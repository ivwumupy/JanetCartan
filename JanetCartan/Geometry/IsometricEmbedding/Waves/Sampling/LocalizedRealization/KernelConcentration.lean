module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.LocalizedRealization.Concentration
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.KernelRealization

/-!
# Concentration of the original kernels from support-local band bounds

This connects `operatorBernstein_familyDeviation_of_support` to the original
refined input in `app:ch_waves:eq:sampling-all-prefixes`. The uniform squared
kernel bound supplies the trace estimate, and positivity reduces every prefix
mean to the largest mean. The source-scale realization consumes this result;
no successful sampling event is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace JanetCartan.Sampling
open SeparatedSampling Realization RawInputRealization RawInputPartition
open SamplingKernelBounds SamplingKernelBounds.Expectation

variable {n J p : ℕ}

/-- Bernstein for the unchanged grouped annular kernels, requiring the sharp
single-band bound only where the original patch weight is nonzero
(`app:ch_waves:eq:sampling-all-prefixes`). The original complex input retains
both real quadratures, and the output is the entire Hilbert space. The kernel
and largest-mean estimates discharge all remaining analytic Bernstein inputs.
The positive upper parameters still permit zero actual variance. -/
theorem operatorBernstein_refinedKernelPrefix_of_support
    {A : Type*} [Fintype A]
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (hn : 1 ≤ n) (L : ℕ) {ψ : A → Point → ℝ} {w : ℝ → ℝ}
    {B W h C_op R C t : ℝ} {P : A → ℝ}
    (hw : WindowBounds p w W) (hψ : ∀ a, PatchBounds (ψ a) B (P a))
    (hψc : ∀ a, Continuous (ψ a)) (hwc : Continuous w) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hC_op : 0 ≤ C_op)
    (hband : ∀ a (i : RefinedIndex J) c z,
      ψ a z ≠ 0 → ‖(D a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
    (hblock : ∀ a, (nodesPerBlock p : ℝ) * (h ^ 3 * (P a * W ^ 3)) *
      ((3 * C_op) * (2 : ℝ) ^ J) ≤ R)
    (hR : 0 < R) (hC : 0 < C)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) w h
      (fun c z ↦ refinedKernelPrefix (D a) J (c, z))‖ ≤ C)
    (ht : 0 < t) (hthreshold : R * C + R * t / 3 ≤ t ^ 2) :
    familyShiftLaw A p B h
      {ω | t < ‖familyDeviation p B ψ w h
        (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ω‖} ≤
      OperatorCompression.bernsteinTail R (R * C)
        (R * ((∑ a, ((D a).squaredKernelConstant * (1 + (2 : ℝ) ^ n)) *
          (countConstant p B * (P a * W ^ 3))) * ((2 : ℝ) ^ J) ^ n)) t := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  apply operatorBernstein_familyDeviation_of_support hw hψ hψc hwc hh _
    (fun a c ↦ (continuous_refinedKernelPrefix (D a) L).comp
      (continuous_const.prodMk continuous_id))
    (fun a c z ↦ isCompactOperator_refinedKernelPrefix (D a) L (c, z))
    (by positivity) (fun a c z hz ↦ norm_refinedKernelPrefix_sq_le (D a) L (c, z) hC_op
      (fun i ↦ hband a i c z hz)) hblock hR hC
    ((norm_refinedKernelPrefix_mean_le_full D L hw hψ hψc hwc).trans hmean) ?_ ht hthreshold
  intro m e he
  change (∑ k, diagonalCLM (e k) (∑ a, patchMeanNormal p B (ψ a) w h
    (fun c z ↦ refinedKernelPrefix (D a) L (c, z)))) ≤ _
  simp only [map_sum]
  rw [Finset.sum_comm, Finset.sum_mul]
  exact Finset.sum_le_sum fun a _ ↦
    refinedKernelPrefix_mean_diagonal_le (D a) hn L hw (hψ a) (hψc a) hwc hh hh₁ m e he

end JanetCartan.Sampling
