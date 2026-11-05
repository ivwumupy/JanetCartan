module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.GroupedKernels.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization

/-! # Reassembly under the original compact colored weights

For `app:ch_waves:eq:sampling-prefix-normal`, the same colors, carrier measure,
window and physical kernels are retained. Integrability follows from the actual
kernel continuity and the original compact block windows.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.Sampling.ColoredNormalComparison
open RawInputPartition SamplingKernelBounds SeparatedSampling Realization BackgroundQuadrature

variable {n J p : ℕ}

/-- The grouped normal is integrable against each original colored carrier
weight. No operator-valued integrability premise is introduced
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_colored_wideKernelPrefix_normal
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    {ψ : Point → ℝ} {w : ℝ → ℝ} {W B h : ℝ}
    (hw : WindowBounds p w W) (hψ : Continuous ψ) (hwc : Continuous w) (hh : h ≠ 0)
    (L : ℕ) (c : Fin 3 → Fin (p + 1)) :
    Integrable (fun z : Point ↦
      coloredBlockMask p (integerCube (blockCutoff p B h)) w h c z •
        (ψ z • ∑ j ∈ Finset.univ.filter (fun j : Fin J ↦ j.val < L),
          atomNormal (wideKernelOperator D j.val (j, (c, z))))) := by
  classical
  simp_rw [← refinedKernelPrefix_normal_eq_wide]
  have hT := (continuous_refinedKernelPrefix D L).comp
    ((continuous_const (y := c)).prodMk (continuous_id (X := Point)))
  simp only [coloredBlockMask, Finset.sum_smul]
  exact integrable_finsetSum _ (fun q _ ↦ integrable_blockWeight_smul hw hwc hh q
    (hψ.smul (hT.clm_comp (ContinuousLinearMap.adjoint.continuous.comp hT))))

/-- Exact reassembly inside the manuscript's original colored carrier integral,
for every prefix of the same fixed ceiling
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem patchMeanNormal_refinedKernelPrefix_eq_wide
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    {ψ : Point → ℝ} {w : ℝ → ℝ} {W B h : ℝ}
    (hw : WindowBounds p w W) (hψ : Continuous ψ) (hwc : Continuous w) (hh : h ≠ 0)
    (L : ℕ) :
    patchMeanNormal p B ψ w h (fun c z ↦ refinedKernelPrefix D L (c, z)) =
      ∑ c, ∫ z : Point,
        coloredBlockMask p (integerCube (blockCutoff p B h)) w h c z •
          (ψ z • ∑ j ∈ Finset.univ.filter (fun j : Fin J ↦ j.val < L),
            atomNormal (wideKernelOperator D j.val (j, (c, z)))) := by
  rw [patchMeanNormal_eq_colored hw hψ hwc hh
    (fun c z ↦ refinedKernelPrefix D L (c, z)) (fun c ↦
    (continuous_refinedKernelPrefix D L).comp (continuous_const.prodMk continuous_id))]
  simp_rw [refinedKernelPrefix_normal_eq_wide]
  rfl

end JanetCartan.Sampling.ColoredNormalComparison
