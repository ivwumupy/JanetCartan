module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RefinedKernels
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.HilbertRefinement

/-!
# Reassembly of the literal sampling bands

For `app:ch_waves:eq:sampling-prefix-normal`, synthesis on each original
`wideBand` is constructed from the same `BandKernelData.column`. The existing
Hilbert refinement identifies it with both sharp components together. This
module supplies the grouped input identity to the colored normal comparison;
the actual wave producer still supplies `BandKernelData`.
-/

@[expose] public noncomputable section
open MeasureTheory
set_option maxHeartbeats 800000
open scoped InnerProductSpace BigOperators

namespace JanetCartan.Sampling.ColoredNormalComparison
open RawInputRealization RawInputPartition SamplingKernelBounds

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n J : ℕ}

/-- Compactness of the original band, with the first scale still one half
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem isCompact_samplingWideBand (n j : ℕ) : IsCompact (wideBand n j) :=
  (isCompact_closedBall _ _).diff Metric.isOpen_ball

/-- Square integrability on the original smooth band is a consequence of the
actual continuous columns (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem memLp_wideBand_column (D : BandKernelData P n) (j : ℕ) (z : P) :
    MemLp (D.column z) 2 (volume.restrict (wideBand n j)) :=
  memLp_restrict_compact_column
    (D.continuous_column.comp (continuous_const.prodMk continuous_id))
    (isCompact_samplingWideBand n j)

/-- Synthesis on the original wide-band measure, retaining the entire physical
output and the original smooth kernel (`app:ch_waves:eq:sampling-prefix-normal`). -/
def wideKernelOperator (D : BandKernelData P n) (j : ℕ) (z : P) :
    WideBandL2 n j →L[ℂ] SamplingKernelBounds.Output n :=
  kernelSynthesis (memLp_wideBand_column D j z)

/-- Literal integral action on a wide band
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideKernelOperator_apply (D : BandKernelData P n) (j : ℕ) (z : P)
    (f : WideBandL2 n j) :
    wideKernelOperator D j z f = ∫ η in wideBand n j, f η • D.column z η :=
  kernelSynthesis_apply (memLp_wideBand_column D j z) f

/-- The adjoint follows from the constructed synthesis kernel
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideKernelOperator_hasAdjointKernel (D : BandKernelData P n) (j : ℕ) (z : P) :
    HasAdjointKernel (wideKernelOperator D j z) (D.column z) :=
  kernelSynthesis_hasAdjointKernel (memLp_wideBand_column D j z)

/-- The wide-band adjoint restricts to the two original annular adjoints.
No normal identity is assumed (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem bandRefinement_wideKernelOperator_adjoint (D : BandKernelData P n)
    (j : ℕ) (z : P) (v : SamplingKernelBounds.Output n) (b : Fin 2) :
    bandRefinement n j ((wideKernelOperator D j z).adjoint v) b =
      (D.operator ((2 : ℝ) ^ (j + b.val)) z).adjoint v := by
  apply Lp.ext
  filter_upwards [bandRestriction_coeFn n j ((wideKernelOperator D j z).adjoint v) b,
    ae_restrict_of_ae_restrict_of_subset (annulus_subset_wideBand n j b)
      (wideKernelOperator_hasAdjointKernel D j z v),
    D.operator_hasAdjointKernel ((2 : ℝ) ^ (j + b.val)) z v] with η h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

/-- A wide-band normal is exactly the sum of its two original sharp-component
normals on the full output (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideKernelOperator_normal (D : BandKernelData P n) (j : ℕ) (z : P) :
    atomNormal (wideKernelOperator D j z) =
      ∑ b : Fin 2, atomNormal (D.operator ((2 : ℝ) ^ (j + b.val)) z) := by
  ext1 v
  apply ext_inner_left ℂ
  intro w
  simp only [atomNormal, sum_apply, ContinuousLinearMap.comp_apply,
    inner_sum]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [← (bandRefinement n j).inner_map_map, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [bandRefinement_wideKernelOperator_adjoint,
    bandRefinement_wideKernelOperator_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- Every literal refined prefix reassembles to its original smooth-band
normals. This holds for all `L`, hence in particular for `L ≤ J`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem refinedKernelPrefix_normal_eq_wide (D : BandKernelData (Fin J × P) n)
    (L : ℕ) (z : P) :
    atomNormal (refinedKernelPrefix D L z) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin J ↦ j.val < L),
        atomNormal (wideKernelOperator D j.val (j, z)) := by
  classical
  rw [refinedKernelPrefix_normal]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < L
  · simp only [hj, ite_true, ← wideKernelOperator_normal, refinedRadius]
  · simp only [hj, ite_false, Finset.sum_const_zero]

/-- The reassembled normal keeps both real quadratures and exactly factor four
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem real_refinedKernelPrefix_normal_eq_wide (D : BandKernelData (Fin J × P) n)
    (L : ℕ) (z : P) :
    realQuadratureChannel (refinedKernelPrefix D L z) ∘L
      (realQuadratureChannel (refinedKernelPrefix D L z)).adjoint =
        (4 : ℝ) • realOutputCompression
          (∑ j ∈ Finset.univ.filter (fun j : Fin J ↦ j.val < L),
            atomNormal (wideKernelOperator D j.val (j, z))) := by
  rw [realQuadratureChannel_normal_eq_four_realPart,
    show refinedKernelPrefix D L z ∘L (refinedKernelPrefix D L z).adjoint = _ from
      refinedKernelPrefix_normal_eq_wide D L z]

end JanetCartan.Sampling.ColoredNormalComparison
