module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.MaskRemoval
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.HilbertRefinement

/-!
# Reassembly of the literal sampling kernels

The two sharp Hilbert components of `app:ch_waves:eq:sampling-prefix-normal`
are reassembled before any smooth symbol calculation. The consumer is the
unmasked right side of `norm_refinedKernelPrefix_mean_le_unmasked`.

All operators below are constructed from `BandKernelData.column` on the original
Lebesgue wide band. Their adjoints and normal identities are deductions from
those kernels, not additional matching assumptions. RawPrimary's
`Construction.fullPrimaryWave` and the leading/full-phase constructions must
still supply the same phase and measured amplitude, including `radialBand`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace JanetCartan.Sampling.MeanNormalBound
open RawInputRealization RawInputPartition SamplingKernelBounds

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n J : ℕ}

/-- Square integrability of the unchanged physical columns on the entire wide
band (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem memLp_wideBand_column (D : BandKernelData P n) (j : ℕ) (z : P) :
    MemLp (D.column z) 2 (volume.restrict (wideBand n j)) :=
  memLp_restrict_compact_column
    (D.continuous_column.comp (continuous_const.prodMk continuous_id))
    ((isCompact_closedBall (0 : Euclidean (n - 1)) (4 * dyadicScale j)).diff
      Metric.isOpen_ball)

/-- The original wide-band sampling operator, with full Euclidean vector L²
output and the unchanged measured kernel (`app:ch_waves:eq:sampling-prefix-normal`). -/
def wideBandKernelOperator (D : BandKernelData P n) (j : ℕ) (z : P) :
    WideBandL2 n j →L[ℂ] SamplingKernelBounds.Output n :=
  kernelSynthesis (memLp_wideBand_column D j z)

/-- Literal forward synthesis on the wide band
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideBandKernelOperator_apply (D : BandKernelData P n) (j : ℕ) (z : P)
    (f : WideBandL2 n j) :
    wideBandKernelOperator D j z f =
      ∫ η in wideBand n j, f η • D.column z η :=
  kernelSynthesis_apply (memLp_wideBand_column D j z) f

/-- The wide-band adjoint is proved from the forward column construction
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideBandKernelOperator_hasAdjointKernel (D : BandKernelData P n) (j : ℕ)
    (z : P) : HasAdjointKernel (wideBandKernelOperator D j z) (D.column z) :=
  kernelSynthesis_hasAdjointKernel (memLp_wideBand_column D j z)

/-- The adjoint retains the literal physical Lebesgue integral on the whole
output (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideBandKernelOperator_adjoint_ae (D : BandKernelData P n) (j : ℕ) (z : P)
    (v : SamplingKernelBounds.Output n) :
    (wideBandKernelOperator D j z).adjoint v =ᵐ[volume.restrict (wideBand n j)]
      fun η ↦ ∫ x, inner ℂ (D.kernel z η x) (v x) := by
  filter_upwards [wideBandKernelOperator_hasAdjointKernel D j z v] with η hη
  rw [hη, L2.inner_def]
  exact integral_congr_ae ((D.column_coe z η).mono
    (fun x hx ↦ congrArg (fun u ↦ inner ℂ u (v x)) hx))

/-- Restricting the actual wide adjoint gives precisely the two original
annular adjoints, retaining both complex quadratures
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem bandRefinement_wideBandKernelOperator_adjoint (D : BandKernelData P n)
    (j : ℕ) (z : P) (v : SamplingKernelBounds.Output n) (b : Fin 2) :
    bandRefinement n j ((wideBandKernelOperator D j z).adjoint v) b =
      (D.operator ((2 : ℝ) ^ (j + b.val)) z).adjoint v := by
  apply Lp.ext
  have hw := ae_mono
    (Measure.restrict_mono (annulus_subset_wideBand n j b) le_rfl)
    (wideBandKernelOperator_hasAdjointKernel D j z v)
  filter_upwards [bandRestriction_coeFn n j
    ((wideBandKernelOperator D j z).adjoint v) b, hw,
    D.operator_hasAdjointKernel ((2 : ℝ) ^ (j + b.val)) z v] with η hr hw ha
  exact hr.trans (hw.trans ha.symm)

set_option maxHeartbeats 800000 in
/-- Forward equality with the two-shell row follows from the derived adjoints;
there is no independent normal matching premise
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideBandKernelOperator_eq_refined (D : BandKernelData P n) (j : ℕ) (z : P) :
    wideBandKernelOperator D j z =
      annularRow (fun b : Fin 2 ↦ D.operator ((2 : ℝ) ^ (j + b.val)) z) ∘L
        (bandRefinement n j).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.adjoint.injective
  rw [ContinuousLinearMap.adjoint_comp, (bandRefinement n j).adjoint_eq_symm]
  ext1 v
  apply (bandRefinement n j).injective
  apply PiLp.ext
  intro b
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply,
    annularRow_adjoint_apply] using bandRefinement_wideBandKernelOperator_adjoint D j z v b

/-- Both sharp components of one band reassemble into its unchanged full
output normal (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideBandKernelOperator_normal (D : BandKernelData P n) (j : ℕ) (z : P) :
    atomNormal (wideBandKernelOperator D j z) =
      ∑ b : Fin 2, atomNormal (D.operator ((2 : ℝ) ^ (j + b.val)) z) := by
  rw [wideBandKernelOperator_eq_refined]
  have he : atomNormal
      (annularRow (fun b : Fin 2 ↦ D.operator ((2 : ℝ) ^ (j + b.val)) z) ∘L
        (bandRefinement n j).toContinuousLinearEquiv.toContinuousLinearMap) =
      atomNormal (annularRow (fun b : Fin 2 ↦
        D.operator ((2 : ℝ) ^ (j + b.val)) z)) := by
    unfold atomNormal
    rw [ContinuousLinearMap.adjoint_comp, (bandRefinement n j).adjoint_eq_symm]
    ext v
    simp
  rw [he]
  simpa only [prefixRow_univ, atomNormal] using prefixRow_normal Finset.univ
    (fun b : Fin 2 ↦ D.operator ((2 : ℝ) ^ (j + b.val)) z)

/-- Continuity in operator norm is proved from the compact original columns
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_wideBandKernelOperator (D : BandKernelData P n) (j : ℕ) :
    Continuous (wideBandKernelOperator D j) :=
  continuous_kernelSynthesis_compact D.continuous_column
    ((isCompact_closedBall (0 : Euclidean (n - 1)) (4 * dyadicScale j)).diff
      Metric.isOpen_ball)

/-- The original row on the full finite sum of wide bands, before the
two-shell input isometry (`app:ch_waves:eq:sampling-prefix-normal`). -/
def wideBandKernelRow (D : BandKernelData (Fin J × P) n) (z : P) :
    WideInput n J →L[ℂ] SamplingKernelBounds.Output n :=
  NormalPerturbation.weightedRow (fun _ ↦ 1)
    (fun j : Fin J ↦ wideBandKernelOperator D j.val (j, z))

/-- The complete original row and the largest refined prefix are the same
forward map under `wideRefinement`. This is the literal input isometry;
its norm and both quadratures are already preserved by the shared construction
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideBandKernelRow_eq_refined (D : BandKernelData (Fin J × P) n) (z : P) :
    wideBandKernelRow D z = refinedKernelPrefix D J z ∘L
      (wideRefinement n J).toContinuousLinearEquiv.toContinuousLinearMap := by
  ext1 f
  simp only [wideBandKernelRow, NormalPerturbation.weightedRow_apply,
    Real.sqrt_one, RCLike.ofReal_one, one_smul, ContinuousLinearMap.comp_apply]
  simp_rw [wideBandKernelOperator_eq_refined, ContinuousLinearMap.comp_apply, annularRow_apply]
  rw [refinedKernelPrefix, prefixRow_apply]
  simp only [Fin.is_lt, Finset.filter_true, Fintype.sum_prod_type]
  rfl

/-- The largest refined prefix is exactly the sum of the reassembled original
wide-band normals. In particular no sharp shell is passed to the subsequent
smooth symbol calculus (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem refinedKernelPrefix_normal_eq_wide (D : BandKernelData (Fin J × P) n) (z : P) :
    atomNormal (refinedKernelPrefix D J z) =
      ∑ j : Fin J, atomNormal (wideBandKernelOperator D j.val (j, z)) := by
  rw [refinedKernelPrefix_normal]
  simp only [Fin.is_lt, Finset.filter_true, Fintype.sum_prod_type]
  simp_rw [wideBandKernelOperator_normal]
  rfl

/-- The same largest-prefix identity for the physical real row includes both
quadratures and the literal factor four
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem real_refinedKernelPrefix_normal_eq_wide
    (D : BandKernelData (Fin J × P) n) (z : P) :
    realQuadratureChannel (refinedKernelPrefix D J z) ∘L
      (realQuadratureChannel (refinedKernelPrefix D J z)).adjoint =
        (4 : ℝ) • realOutputCompression
          (∑ j : Fin J, atomNormal (wideBandKernelOperator D j.val (j, z))) := by
  rw [← refinedKernelPrefix_normal_eq_wide]
  exact realQuadratureChannel_normal_eq_four_realPart _

end JanetCartan.Sampling.MeanNormalBound
