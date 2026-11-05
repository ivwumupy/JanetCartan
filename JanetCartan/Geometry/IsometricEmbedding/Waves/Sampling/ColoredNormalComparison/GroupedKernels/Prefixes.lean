module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.GroupedKernels.Basic

/-! # The original wide-band row and its unchanged grouped projections

The input identification in `app:ch_waves:eq:sampling-prefix-normal` uses the
published `wideRefinement`, `widePrefix`, and `refinedPrefix`. No new partition
or enumeration is introduced.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 800000

namespace JanetCartan.Sampling.ColoredNormalComparison
open RawInputRealization RawInputPartition SamplingKernelBounds NormalPerturbation

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n J : ℕ}

/-- The row of the original wide-band synthesis operators on the full input
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def wideKernelRow (D : BandKernelData (Fin J × P) n) (z : P) :
    WideInput n J →L[ℂ] SamplingKernelBounds.Output n :=
  weightedRow (fun _ ↦ 1) (fun j ↦ wideKernelOperator D j.val (j, z))

/-- The prefix uses exactly the existing original-band projection
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def wideKernelPrefix (D : BandKernelData (Fin J × P) n) (L : ℕ) (z : P) :
    WideInput n J →L[ℂ] SamplingKernelBounds.Output n :=
  wideKernelRow D z ∘L widePrefix n J L

/-- Refinement carries the original full adjoint to the actual annular adjoint
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideRefinement_wideKernelRow_adjoint (D : BandKernelData (Fin J × P) n)
    (z : P) (v : SamplingKernelBounds.Output n) :
    wideRefinement n J ((wideKernelRow D z).adjoint v) =
      (annularRow (n := n) (fun i : RefinedIndex J ↦
        D.operator (refinedRadius i) (i.1, z))).adjoint v := by
  apply PiLp.ext
  intro i
  rw [annularRow_adjoint_apply]
  change bandRefinement n i.1.val ((wideKernelRow D z).adjoint v i.1) i.2 = _
  simp only [wideKernelRow, weightedRow_adjoint, weightedColumn_apply,
    Real.sqrt_one, RCLike.ofReal_one, one_smul]
  exact bandRefinement_wideKernelOperator_adjoint D i.1.val (i.1, z) v i.2

/-- Exact synthesis reassembly through the already constructed full Hilbert
isometry (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideKernelRow_eq_refined (D : BandKernelData (Fin J × P) n) (z : P) :
    wideKernelRow D z =
      annularRow (n := n) (fun i : RefinedIndex J ↦
        D.operator (refinedRadius i) (i.1, z)) ∘L
          (wideRefinement n J : WideInput n J →L[ℂ] RefinedInput n J) := by
  let T : RefinedInput n J →L[ℂ] SamplingKernelBounds.Output n :=
    annularRow (n := n) (fun i : RefinedIndex J ↦ D.operator (refinedRadius i) (i.1, z))
  ext1 f
  apply ext_inner_right ℂ
  intro v
  change inner ℂ (wideKernelRow D z f) v = inner ℂ (T (wideRefinement n J f)) v
  rw [← (wideKernelRow D z).adjoint_inner_right, ← T.adjoint_inner_right]
  have ha : T.adjoint v = wideRefinement n J ((wideKernelRow D z).adjoint v) :=
    (wideRefinement_wideKernelRow_adjoint D z v).symm
  rw [ha]
  exact ((wideRefinement n J).inner_map_map f ((wideKernelRow D z).adjoint v)).symm

/-- Every unchanged grouped prefix is the literal refined sampling prefix in
the published Hilbert coordinates (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideKernelPrefix_eq_refined (D : BandKernelData (Fin J × P) n)
    (L : ℕ) (z : P) :
    wideKernelPrefix D L z = refinedKernelPrefix D L z ∘L
      (wideRefinement n J : WideInput n J →L[ℂ] RefinedInput n J) := by
  rw [wideKernelPrefix, wideKernelRow_eq_refined, refinedKernelPrefix_eq_comp]
  ext1 v
  change annularRow (n := n) (fun i : RefinedIndex J ↦
    D.operator (refinedRadius i) (i.1, z))
      (wideRefinement n J (widePrefix n J L v)) = _
  rw [wideRefinement_prefix]
  rfl

/-- Normal reassembly for each prefix on the full output. In particular this
applies to every `L ≤ J` (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideKernelPrefix_normal_eq_refined (D : BandKernelData (Fin J × P) n)
    (L : ℕ) (z : P) :
    atomNormal (wideKernelPrefix D L z) = atomNormal (refinedKernelPrefix D L z) := by
  rw [wideKernelPrefix_eq_refined]
  simp only [atomNormal, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm]
  ext1 v
  change refinedKernelPrefix D L z (wideRefinement n J
    ((wideRefinement n J).symm ((refinedKernelPrefix D L z).adjoint v))) = _
  rw [(wideRefinement n J).apply_symm_apply]
  rfl

end JanetCartan.Sampling.ColoredNormalComparison
