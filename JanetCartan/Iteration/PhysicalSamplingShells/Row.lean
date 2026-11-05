module

public import JanetCartan.Iteration.PhysicalMean.ScalarRow
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.SampledRow
public import JanetCartan.Analysis.Operator.NormalPerturbation.Weighted

/-!
# The same complex sampled row and its original normal

The scalar amplitude test uses the original common sample from
`PhysicalMean.SamplingEvent`. The square-root weights stay in the row and the
original grouped shells stay in its input. Its norm is bounded through the
common-event normal, not by summing individual band operator norms.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.PhysicalSamplingShells
open Sampling Sampling.Realization SamplingKernelBounds RawInputPartition
open SeparatedSampling CanonicalRowComparison

variable {A : Type*} [Fintype A] {n J p : ℕ}
local notation "CP" => (Fin 3 → Fin (p + 1)) × Point

/-- The actual complex row on the same original labels, weights, grouped
prefixes and annular inputs (`new:eq:amplitude-test`). -/
def sampledRefinedRow (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ) :
    PiLp 2 (fun _ : SampleIndex p B ψ w h U ↦ RefinedInput n J) →L[ℂ] Output n :=
  NormalPerturbation.weightedRow (sampleWeight B ψ w h U)
    (fun i ↦ refinedKernelPrefix (D i.1) L (color p i.2.val.1, node h (U i.1) i.2))

/-- The literal square-root sampling sum; zero weights require no exception. -/
theorem sampledRefinedRow_apply (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (f : PiLp 2 (fun _ : SampleIndex p B ψ w h U ↦ RefinedInput n J)) :
    sampledRefinedRow B ψ w h U D L f =
      ∑ i, (Real.sqrt (sampleWeight B ψ w h U i) : ℂ) •
        refinedKernelPrefix (D i.1) L (color p i.2.val.1, node h (U i.1) i.2) (f i) :=
  NormalPerturbation.weightedRow_apply _ _ _

/-- The normal is exactly the producer's original sampled normal, with no
realification factor and no changed sample (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sampledRefinedRow_normal (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (hμ : ∀ i : SampleIndex p B ψ w h U, 0 ≤ sampleWeight B ψ w h U i) :
    NormalPerturbation.normal (sampledRefinedRow B ψ w h U D L) =
      ∑ a, patchSampleNormal p B (ψ a) w h
        (fun c z ↦ refinedKernelPrefix (D a) L (c, z)) (U a) := by
  rw [sampledRefinedRow, NormalPerturbation.normal_weightedRow _ hμ]
  simp only [sampleWeight, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  unfold patchSampleNormal
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i _
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

/-- The common Bernstein event and scalar continuum mean bound control the
SAME row. No sharp-band sum or logarithmic loss is introduced. The event and
mean estimates are produced by `SamplingEvent` and the original scalar kernel
bounds, respectively (`new:eq:amplitude-test`). -/
theorem norm_sampledRefinedRow_le_of_common_event
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (ξ : A → ShiftSpace p B h) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (hμ : ∀ i : SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a)),
      0 ≤ sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)) i)
    {C t : ℝ}
    (hevent : ‖familyDeviation p B ψ w h
      (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤ t)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) w h
      (fun c z ↦ refinedKernelPrefix (D a) L (c, z))‖ ≤ C) :
    ‖sampledRefinedRow B ψ w h (fun a ↦ extendedShift (ξ a)) D L‖ ≤ Real.sqrt (C + t) := by
  let T := fun a c z ↦ refinedKernelPrefix (D a) L (c, z)
  have he : ‖(∑ a, patchSampleNormal p B (ψ a) w h (T a) (extendedShift (ξ a))) -
      (∑ a, patchMeanNormal p B (ψ a) w h (T a))‖ ≤ t := by
    simpa only [familyDeviation, Finset.sum_sub_distrib] using hevent
  have hs : ‖sampledRefinedRow B ψ w h (fun a ↦ extendedShift (ξ a)) D L‖ ^ 2 ≤ C + t := by
    rw [← NormalPerturbation.norm_normal, sampledRefinedRow_normal B ψ w h _ D L hμ]
    exact (norm_le_norm_sub_add _ _).trans ((add_le_add he hmean).trans_eq (add_comm t C))
  calc
    _ = Real.sqrt (‖sampledRefinedRow B ψ w h (fun a ↦ extendedShift (ξ a)) D L‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (C + t) := Real.sqrt_le_sqrt hs

/-- Coordinate extraction of the constructed scalar auxiliary row retains the
same common-event bound; the measured row is not substituted for it. -/
theorem norm_scalar_sampledRefinedRow_le_of_common_event (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (ξ : A → ShiftSpace p B h) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (hμ : ∀ i : SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a)),
      0 ≤ sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)) i)
    {C t : ℝ}
    (hevent : ‖familyDeviation p B ψ w h
      (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤ t)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) w h
      (fun c z ↦ refinedKernelPrefix (D a) L (c, z))‖ ≤ C) :
    ‖(PhysicalMean.scalarOutputProjection hn).comp
      (sampledRefinedRow B ψ w h (fun a ↦ extendedShift (ξ a)) D L)‖ ≤ Real.sqrt (C + t) :=
  (PhysicalMean.norm_scalarOutputProjection_comp_le hn _).trans
    (norm_sampledRefinedRow_le_of_common_event B ψ w h ξ D L hμ hevent hmean)

end JanetCartan.PhysicalSamplingShells
