module

public import JanetCartan.Iteration.PhysicalSamplingShells.Samples
public import JanetCartan.Iteration.PhysicalSamplingShells.Row
public import JanetCartan.Iteration.PhysicalSamplingShells.Kernel

/-!
# The same scalar sampled row on native disjoint-shell L²

This is the scalar operator supplied to the physical matrix-amplitude test
`new:eq:amplitude-test`. Its kernel retains each original sample and refined
shell, the full band phase, the half derivative and the square-root sample
weight. Its norm is exactly the original sampled scalar row norm.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.PhysicalSamplingShells
open Sampling Sampling.Realization SamplingKernelBounds RawInputPartition RawInputRealization
open SeparatedSampling CanonicalRowComparison

variable {A : Type*} [Fintype A]

omit [Fintype A] in
/-- Every original dependent sample label is measurable. This uses its finite
sample fiber, not an altered sampling measure. -/
instance sampleIndex_measurableSingletonClass (p : ℕ)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ) (U : A → Lattice → Point) :
    MeasurableSingletonClass (SampleIndex p B ψ w h U) := by
  constructor
  intro i
  change MeasurableSet[⨅ a, (inferInstance : MeasurableSpace (samples p B (ψ a) w h (U a))).map
    (Sigma.mk a)] {i}
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro a
  change MeasurableSet ((Sigma.mk a) ⁻¹' {i})
  exact (Set.to_countable _).measurableSet

variable {n J p : ℕ}
local notation "CP" => (Fin 3 → Fin (p + 1)) × Point

/-- The original scalar sampled row, transported through the exact disjoint
input isometry and no other replacement (`new:eq:amplitude-test`). -/
def nativeScalarOperator (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ) :
    Lp ℂ 2 (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)) :=
  ((PhysicalMean.scalarOutputProjection hn).comp (sampledRefinedRow B ψ w h U D L)).comp
    (sampledShellEquiv n J).toLinearIsometry.toContinuousLinearMap

/-- Literal scalar shell kernel. Original square-root weights, including zero
weights, are multiplied in; they are never moved into the measure or inverted. -/
def nativeScalarKernel (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (x : Euclidean n)
    (u : (SampleIndex p B ψ w h U × RefinedIndex J) × Euclidean (n - 1)) : ℂ :=
  if u.1.2.1.val < L then
    (Real.sqrt (sampleWeight B ψ w h U u.1.1) : ℂ) *
      scalarBandKernel hn (D u.1.1.1)
        (u.1.2.1, color p u.1.1.2.val.1, node h (U u.1.1.1) u.1.1.2) x u.2
  else 0

/-- The original same-sample scalar row and its native shell realization have
identical operator norm. No shell-count or logarithmic factor appears. -/
theorem norm_nativeScalarOperator_eq (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ) :
    ‖nativeScalarOperator hn B ψ w h U D L‖ =
      ‖(PhysicalMean.scalarOutputProjection hn).comp (sampledRefinedRow B ψ w h U D L)‖ := by
  let e := sampledShellEquiv (V := ℂ) (ι := SampleIndex p B ψ w h U) n J
  let T := (PhysicalMean.scalarOutputProjection hn).comp (sampledRefinedRow B ψ w h U D L)
  change ‖T.comp e.toLinearIsometry.toContinuousLinearMap‖ = ‖T‖
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro f
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, e.norm_map] using T.le_opNorm (e f)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro f
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, e.apply_symm_apply, e.symm.norm_map] using
      (T.comp e.toLinearIsometry.toContinuousLinearMap).le_opNorm (e.symm f)

/-- The SAME common-event bound transfers to the native scalar test operator;
no independent sample or scalar-row norm premise is selected. -/
theorem norm_nativeScalarOperator_le_of_common_event (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (ξ : A → ShiftSpace p B h) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (hμ : ∀ i : SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a)),
      0 ≤ sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)) i)
    {C t : ℝ}
    (hevent : ‖familyDeviation p B ψ w h
      (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤ t)
    (hmean : ‖∑ a, patchMeanNormal p B (ψ a) w h
      (fun c z ↦ refinedKernelPrefix (D a) L (c, z))‖ ≤ C) :
    ‖nativeScalarOperator hn B ψ w h (fun a ↦ extendedShift (ξ a)) D L‖ ≤ Real.sqrt (C + t) := by
  rw [norm_nativeScalarOperator_eq]
  exact norm_scalar_sampledRefinedRow_le_of_common_event hn B ψ w h ξ D L hμ hevent hmean

/-- Every physical row section is integrable against every native input.
The proof uses the original annular datum on each disjoint shell. -/
theorem integrable_nativeScalarKernel_mul (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (f : Lp ℂ 2 (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J))
    (x : Euclidean n) :
    Integrable (fun u ↦ nativeScalarKernel hn B ψ w h U D L x u * f u)
      (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J) := by
  change Integrable _ (Measure.sum (fun i : SampleIndex p B ψ w h U × RefinedIndex J ↦
    (annularMeasure n (refinedRadius i.2)).map (Prod.mk i)))
  rw [Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i _
  apply (measurableEmbedding_prodMk_left i).integrable_map_iff.mpr
  change Integrable (fun η ↦ nativeScalarKernel hn B ψ w h U D L x (i, η) * f (i, η))
    (annularMeasure n (refinedRadius i.2))
  by_cases hi : i.2.1.val < L
  · have hmem := (scalar_band_kernel_realization hn (D i.1.1) (refinedRadius i.2)
      (i.2.1, color p i.1.2.val.1, node h (U i.1.1) i.1.2)).1
        (sampledShellEquiv n J f i.1 i.2) x
    apply (hmem.const_mul (Real.sqrt (sampleWeight B ψ w h U i.1) : ℂ)).congr
    filter_upwards [sampledShellEquiv_ae n J f i.1 i.2] with η hη
    simp only [nativeScalarKernel, hi, ite_true, hη, mul_assoc]
  · simp only [nativeScalarKernel, hi, ite_false, zero_mul]
    exact integrable_const (0 : ℂ)

/-- The original scalar kernel is integrable against every native finite-channel
input. This proves the vector-integrability premise of
`norm_integralMatrixRowAmplitudeOperator_le_of_physicalSobolev` on the SAME shells. -/
theorem integrable_nativeScalarKernel_smul {I : Type*} [Fintype I] (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (f : Lp (EuclideanSpace ℂ I) 2
      (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J)) (x : Euclidean n) :
    Integrable (fun u ↦ nativeScalarKernel hn B ψ w h U D L x u • f u)
      (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J) := by
  apply Integrable.of_eval_piLp
  intro i
  let μ := sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J
  let pr := PiLp.proj (𝕜 := ℂ) 2 (fun _ : I ↦ ℂ) i
  let g := pr.compLpL 2 μ f
  apply (integrable_nativeScalarKernel_mul hn B ψ w h U D L g x).congr
  filter_upwards [pr.coeFn_compLpL f] with u hu
  simpa only [g, pr, PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul] using
    congrArg (fun z : ℂ ↦ nativeScalarKernel hn B ψ w h U D L x u * z) hu

end JanetCartan.PhysicalSamplingShells
