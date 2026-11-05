module

public import JanetCartan.Iteration.PhysicalSamplingShells.Native

/-!
# Literal native shell kernel of the original common sampled row

This identifies the SAME complex scalar row with the kernel required by
`norm_integralMatrixRowAmplitudeOperator_le_of_physicalSobolev`. All integrals,
weights, sharp-shell copies and phase factors are literal. No kernel-action or
operator-norm success premise is introduced.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators

namespace JanetCartan.PhysicalSamplingShells
open Sampling Sampling.Realization SamplingKernelBounds RawInputPartition RawInputRealization
open SeparatedSampling CanonicalRowComparison

variable {n J : ℕ}

/-- The scalar coordinate of the original grouped prefix has exactly its finite
annular kernel sum; the two sharp shell copies remain distinct. -/
theorem scalar_refinedKernelPrefix_ae {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (hn : 1 ≤ n) (D : BandKernelData (Fin J × P) n) (L : ℕ) (z : P)
    (f : RefinedInput n J) :
    (PhysicalMean.scalarOutputProjection hn) (refinedKernelPrefix D L z f) =ᵐ[volume]
      fun x ↦ ∑ i ∈ Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < L),
        ∫ η, scalarBandKernel hn D (i.1, z) x η * f i η ∂annularMeasure n (refinedRadius i) := by
  simp only [refinedKernelPrefix, prefixRow_apply, map_sum]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have he := eventuallyEq_sum
    (s := Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < L))
    (fun i _ ↦ (scalar_band_kernel_realization hn D (refinedRadius i) (i.1, z)).2 (f i))
  filter_upwards [he] with x hx
  simpa only [Finset.sum_apply] using hx

variable {A : Type*} [Fintype A]
variable {p : ℕ}
local notation "CP" => (Fin 3 → Fin (p + 1)) × Point

/-- The actual original sampled scalar row is the finite sum of its original
annular integrals, on the unchanged sampled/refined input. -/
theorem nativeScalarOperator_ae_sum (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (f : Lp ℂ 2 (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J)) :
    nativeScalarOperator hn B ψ w h U D L f =ᵐ[volume] fun x ↦
      ∑ i : SampleIndex p B ψ w h U, (Real.sqrt (sampleWeight B ψ w h U i) : ℂ) *
        ∑ j ∈ Finset.univ.filter (fun j : RefinedIndex J ↦ j.1.val < L),
          ∫ η, scalarBandKernel hn (D i.1)
            (j.1, color p i.2.val.1, node h (U i.1) i.2) x η *
            sampledShellEquiv n J f i j η ∂annularMeasure n (refinedRadius j) := by
  simp only [nativeScalarOperator, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    sampledRefinedRow_apply, map_sum, map_smul]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have hi (i : SampleIndex p B ψ w h U) :=
    (Lp.coeFn_smul (Real.sqrt (sampleWeight B ψ w h U i) : ℂ)
      ((PhysicalMean.scalarOutputProjection hn)
        (refinedKernelPrefix (D i.1) L (color p i.2.val.1, node h (U i.1) i.2)
          (sampledShellEquiv n J f i)))).trans
      ((scalar_refinedKernelPrefix_ae hn (D i.1) L
        (color p i.2.val.1, node h (U i.1) i.2) (sampledShellEquiv n J f i)).fun_comp
        (fun z ↦ (Real.sqrt (sampleWeight B ψ w h U i) : ℂ) • z))
  filter_upwards [eventuallyEq_sum (s := Finset.univ) (fun i _ ↦ hi i)] with x hx
  simpa only [Finset.sum_apply, Function.comp_apply, smul_eq_mul] using hx

/-- Integrating on the literal disjoint shell measure is exactly the original
weighted annular sum, not an overlapping-shell or flattened-frequency integral. -/
theorem integral_nativeScalarKernel_mul (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (f : Lp ℂ 2 (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J))
    (x : Euclidean n) :
    (∫ u, nativeScalarKernel hn B ψ w h U D L x u * f u
      ∂sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J) =
      ∑ i : SampleIndex p B ψ w h U, (Real.sqrt (sampleWeight B ψ w h U i) : ℂ) *
        ∑ j ∈ Finset.univ.filter (fun j : RefinedIndex J ↦ j.1.val < L),
          ∫ η, scalarBandKernel hn (D i.1)
            (j.1, color p i.2.val.1, node h (U i.1) i.2) x η *
            sampledShellEquiv n J f i j η ∂annularMeasure n (refinedRadius j) := by
  change (∫ u, nativeScalarKernel hn B ψ w h U D L x u * f u
    ∂Measure.sum (fun i : SampleIndex p B ψ w h U × RefinedIndex J ↦
      (annularMeasure n (refinedRadius i.2)).map (Prod.mk i))) = _
  rw [integral_sum_measure (integrable_nativeScalarKernel_mul hn B ψ w h U D L f x),
    tsum_fintype, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rw [(measurableEmbedding_prodMk_left (i, j)).integral_map]
  by_cases hj : j.1.val < L
  · simp only [nativeScalarKernel, hj, ite_true, mul_assoc, integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards [sampledShellEquiv_ae n J f i j] with η hη
    rw [hη]
  · simp only [nativeScalarKernel, hj, ite_false, zero_mul, integral_zero]

/-- The scalar operator consumed by the physical matrix-amplitude test has
exactly the original common-sample scalar kernel on native disjoint-shell L²
(`new:eq:amplitude-test`). Both its existence and its kernel action are proved. -/
theorem nativeScalarOperator_ae_integral (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : A → Lattice → Point) (D : A → BandKernelData (Fin J × CP) n) (L : ℕ)
    (f : Lp ℂ 2 (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J)) :
    nativeScalarOperator hn B ψ w h U D L f =ᵐ[volume] fun x ↦
      ∫ u, nativeScalarKernel hn B ψ w h U D L x u * f u
        ∂sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J :=
  (nativeScalarOperator_ae_sum hn B ψ w h U D L f).trans
    (Filter.Eventually.of_forall fun x ↦ (integral_nativeScalarKernel_mul hn B ψ w h U D L f x).symm)

end JanetCartan.PhysicalSamplingShells
