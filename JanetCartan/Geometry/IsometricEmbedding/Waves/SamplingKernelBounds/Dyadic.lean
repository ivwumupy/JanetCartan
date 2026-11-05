module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.BandOperator
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Rows

/-!
# Dyadic rows of the actual annular kernels

Assembly of `app:ch_waves:eq:sampling-prefix-normal` and the first two estimates
in `app:ch_waves:eq:sampling-operator-bounds`. One `BandKernelData` on the band
index times the parameter space expresses the common physical support and low
amplitude bounds. All Hilbert–Schmidt and continuity premises of the finite-row
deduction are discharged here. Only the sharper single-band oscillatory norm
estimate is a separate input, supplied by `jc-raw-primary-slice-l2`.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.SamplingKernelBounds.BandKernelData
open RawInputRealization

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n J : ℕ} (D : BandKernelData (Fin J × P) n)

/-- The actual coordinate prefix on the unchanged full dyadic input
(`app:ch_waves:eq:sampling-prefix-normal`). The full row is `s = Finset.univ`. -/
def dyadicPrefix (s : Finset (Fin J)) (p : P) :
    Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val) →L[ℂ] Output n :=
  prefixRow s (fun i ↦ D.operator ((2 : ℝ) ^ i.val) (i, p))

/-- Literal band synthesis for the constructed prefix
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem dyadicPrefix_apply (s : Finset (Fin J)) (p : P)
    (f : Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val)) :
    D.dyadicPrefix s p f = ∑ i ∈ s,
      ∫ η, (f i) η • D.column (i, p) η ∂annularMeasure n ((2 : ℝ) ^ i.val) := by
  simp only [dyadicPrefix, prefixRow_apply, D.operator_apply]

/-- The exact sum of the actual band normals, with no cross-band terms
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem dyadicPrefix_normal (s : Finset (Fin J)) (p : P) :
    D.dyadicPrefix s p ∘L (D.dyadicPrefix s p).adjoint =
      ∑ i ∈ s, D.operator ((2 : ℝ) ^ i.val) (i, p) ∘L
        (D.operator ((2 : ℝ) ^ i.val) (i, p)).adjoint :=
  prefixRow_normal s _

/-- Continuity of the actual row, discharging the input to `Sampling.AtomicBlocks`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_dyadicPrefix (s : Finset (Fin J)) : Continuous (D.dyadicPrefix s) :=
  continuous_prefixRow s _ (fun _i ↦
    (D.continuous_operator _).comp (continuous_const.prodMk continuous_id))

variable {ι δ : Type*} [Countable ι] (a : HilbertBasis ι ℂ (Output n))
  (b : HilbertBasis δ ℂ (Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val)))
include a b

/-- Hilbert–Schmidt summability and the literal sum of squared-kernel integrals.
There are no operator summability hypotheses
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem dyadicPrefix_hilbertSchmidt (s : Finset (Fin J)) (p : P) :
    IsHilbertSchmidt b (D.dyadicPrefix s p) ∧
      hilbertSchmidtSq b (D.dyadicPrefix s p) =
        ∑ i ∈ s, ∫ η, ‖D.column (i, p) η‖ ^ 2 ∂annularMeasure n ((2 : ℝ) ^ i.val) := by
  choose κ c hc using fun i : Fin J ↦
    exists_hilbertBasis ℂ (AnnularL2 n ((2 : ℝ) ^ i.val))
  have hs (i : Fin J) := (D.operator_hasAdjointKernel ((2 : ℝ) ^ i.val) (i, p)).hilbertSchmidtSq_eq_integral
    (D.memLp_column _ _) a (c i)
  obtain ⟨hr, he⟩ := prefixRow_hilbertSchmidt s _ c b (fun i _ ↦ (hs i).1)
  refine ⟨hr, he.trans ?_⟩
  exact Finset.sum_congr rfl (fun i _ ↦ (hs i).2)

/-- The weighted trace integrability input is proved from the actual kernels
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_hilbertSchmidtSq_dyadicPrefix (s : Finset (Fin J)) :
    Continuous (fun p ↦ hilbertSchmidtSq b (D.dyadicPrefix s p)) := by
  simp_rw [(D.dyadicPrefix_hilbertSchmidt a b s _).2]
  exact continuous_finsetSum _ (fun i _ ↦
    (D.continuous_integral_norm_column_sq _).comp (continuous_const.prodMk continuous_id))

omit b in
/-- The actual prefix is compact on the whole output
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem isCompactOperator_dyadicPrefix (s : Finset (Fin J)) (p : P) :
    IsCompactOperator (D.dyadicPrefix s p) := by
  obtain ⟨δ, b, _⟩ := exists_hilbertBasis ℂ
    (Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val))
  exact (D.dyadicPrefix_hilbertSchmidt a b s p).1.isCompactOperator

/-- Uniform prefix Hilbert–Schmidt estimate from the actual annular volume
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem hilbertSchmidtSq_dyadicPrefix_le (hn : 1 ≤ n) (s : Finset (Fin J)) (p : P)
    {C_ceiling Λ : ℝ} (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) :
    hilbertSchmidtSq b (D.dyadicPrefix s p) ≤
      (D.squaredKernelConstant * C_ceiling ^ n) * Λ ^ n := by
  rw [(D.dyadicPrefix_hilbertSchmidt a b s p).2]
  exact sum_prefix_dyadic_bound hn s _ D.squaredKernelConstant_nonneg
    (fun i ↦ D.integral_norm_column_sq_le hn (by positivity) (i, p)) hceil

/-- Uniform positive trace on the entire output
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem positiveTrace_dyadicPrefix_normal_le (hn : 1 ≤ n) (s : Finset (Fin J)) (p : P)
    {C_ceiling Λ : ℝ} (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) :
    positiveTrace a (D.dyadicPrefix s p ∘L (D.dyadicPrefix s p).adjoint) ≤
      (D.squaredKernelConstant * C_ceiling ^ n) * Λ ^ n := by
  rw [positiveTrace_normal_eq b a _ (D.dyadicPrefix_hilbertSchmidt a b s p).1]
  exact D.hilbertSchmidtSq_dyadicPrefix_le a b hn s p hceil

/-- Every finite compression obeys the same trace bound
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem trace_finiteCompression_dyadicPrefix_le (hn : 1 ≤ n) (s : Finset (Fin J)) (p : P)
    {C_ceiling Λ : ℝ} (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ)
    (U : Submodule ℂ (Output n)) [FiniteDimensional ℂ U] :
    Complex.re (LinearMap.trace ℂ U (finiteCompression U
      (D.dyadicPrefix s p ∘L (D.dyadicPrefix s p).adjoint)).toLinearMap) ≤
      (D.squaredKernelConstant * C_ceiling ^ n) * Λ ^ n :=
  (trace_finiteCompression_normal_le b _ (D.dyadicPrefix_hilbertSchmidt a b s p).1 U).trans
    (D.hilbertSchmidtSq_dyadicPrefix_le a b hn s p hceil)

omit a b [Countable ι] in
/-- The only additional analytic input is the sharp single-band oscillatory
bound. The full row estimate is deduced, uniformly over all prefixes
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_dyadicPrefix_sq_le (s : Finset (Fin J)) (p : P)
    {C_op C_ceiling Λ : ℝ} (hC : 0 ≤ C_op)
    (hband : ∀ i, ‖D.operator ((2 : ℝ) ^ i.val) (i, p)‖ ^ 2 ≤ C_op * (2 : ℝ) ^ i.val)
    (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) :
    ‖D.dyadicPrefix s p‖ ^ 2 ≤ (C_op * C_ceiling) * Λ :=
  norm_prefixRow_sq_ceiling_le s _ hC hband hceil

omit a b [Countable ι] in
/-- Both input quadratures are retained with the exact factor four and actual
sum of band normals (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem real_dyadicPrefix_normal (s : Finset (Fin J)) (p : P) :
    realQuadratureChannel (D.dyadicPrefix s p) ∘L
      (realQuadratureChannel (D.dyadicPrefix s p)).adjoint =
        (4 : ℝ) • realOutputCompression (∑ i ∈ s,
          D.operator ((2 : ℝ) ^ i.val) (i, p) ∘L
            (D.operator ((2 : ℝ) ^ i.val) (i, p)).adjoint) :=
  real_prefixRow_normal s _

end JanetCartan.SamplingKernelBounds.BandKernelData
