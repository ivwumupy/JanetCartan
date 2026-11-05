module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.RefinedEstimates.PowerSums

/-!
# Sampling kernels on the actual grouped annular input

For `app:ch_waves:eq:sampling-prefix-normal`, both sharp shells belonging to
one smooth band use the same kernel. Prefixes are exactly the published
`RawInputPartition.refinedPrefix` on the same full complex input. The sharp
shells occur only in the Hilbert input measures; no smooth symbol estimate is
applied to a shell indicator. The actual raw-wave producer supplies the common
`BandKernelData`, including the original smooth band mask in its amplitude.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace JanetCartan.Sampling
open RawInputRealization RawInputPartition SamplingKernelBounds

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n J : ℕ}

/-- The two shell components remain grouped under their original smooth-band
label (`app:ch_waves:eq:sampling-prefix-normal`). -/
def refinedKernelPrefix (D : BandKernelData (Fin J × P) n) (L : ℕ) (z : P) :
    RefinedInput n J →L[ℂ] SamplingKernelBounds.Output n :=
  prefixRow (Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < L))
    (fun i ↦ D.operator (refinedRadius i) (i.1, z))

/-- Literal annular synthesis for every grouped prefix
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem refinedKernelPrefix_apply (D : BandKernelData (Fin J × P) n) (L : ℕ) (z : P)
    (f : RefinedInput n J) :
    refinedKernelPrefix D L z f =
      ∑ i ∈ Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < L),
        ∫ η, (f i) η • D.column (i.1, z) η ∂annularMeasure n (refinedRadius i) := by
  simp only [refinedKernelPrefix, prefixRow_apply, D.operator_apply]

/-- The sampled prefix is the original row composed with the already constructed
grouped projection, including both complex quadratures
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem refinedKernelPrefix_eq_comp (D : BandKernelData (Fin J × P) n) (L : ℕ) (z : P) :
    refinedKernelPrefix D L z =
      annularRow (fun i : RefinedIndex J ↦ D.operator (refinedRadius i) (i.1, z)) ∘L
        refinedPrefix n J L := by
  symm
  apply annularRow_comp_coordinateProjection
  intro f i
  simp [refinedPrefix_apply]

/-- Exact sum of refined annular normals on the full output
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem refinedKernelPrefix_normal (D : BandKernelData (Fin J × P) n) (L : ℕ) (z : P) :
    atomNormal (refinedKernelPrefix D L z) =
      ∑ i ∈ Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < L),
        atomNormal (D.operator (refinedRadius i) (i.1, z)) :=
  prefixRow_normal _ _

/-- Operator-norm continuity of the literal grouped row
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_refinedKernelPrefix (D : BandKernelData (Fin J × P) n) (L : ℕ) :
    Continuous (refinedKernelPrefix D L) :=
  continuous_prefixRow _ _ (fun i ↦
    (D.continuous_operator (refinedRadius i)).comp (continuous_const.prodMk continuous_id))

/-- Exact Hilbert--Schmidt sum for the same two-shell input; all summability
premises follow from the actual kernels (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem refinedKernelPrefix_hilbertSchmidt (D : BandKernelData (Fin J × P) n)
    {δ : Type*} (b : HilbertBasis δ ℂ (RefinedInput n J)) (L : ℕ) (z : P) :
    IsHilbertSchmidt b (refinedKernelPrefix D L z) ∧
      hilbertSchmidtSq b (refinedKernelPrefix D L z) =
        ∑ i ∈ Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < L),
          ∫ η, ‖D.column (i.1, z) η‖ ^ 2 ∂annularMeasure n (refinedRadius i) := by
  choose κ c _ using fun i : RefinedIndex J ↦ exists_hilbertBasis ℂ (AnnularL2 n (refinedRadius i))
  have hs (i : RefinedIndex J) := (D.operator_hasAdjointKernel (refinedRadius i) (i.1, z)).hilbertSchmidtSq_eq_integral
    (D.memLp_column _ _) (outputHilbertBasis n) (c i)
  obtain ⟨hr, he⟩ := prefixRow_hilbertSchmidt _ _ c b (fun i _ ↦ (hs i).1)
  exact ⟨hr, he.trans (Finset.sum_congr rfl (fun i _ ↦ (hs i).2))⟩

/-- Actual compactness on the entire output, with no compactness premise
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem isCompactOperator_refinedKernelPrefix (D : BandKernelData (Fin J × P) n)
    (L : ℕ) (z : P) : IsCompactOperator (refinedKernelPrefix D L z) := by
  obtain ⟨δ, b, _⟩ := exists_hilbertBasis ℂ (RefinedInput n J)
  exact (refinedKernelPrefix_hilbertSchmidt D b L z).1.isCompactOperator

/-- The actual trace density varies continuously, supplying weighted Bochner
integrability (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_hilbertSchmidtSq_refinedKernelPrefix (D : BandKernelData (Fin J × P) n)
    {δ : Type*} (b : HilbertBasis δ ℂ (RefinedInput n J)) (L : ℕ) :
    Continuous (fun z ↦ hilbertSchmidtSq b (refinedKernelPrefix D L z)) := by
  simp_rw [(refinedKernelPrefix_hilbertSchmidt D b L _).2]
  exact continuous_finsetSum _ (fun i _ ↦
    (D.continuous_integral_norm_column_sq _).comp (continuous_const.prodMk continuous_id))

/-- The fixed two-shell refinement loses only `1 + 2^n` in the trace bound,
independently of the number of bands (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem hilbertSchmidtSq_refinedKernelPrefix_le (D : BandKernelData (Fin J × P) n)
    {δ : Type*} (b : HilbertBasis δ ℂ (RefinedInput n J)) (hn : 1 ≤ n) (L : ℕ) (z : P) :
    hilbertSchmidtSq b (refinedKernelPrefix D L z) ≤
      (D.squaredKernelConstant * (1 + (2 : ℝ) ^ n)) * ((2 : ℝ) ^ J) ^ n := by
  rw [(refinedKernelPrefix_hilbertSchmidt D b L z).2]
  calc
    _ ≤ ∑ i : RefinedIndex J, ∫ η, ‖D.column (i.1, z) η‖ ^ 2
          ∂annularMeasure n (refinedRadius i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    _ ≤ ∑ i : RefinedIndex J, D.squaredKernelConstant * refinedRadius i ^ n :=
      Finset.sum_le_sum (fun i _ ↦ D.integral_norm_column_sq_le hn (refinedRadius_pos i).le _)
    _ = D.squaredKernelConstant * ∑ i : RefinedIndex J, refinedRadius i ^ n :=
      (Finset.mul_sum ..).symm
    _ ≤ D.squaredKernelConstant * ((1 + (2 : ℝ) ^ n) * ((2 : ℝ) ^ J) ^ n) :=
      mul_le_mul_of_nonneg_left (sum_refinedRadius_pow_le hn J) D.squaredKernelConstant_nonneg
    _ = _ := by ring

/-- The sharp row bound has only the fixed refinement factor three. Its sole
analytic input is the original single-band oscillatory bound, applied to the
two restrictions of each smooth band (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_refinedKernelPrefix_sq_le (D : BandKernelData (Fin J × P) n)
    (L : ℕ) (z : P) {C : ℝ} (hC : 0 ≤ C)
    (hband : ∀ i : RefinedIndex J,
      ‖D.operator (refinedRadius i) (i.1, z)‖ ^ 2 ≤ C * refinedRadius i) :
    ‖refinedKernelPrefix D L z‖ ^ 2 ≤ (3 * C) * (2 : ℝ) ^ J := by
  apply (norm_prefixRow_sq_le _ _).trans
  calc
    _ ≤ ∑ i : RefinedIndex J, ‖D.operator (refinedRadius i) (i.1, z)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ sq_nonneg _)
    _ ≤ ∑ i : RefinedIndex J, C * refinedRadius i := Finset.sum_le_sum (fun i _ ↦ hband i)
    _ = C * ∑ i : RefinedIndex J, refinedRadius i := (Finset.mul_sum ..).symm
    _ ≤ C * (3 * (2 : ℝ) ^ J) := mul_le_mul_of_nonneg_left
      (by simpa only [pow_one, show 1 + (2 : ℝ) = 3 by norm_num] using
        sum_refinedRadius_pow_le (p := 1) le_rfl J) hC
    _ = _ := by ring

/-- Both physical real quadratures are retained with the literal factor four
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem real_refinedKernelPrefix_normal (D : BandKernelData (Fin J × P) n) (L : ℕ) (z : P) :
    realQuadratureChannel (refinedKernelPrefix D L z) ∘L
      (realQuadratureChannel (refinedKernelPrefix D L z)).adjoint =
        (4 : ℝ) • realOutputCompression
          (∑ i ∈ Finset.univ.filter (fun i : RefinedIndex J ↦ i.1.val < L),
            atomNormal (D.operator (refinedRadius i) (i.1, z))) :=
  real_prefixRow_normal _ _

end JanetCartan.Sampling
