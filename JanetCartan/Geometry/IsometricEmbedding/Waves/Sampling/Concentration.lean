module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Family
public import JanetCartan.Analysis.Operator.HilbertSchmidt.Integral
public import JanetCartan.Probability.HilbertOperatorBernstein
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Concentration of the literal shifted blocks

The probability connection in `app:ch_waves:thm:sampling`: the independent
variables are the original positive atomic blocks on the finite chart product
law. Their centered variance is bounded by `R E_h`, with the original continuum
expectation. The entire output is retained, including when actual variance is
zero; only the chosen upper parameters are positive.

The actual wave producer must still supply compact continuous rows, their sharp
norm bound, and the order-one bound for the continuum normal. The last bound
comes from the full normal comparison, not the Hilbert--Schmidt estimate.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped InnerProductSpace BigOperators

namespace JanetCartan.Sampling
open SeparatedSampling Realization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H]

omit [CompleteSpace H] in
private theorem exists_finiteDimensional_approximation :
    ∃ U : ℕ → Submodule ℂ H, (∀ n, FiniteDimensional ℂ (U n)) ∧
      Monotone U ∧ (⨆ n, U n).topologicalClosure = ⊤ := by
  classical
  let U (n : ℕ) := Submodule.span ℂ (↑((Finset.range n).image (denseSeq H)) : Set H)
  refine ⟨U, fun _ ↦ inferInstance, ?_, ?_⟩
  · intro i j hij
    exact Submodule.span_mono (Finset.coe_subset.mpr
      (Finset.image_subset_image (Finset.range_mono hij)))
  · apply Submodule.eq_top_iff'.mpr
    intro x
    change x ∈ closure (↑(⨆ n, U n) : Set H)
    apply (closure_mono ?_) ((denseRange_denseSeq H) x)
    rintro _ ⟨i, rfl⟩
    exact (le_iSup U (i + 1)) (Submodule.subset_span
      (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_self i), rfl⟩))

private theorem positive_blocks_bernstein
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    [MeasurableSpace (H →L[ℂ] H)] [BorelSpace (H →L[ℂ] H)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → H →L[ℂ] H)
    (hIndep : iIndepFun X μ) (hX : ∀ i, StronglyMeasurable (X i))
    (hcompact : ∀ i ω, IsCompactOperator (X i ω))
    (hpos : ∀ i ω, 0 ≤ X i ω) {R C D t : ℝ}
    (hbound : ∀ i ω, ‖X i ω‖ ≤ R) (hR : 0 < R) (hC : 0 < C)
    (hmean : ‖∑ i, ∫ ω, X i ω ∂μ‖ ≤ C)
    (htrace : ∀ (m : ℕ) (e : Fin m → H), Orthonormal ℂ e →
      ∑ j, Complex.re ⟪e j, (∑ i, ∫ ω, X i ω ∂μ) (e j)⟫_ℂ ≤ D)
    (ht : 0 < t) (hthreshold : R * C + R * t / 3 ≤ t ^ 2) :
    μ {ω | t < ‖∑ i, (X i ω - ∫ ω', X i ω' ∂μ)‖} ≤
      OperatorCompression.bernsteinTail R (R * C) (R * D) t := by
  classical
  let Y i ω := X i ω - ∫ ω', X i ω' ∂μ
  have hi i : Integrable (X i) μ :=
    Integrable.of_bound (hX i).aestronglyMeasurable R
      (Filter.Eventually.of_forall (hbound i))
  have hp i : 0 ≤ ∫ ω, X i ω ∂μ := integral_nonneg (hpos i)
  have hYm i : StronglyMeasurable (Y i) := (hX i).sub stronglyMeasurable_const
  have hYsa i ω : IsSelfAdjoint (Y i ω) :=
    (hpos i ω).isSelfAdjoint.sub (hp i).isSelfAdjoint
  have hYb i ω : ‖Y i ω‖ ≤ R := by
    apply (CStarAlgebra.norm_sub_le_max_of_nonneg (hpos i ω) (hp i)).trans
    apply max_le (hbound i ω)
    simpa using norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (hbound i))
  obtain ⟨U, hU, hmono, hdense⟩ := exists_finiteDimensional_approximation (H := H)
  let := hU
  apply HilbertOperatorBernstein.operatorBernstein U hmono hdense
    (hIndep.comp (fun i A ↦ A - ∫ ω, X i ω ∂μ)
      (fun _ ↦ (continuous_id.sub continuous_const).measurable))
    (fun i ↦ (hYm i).aestronglyMeasurable)
    (fun i ω ↦ (hcompact i ω).sub (isCompactOperator_integral _ (hi i)
      (Filter.Eventually.of_forall (hcompact i)))) hYsa ?_
    (fun i ↦ Filter.Eventually.of_forall (hYb i)) hR (mul_pos hR hC)
    (R • (∑ i, ∫ ω, X i ω ∂μ)) ?_ ?_ ?_ ht hthreshold
  · intro i
    simp [integral_sub (hi i) (integrable_const _)]
  · rw [norm_smul, Real.norm_of_nonneg hR.le]
    exact mul_le_mul_of_nonneg_left hmean hR.le
  · intro x
    have horder := sum_block_variance_le (μ := μ) Finset.univ X hR.le
      (fun i _ ↦ (hX i).aestronglyMeasurable)
      (fun i _ ↦ Filter.Eventually.of_forall (hpos i))
      (fun i _ ↦ Filter.Eventually.of_forall fun ω ↦ by
        simpa only [Algebra.algebraMap_eq_smul_one] using
          (CStarAlgebra.norm_le_iff_le_algebraMap _ hR.le (hpos i ω)).mp (hbound i ω))
    have hq := (ContinuousLinearMap.le_def.mp horder).re_inner_nonneg_right x
    have hmoment i := HilbertOperatorBernstein.re_inner_integral_square (μ := μ)
      (hYm i).aestronglyMeasurable (Filter.Eventually.of_forall (hYb i))
      (Filter.Eventually.of_forall (hYsa i)) x
    have he : Complex.re ⟪x, (∑ i, ∫ ω, Y i ω ^ 2 ∂μ) x⟫_ℂ =
        ∑ i, ∫ ω, ‖Y i ω x‖ ^ 2 ∂μ := by
      change diagonalCLM x (∑ i, ∫ ω, Y i ω ^ 2 ∂μ) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      change Complex.re ⟪x, (∫ ω, Y i ω ^ 2 ∂μ) x⟫_ℂ = _
      simpa only [pow_two] using hmoment i
    simp only [sub_apply, inner_sub_right, map_sub] at hq
    change 0 ≤ Complex.re ⟪x, (R • (∑ i, ∫ ω, X i ω ∂μ)) x⟫_ℂ -
      Complex.re ⟪x, (∑ i, ∫ ω, Y i ω ^ 2 ∂μ) x⟫_ℂ at hq
    rw [he] at hq
    exact sub_nonneg.mp hq
  · intro m e he
    change (∑ j, diagonalCLM (e j) (R • (∑ i, ∫ ω, X i ω ∂μ))) ≤ _
    simp only [map_smul, smul_eq_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (htrace m e he) hR.le

variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype J]

omit [SeparableSpace H] in
/-- Compact rows give compact literal blocks, before centering or compression
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem isCompactOperator_atomicBlock {p : ℕ} (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c z, IsCompactOperator (T c z)) (q : Lattice) (u : Point) :
    IsCompactOperator (atomicBlock p ψ w h T q u) := by
  change (∑ m ∈ integerCube (p + 2), _) ∈ compactOperator (RingHom.id ℂ) H H
  apply Submodule.sum_mem
  intro m _
  exact ((hT (color p q) (node h (fun _ ↦ u) (q, m))).comp_clm
    (T (color p q) (node h (fun _ ↦ u) (q, m))).adjoint).smul
      (weight ψ w h (fun _ ↦ u) (q, m))

omit [SeparableSpace H] in
/-- Independence across both charts and blocks on the original product law
(`app:ch_waves:thm:sampling`). No replacement of the sample space is made. -/
theorem iIndepFun_atomicBlock_familyShiftLaw
    [MeasurableSpace (H →L[ℂ] H)] [BorelSpace (H →L[ℂ] H)]
    {p : ℕ} {B h : ℝ} {ψ : J → Point → ℝ} {w : ℝ → ℝ}
    (hψc : ∀ j, Continuous (ψ j)) (hwc : Continuous w) (hh : 0 < h)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ j c, Continuous (T j c)) :
    iIndepFun (fun i : J × ShiftIndex p B h ↦ fun ω : J → ShiftSpace p B h ↦
      atomicBlock p (ψ i.1) w h (T i.1) i.2 (extendedShift (ω i.1) i.2))
        (familyShiftLaw J p B h) := by
  let := isProbabilityMeasure_uniformShift hh
  simpa only [Measure.infinitePi_eq_pi, familyShiftLaw, shiftLaw, extendedShift_coe] using
    (iIndepFun_uncurry_infinitePi'
      (fun (_ : J) (_ : ShiftIndex p B h) ↦ uniformShift h)
      (X := fun j (q : ShiftIndex p B h) ↦ atomicBlock p (ψ j) w h (T j) q)
      (fun j q ↦ (continuous_atomicBlock (hψc j) hwc h (T j) (hT j) q).measurable))

omit [SeparableSpace H] in
/-- Each chart/block expectation on the full chart product law is its literal
Lebesgue integral (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_atomicBlock_familyShiftLaw
    {p : ℕ} {B W h : ℝ} {P : J → ℝ} {ψ : J → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hψ : ∀ j, PatchBounds (ψ j) B (P j))
    (hψc : ∀ j, Continuous (ψ j)) (hwc : Continuous w) (hh : 0 < h)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ j c, Continuous (T j c)) (i : J × ShiftIndex p B h) :
    (∫ ω, atomicBlock p (ψ i.1) w h (T i.1) i.2 (extendedShift (ω i.1) i.2)
      ∂familyShiftLaw J p B h) =
        ∫ z, (ψ i.1 z * blockWeight w h i.2 z) • atomNormal (T i.1 (color p i.2) z) := by
  let := isProbabilityMeasure_shiftLaw p B hh
  have he := integral_comp_eval (i := i.1)
    (μ := fun _ : J ↦ shiftLaw p B h)
    (integrable_atomicBlock_shiftLaw (hψc i.1) hwc hh (T i.1) (hT i.1) i.2).aestronglyMeasurable
  exact he.trans (integral_atomicBlock_shiftLaw hw (hψ i.1) (hψc i.1) hwc hh
    (T i.1) (hT i.1) i.2)

/-- Whole-output concentration for the original finite chart family and its
unchanged prefix rows (`app:ch_waves:eq:sampling-all-prefixes`). The centered
family, compactness, self-adjointness, expectation and variance are derived
here, rather than assumed as Bernstein inputs. `hmean` is the separate full
normal comparison obligation, and `htrace` is supplied by kernel estimates.
Positive upper parameters allow zero row, zero weight and zero variance. -/
theorem operatorBernstein_familyDeviation
    {p : ℕ} {B W h M R C D t : ℝ} {P : J → ℝ}
    {ψ : J → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hψ : ∀ j, PatchBounds (ψ j) B (P j))
    (hψc : ∀ j, Continuous (ψ j)) (hwc : Continuous w) (hh : 0 < h)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hTc : ∀ j c, Continuous (T j c)) (hcompact : ∀ j c z, IsCompactOperator (T j c z))
    (hT : ∀ j c z, ‖T j c z‖ ^ 2 ≤ M)
    (hblock : ∀ j, (nodesPerBlock p : ℝ) * (h ^ 3 * (P j * W ^ 3)) * M ≤ R)
    (hR : 0 < R) (hC : 0 < C)
    (hmean : ‖∑ j, patchMeanNormal p B (ψ j) w h (T j)‖ ≤ C)
    (htrace : ∀ (m : ℕ) (e : Fin m → H), Orthonormal ℂ e →
      ∑ k, Complex.re ⟪e k, (∑ j, patchMeanNormal p B (ψ j) w h (T j)) (e k)⟫_ℂ ≤ D)
    (ht : 0 < t) (hthreshold : R * C + R * t / 3 ≤ t ^ 2) :
    familyShiftLaw J p B h {ω | t < ‖familyDeviation p B ψ w h T ω‖} ≤
      OperatorCompression.bernsteinTail R (R * C) (R * D) t := by
  classical
  let : MeasurableSpace (H →L[ℂ] H) := borel _
  let := isProbabilityMeasure_familyShiftLaw (J := J) p B hh
  let X (i : J × ShiftIndex p B h) (ω : J → ShiftSpace p B h) :=
    atomicBlock p (ψ i.1) w h (T i.1) i.2 (extendedShift (ω i.1) i.2)
  have hsum : (∑ i, ∫ ω, X i ω ∂familyShiftLaw J p B h) =
      ∑ j, patchMeanNormal p B (ψ j) w h (T j) := by
    simp only [X, integral_atomicBlock_familyShiftLaw hw hψ hψc hwc hh T hTc,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_coe_sort (integerCube (blockCutoff p B h))
      (fun q ↦ ∫ z, (ψ j z * blockWeight w h q z) • atomNormal (T j (color p q) z))
  have hdev ω : familyDeviation p B ψ w h T ω =
      ∑ i, (X i ω - ∫ ω', X i ω' ∂familyShiftLaw J p B h) := by
    simp only [familyDeviation, Finset.sum_sub_distrib, hsum, X, Fintype.sum_prod_type]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_coe_sort (integerCube (blockCutoff p B h))
      (fun q ↦ atomicBlock p (ψ j) w h (T j) q (extendedShift (ω j) q))]
    exact (sum_atomicBlock_eq_sample_normal B (ψ j) w h (T j) _).symm
  simp_rw [hdev]
  apply positive_blocks_bernstein _ X
    (iIndepFun_atomicBlock_familyShiftLaw hψc hwc hh T hTc)
    (fun i ↦ stronglyMeasurable_atomicBlock (hψc i.1) hwc h (T i.1) (hTc i.1) i.2
      ((measurable_extendedShift i.2).comp (measurable_pi_apply i.1)))
    (fun i ω ↦ isCompactOperator_atomicBlock _ _ _ _ (hcompact i.1) _ _)
    (fun i ω ↦ atomicBlock_nonneg hw (hψ i.1) hh.le _ _ _)
    (fun i ω ↦ (norm_atomicBlock_le hw (hψ i.1) hh.le _ (hT i.1) _ _).trans (hblock i.1))
    hR hC (hsum ▸ hmean) ?_ ht hthreshold
  simpa only [hsum] using htrace

end JanetCartan.Sampling
