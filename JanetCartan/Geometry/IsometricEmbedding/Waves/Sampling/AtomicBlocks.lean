module

public import JanetCartan.Analysis.Fourier.SeparatedSampling.Counting
public import JanetCartan.Probability.SamplingPrefixes.Variance
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Positive blocks for separated sampling

The literal block operators in `app:ch_waves:thm:sampling` (paper.tex,
lines 5928–5941). The finite sum retains zero weights so that continuity and
strong measurability follow directly. It agrees exactly with the nonzero sample
enumeration from `SeparatedSampling.Counting`.

For a continuous family `T` with `‖T c z‖² ≤ M`, these results prove positivity,
integrability, the block and centered-block bounds, and variance reduction.
The constants give `R = C Λ h³` when `M = C' Λ`. No variance parameter is divided
by, and the statements allow zero operators and zero weights.

This is a conditional component of the sampling theorem. The WKB operator family
and its uniform bounds, uniform shift law and exact expectation, trace estimates,
concentration, and background quadrature must still be supplied at assembly.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public noncomputable section
namespace JanetCartan.Sampling
open SeparatedSampling

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The output normal `TT*` of one row in `app:ch_waves:eq:sampling-prefix-normal`. -/
def atomNormal (T : E →L[ℂ] H) : H →L[ℂ] H := T.comp T.adjoint

/-- Positivity of each atomic normal (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem atomNormal_nonneg (T : E →L[ℂ] H) : 0 ≤ atomNormal T :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_self_comp_adjoint T)

/-- The exact squared row norm used in `app:ch_waves:eq:sampling-operator-bounds`. -/
theorem norm_atomNormal (T : E →L[ℂ] H) : ‖atomNormal T‖ = ‖T‖ ^ 2 := by
  simpa [atomNormal, pow_two] using ContinuousLinearMap.norm_adjoint_comp_self T.adjoint

/-- The positive block `X_q` of `app:ch_waves:thm:sampling`, depending only on its own
shift `u`. The fixed finite enumeration retains zero-weight terms. -/
def atomicBlock (p : ℕ) (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (q : Lattice) (u : Point) : H →L[ℂ] H :=
  ∑ m ∈ integerCube (p + 2), weight ψ w h (fun _ ↦ u) (q, m) •
    atomNormal (T (color p q) (node h (fun _ ↦ u) (q, m)))

/-- The literal translated nodes of `app:ch_waves:thm:sampling` depend continuously
on their block shift. -/
theorem continuous_shifted_node (h : ℝ) (a : Sample) :
    Continuous (fun u : Point ↦ node h (fun _ ↦ u) a) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_apply i)

/-- Continuity of the literal sampling weights in `app:ch_waves:thm:sampling`. -/
theorem continuous_shifted_weight {ψ : Point → ℝ} {w : ℝ → ℝ}
    (hψ : Continuous ψ) (hw : Continuous w) (h : ℝ) (a : Sample) :
    Continuous (fun u : Point ↦ weight ψ w h (fun _ ↦ u) a) := by
  apply (continuous_const.mul (hψ.comp (continuous_shifted_node h a))).mul
  apply continuous_finsetProd
  intro i _
  exact hw.comp (((continuous_apply i).comp
    (continuous_shifted_node h a)).div_const h |>.sub continuous_const)

/-- Continuity of a block from continuity of the window, patch, and row family
(`app:ch_waves:thm:sampling`). -/
theorem continuous_atomicBlock {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    (hψ : Continuous ψ) (hw : Continuous w) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) (q : Lattice) :
    Continuous (atomicBlock p ψ w h T q) := by
  apply continuous_finsetSum
  intro m _
  apply (continuous_shifted_weight hψ hw h (q, m)).smul
  have ht := (hT (color p q)).comp (continuous_shifted_node h (q, m))
  exact ht.clm_comp (ContinuousLinearMap.adjoint.continuous.comp ht)

/-- The bound `0 ≤ X_q` in `app:ch_waves:thm:sampling` for the actual finite
weighted sum of atomic normals. -/
theorem atomicBlock_nonneg {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 ≤ h) (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (q : Lattice) (u : Point) : 0 ≤ atomicBlock p ψ w h T q u := by
  exact Finset.sum_nonneg fun m _ ↦
    smul_nonneg (weight_nonneg hw hψ hh (q, m)) (atomNormal_nonneg _)

/-- The block norm estimate in `app:ch_waves:thm:sampling`. With `M = C Λ`,
the right side has exactly the required order `Λ h³`. -/
theorem norm_atomicBlock_le {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h M : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 ≤ h) (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c z, ‖T c z‖ ^ 2 ≤ M) (q : Lattice) (u : Point) :
    ‖atomicBlock p ψ w h T q u‖ ≤
      (nodesPerBlock p : ℝ) * (h ^ 3 * (P * W ^ 3)) * M := by
  calc
    _ ≤ ∑ m ∈ integerCube (p + 2), ‖weight ψ w h (fun _ ↦ u) (q, m) •
        atomNormal (T (color p q) (node h (fun _ ↦ u) (q, m)))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ integerCube (p + 2), (h ^ 3 * (P * W ^ 3)) * M := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_smul, Real.norm_of_nonneg (weight_nonneg hw hψ hh _), norm_atomNormal]
      exact mul_le_mul (weight_le hw hψ hh _) (hT _ _) (sq_nonneg _) (by
        have hP := (hψ.nonneg 0).trans (hψ.le_bound 0)
        have hW := (hw.nonneg 0).trans (hw.le_bound 0)
        positivity)
    _ = _ := by simp [card_integerCube, nodesPerBlock, mul_assoc]

/-- The Loewner bound `X_q ≤ R I` in `app:ch_waves:thm:sampling`. -/
theorem atomicBlock_le {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h M : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 ≤ h) (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c z, ‖T c z‖ ^ 2 ≤ M) (q : Lattice) (u : Point) :
    atomicBlock p ψ w h T q u ≤
      ((nodesPerBlock p : ℝ) * (h ^ 3 * (P * W ^ 3)) * M) • (1 : H →L[ℂ] H) := by
  have hn := norm_atomicBlock_le hw hψ hh T hT q u
  have hp := atomicBlock_nonneg hw hψ hh T q u
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (CStarAlgebra.norm_le_iff_le_algebraMap _ ((norm_nonneg _).trans hn) hp).mp hn

/-- Strong measurability of a block for any measurable shift
(`app:ch_waves:thm:sampling`). No separability of the space of operators is required. -/
theorem stronglyMeasurable_atomicBlock {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    (hψ : Continuous ψ) (hw : Continuous w) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c, Continuous (T c)) (q : Lattice)
    {Ω : Type*} [MeasurableSpace Ω] {U : Ω → Point} (hU : Measurable U) :
    StronglyMeasurable (fun ω ↦ atomicBlock p ψ w h T q (U ω)) :=
  (continuous_atomicBlock hψ hw h T hT q).stronglyMeasurable.comp_measurable hU

/-- Bochner integrability of the atomic block in `app:ch_waves:thm:sampling`
on every finite measure space of measurable shifts. -/
theorem integrable_atomicBlock {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h M : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hwc : Continuous w) (hψc : Continuous ψ) (hh : 0 ≤ h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hTc : ∀ c, Continuous (T c)) (hT : ∀ c z, ‖T c z‖ ^ 2 ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : Lattice) (U : Ω → Point) (hU : Measurable U) :
    Integrable (fun ω ↦ atomicBlock p ψ w h T q (U ω)) μ :=
  Integrable.of_bound
    (stronglyMeasurable_atomicBlock hψc hwc h T hTc q hU).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun ω ↦ norm_atomicBlock_le hw hψ hh T hT q (U ω))

/-- The centered bound `‖X_q - E X_q‖ ≤ R` in `app:ch_waves:thm:sampling`.
Positivity avoids a factor of two. The integral is Bochner;
`integrable_atomicBlock` supplies integrability for measurable shifts. -/
theorem norm_centered_atomicBlock_le {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h M : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 ≤ h) (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hT : ∀ c z, ‖T c z‖ ^ 2 ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Lattice) (U : Ω → Point) (ω : Ω) :
    ‖atomicBlock p ψ w h T q (U ω) - ∫ ω', atomicBlock p ψ w h T q (U ω') ∂μ‖ ≤
      (nodesPerBlock p : ℝ) * (h ^ 3 * (P * W ^ 3)) * M := by
  have hp : 0 ≤ ∫ ω', atomicBlock p ψ w h T q (U ω') ∂μ :=
    integral_nonneg fun ω' ↦ atomicBlock_nonneg hw hψ hh T q (U ω')
  apply (CStarAlgebra.norm_sub_le_max_of_nonneg
    (atomicBlock_nonneg hw hψ hh T q (U ω)) hp).trans
  apply max_le (norm_atomicBlock_le hw hψ hh T hT q (U ω))
  simpa using norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall fun ω' ↦ norm_atomicBlock_le hw hψ hh T hT q (U ω'))

/-- Discarding zero weights leaves each block unchanged
(`app:ch_waves:thm:sampling`). -/
theorem atomicBlock_eq_sum_nonzero {p : ℕ} (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (q : Lattice) (U : Lattice → Point) :
    atomicBlock p ψ w h T q (U q) =
      ∑ m ∈ blockSamples p ψ w h U q,
        weight ψ w h U (q, m) • atomNormal (T (color p q) (node h U (q, m))) := by
  classical
  unfold atomicBlock blockSamples
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  have hn : node h (fun _ ↦ U q) (q, m) = node h U (q, m) := rfl
  have hw : weight ψ w h (fun _ ↦ U q) (q, m) = weight ψ w h U (q, m) := rfl
  rw [hw, hn]
  by_cases hm : weight ψ w h U (q, m) = 0 <;> simp [hm]

/-- The block sum is exactly the literal sampled normal from
`app:ch_waves:eq:sampling-prefix-normal`, with unchanged colors, nodes, and weights. -/
theorem sum_atomicBlock_eq_sample_normal {p : ℕ} (B : ℝ)
    (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (U : Lattice → Point) :
    (∑ q ∈ integerCube (blockCutoff p B h), atomicBlock p ψ w h T q (U q)) =
      ∑ a ∈ samples p B ψ w h U,
        weight ψ w h U a • atomNormal (T (color p a.1) (node h U a)) := by
  classical
  unfold samples
  rw [Finset.sum_filter]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q _
  unfold atomicBlock
  apply Finset.sum_congr rfl
  intro m _
  have hn : node h (fun _ ↦ U q) (q, m) = node h U (q, m) := rfl
  have hw : weight ψ w h (fun _ ↦ U q) (q, m) = weight ψ w h U (q, m) := rfl
  rw [hw, hn]
  by_cases hm : weight ψ w h U (q, m) = 0 <;> simp [hm]

/-- The variance estimate `V ≤ R ∑q E X_q` of `app:ch_waves:thm:sampling`,
proved for the literal atomic blocks. Identifying the expectation with `E_h`
requires the uniform translation identity. Independence is not needed for this estimate. -/
theorem atomicBlock_variance_le {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ}
    {B P W h M : ℝ} (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hwc : Continuous w) (hψc : Continuous ψ) (hh : 0 ≤ h)
    (T : (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] H)
    (hTc : ∀ c, Continuous (T c)) (hT : ∀ c z, ‖T c z‖ ^ 2 ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset Lattice) (U : Lattice → Ω → Point) (hU : ∀ q, Measurable (U q)) :
    (∑ q ∈ s, ∫ ω, (atomicBlock p ψ w h T q (U q ω) -
        ∫ ω', atomicBlock p ψ w h T q (U q ω') ∂μ) ^ 2 ∂μ) ≤
      ((nodesPerBlock p : ℝ) * (h ^ 3 * (P * W ^ 3)) * M) •
        (∑ q ∈ s, ∫ ω, atomicBlock p ψ w h T q (U q ω) ∂μ) := by
  have hM : 0 ≤ M := (sq_nonneg ‖T (color p 0) 0‖).trans (hT _ _)
  have hP := (hψ.nonneg 0).trans (hψ.le_bound 0)
  have hW := (hw.nonneg 0).trans (hw.le_bound 0)
  apply sum_block_variance_le s _ (by positivity)
  · intro q _
    exact (stronglyMeasurable_atomicBlock hψc hwc h T hTc q (hU q)).aestronglyMeasurable
  · intro q _
    exact Filter.Eventually.of_forall fun ω ↦ atomicBlock_nonneg hw hψ hh T q (U q ω)
  · intro q _
    exact Filter.Eventually.of_forall fun ω ↦ atomicBlock_le hw hψ hh T hT q (U q ω)

end JanetCartan.Sampling
