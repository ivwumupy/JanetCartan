module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Rows.Ceiling
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# Physical real rows retaining both quadratures

The full complex annular input is regarded as real, as required after
`app:ch_waves:eq:sampling-operator-bounds`. No input quadrature is discarded.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.SamplingKernelBounds
open RawInputRealization

variable {ι : Type*} [Fintype ι] {n : ℕ} {radius : ι → ℝ}

/-- Both physical quadratures survive every coordinate prefix
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem real_prefixRow_both_quadratures_ae (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) (f g : Input n radius) :
    ∀ᵐ x ∂volume, ∀ j, realQuadratureChannel (prefixRow s T) (f + Complex.I • g) x j =
      2 * (((∑ i ∈ s, T i (f i)) x j).re - ((∑ i ∈ s, T i (g i)) x j).im) := by
  simpa only [prefixRow_apply] using
    realQuadratureChannel_both_quadratures_ae (prefixRow s T) f g

/-- Exact factor-four real normal on the same full input, with the literal
sum of annular normals (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem real_prefixRow_normal (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) :
    realQuadratureChannel (prefixRow s T) ∘L (realQuadratureChannel (prefixRow s T)).adjoint =
      (4 : ℝ) • realOutputCompression (∑ i ∈ s, T i ∘L (T i).adjoint) := by
  rw [realQuadratureChannel_normal_eq_four_realPart, prefixRow_normal]

/-- The real squared row bound costs at most the fixed factor four
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_real_prefixRow_sq_le (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n) :
    ‖realQuadratureChannel (prefixRow s T)‖ ^ 2 ≤ 4 * ∑ i ∈ s, ‖T i‖ ^ 2 :=
  (realQuadratureChannel_norm_sq_le _).trans
    (mul_le_mul_of_nonneg_left (norm_prefixRow_sq_le s T) (by positivity))

/-- The real row is compact while retaining both quadratures
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem isCompactOperator_real_prefixRow {κ : ι → Type*} (s : Finset ι)
    (T : ∀ i, AnnularL2 n (radius i) →L[ℂ] Output n)
    (c : ∀ i, HilbertBasis (κ i) ℂ (AnnularL2 n (radius i)))
    (hT : ∀ i ∈ s, IsHilbertSchmidt (c i) (T i)) :
    IsCompactOperator (realQuadratureChannel (prefixRow s T)) :=
  ((isCompactOperator_prefixRow s T c hT).clm_comp (l2RealPart volume)).smul (2 : ℝ)

/-- The fixed real factor does not depend on the chosen prefix or ceiling
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_real_prefixRow_sq_ceiling_le {J : ℕ} (s : Finset (Fin J))
    (T : ∀ i : Fin J, AnnularL2 n ((2 : ℝ) ^ i.val) →L[ℂ] Output n)
    {C_op C_ceiling Λ : ℝ} (hC : 0 ≤ C_op)
    (hT : ∀ i, ‖T i‖ ^ 2 ≤ C_op * (2 : ℝ) ^ i.val)
    (hceil : (2 : ℝ) ^ J ≤ C_ceiling * Λ) :
    ‖realQuadratureChannel (prefixRow s T)‖ ^ 2 ≤ 4 * ((C_op * C_ceiling) * Λ) :=
  (realQuadratureChannel_norm_sq_le _).trans
    (mul_le_mul_of_nonneg_left (norm_prefixRow_sq_ceiling_le s T hC hT hceil)
      (by positivity))

end JanetCartan.SamplingKernelBounds
