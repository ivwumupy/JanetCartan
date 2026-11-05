module

public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.Inverse

/-!
# The same contraction constant for the complex normalized inverse

The normalized construction records its contraction on real L². Its complete
complex residual preserves conjugation, so its norm equals the norm of that
real compression. This permits the existing complex Neumann-series API to be
used on the SAME measured operator. In particular, the two original real
quadratures are recombined before primary demodulation in
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open RegularSector RegularSector.Realization

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α] {μ : Measure α}
local notation "RH" => Lp (EuclideanSpace ℝ ι) 2 μ
local notation "CH" => Lp (EuclideanSpace ℂ ι) 2 μ

private theorem norm_l2_inclusion (f : RH) : ‖l2ComplexInclusion μ f‖ = ‖f‖ := by
  apply le_antisymm
  · exact ((l2ComplexInclusion μ).le_opNorm f).trans
      ((mul_le_mul_of_nonneg_right (l2ComplexInclusion_norm_le μ) (norm_nonneg f)).trans_eq
        (one_mul _))
  · calc
      ‖f‖ = ‖l2RealPart μ (l2ComplexInclusion μ f)‖ := by rw [realPart_inclusion]
      _ ≤ ‖l2ComplexInclusion μ f‖ := ((l2RealPart μ).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (l2RealPart_norm_le μ) (norm_nonneg _)).trans_eq
          (one_mul _))

private theorem realPart_imaginary_inclusion (f : RH) :
    l2RealPart μ (Complex.I • l2ComplexInclusion μ f) = 0 := by
  apply Lp.ext
  filter_upwards [euclideanRealPart.coeFn_compLpL (Complex.I • l2ComplexInclusion μ f),
    Lp.coeFn_smul Complex.I (l2ComplexInclusion μ f),
    euclideanComplexInclusion.coeFn_compLpL f, Lp.coeFn_zero (E := EuclideanSpace ℝ ι)
      (p := 2) (μ := μ)] with x hr hs hi hz
  simp only [l2RealPart, l2ComplexInclusion, Pi.smul_apply] at *
  rw [hr, hs, hi, hz]
  ext i
  simp

private theorem norm_l2_quadratures_sq (f g : RH) :
    ‖l2ComplexInclusion μ f + Complex.I • l2ComplexInclusion μ g‖ ^ 2 =
      ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
  have hi : ⟪l2ComplexInclusion μ f, Complex.I • l2ComplexInclusion μ g⟫_ℝ = 0 := by
    rw [real_inner_comm, ← l2RealPart_inner, realPart_imaginary_inclusion, inner_zero_left]
  rw [norm_add_sq_real, hi, norm_smul, Complex.norm_I, one_mul,
    norm_l2_inclusion f, norm_l2_inclusion g]
  ring

/-- Conjugation-preserving complex L² operators have exactly the norm of
their real compression. Applied to the complete measured normalized residual,
this retains its original contraction constant; the characteristic and
elliptic summands are not compressed separately
(`app:ch_regular:eq:neumann-series`, `real-sector-normalization`). -/
theorem realCompression_norm_eq_of_conjugation (T : CH →L[ℂ] CH)
    (hT : conjugateOperator T.toLinearMap = T.toLinearMap) :
    ‖realCompression T‖ = ‖T‖ := by
  apply le_antisymm (realCompression_norm_le T)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  let f := l2RealPart μ z
  let g := l2RealPart μ (-Complex.I • z)
  have hz : ‖z‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
    simpa only [f, g, quadrature_decomposition] using norm_l2_quadratures_sq f g
  have hTz : ‖T z‖ ^ 2 =
      ‖realCompression T f‖ ^ 2 + ‖realCompression T g‖ ^ 2 := by
    rw [realCompression_complex_extension T hT z]
    exact norm_l2_quadratures_sq _ _
  have hf := pow_le_pow_left₀ (norm_nonneg (realCompression T f))
    ((realCompression T).le_opNorm f) 2
  have hg := pow_le_pow_left₀ (norm_nonneg (realCompression T g))
    ((realCompression T).le_opNorm g) 2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [hTz, mul_pow, hz, mul_add]
  simpa only [mul_pow] using add_le_add hf hg

/-- The real contraction supplied by the initialized inverse constructs a
contracting complex residual on the SAME L² measure, and the existing complex
Neumann series is exactly the combined pair of real series. No second
operator or independently selected inverse occurs
(`app:ch_regular:eq:neumann-series`,
`app:ch_response:eq:response-actual-solver-formula`). -/
theorem complexNeumannInverse_of_real_contraction (T : CH →L[ℂ] CH)
    (hT : conjugateOperator T.toLinearMap = T.toLinearMap)
    {κ : ℝ} (hκ : κ < 1) (hreal : ‖realOutputCompression T‖ ≤ κ) :
    ∃ hcomplex : ‖T‖ < 1,
      ‖complexNeumannInverse T hcomplex‖ ≤ (1 - κ)⁻¹ ∧
      ∀ f g : RH,
        complexNeumannInverse T hcomplex
            (l2ComplexInclusion μ f + Complex.I • l2ComplexInclusion μ g) =
          l2ComplexInclusion μ (neumannInverse (realOutputCompression T) f) +
            Complex.I • l2ComplexInclusion μ (neumannInverse (realOutputCompression T) g) := by
  have hbound : ‖T‖ ≤ κ := by
    rw [← realCompression_norm_eq_of_conjugation T hT]
    exact hreal
  exact ⟨hbound.trans_lt hκ, (real_complex_neumannInverse_norm_le T hbound hκ).2,
    neumannInverse_quadratures T hT (hbound.trans_lt hκ)⟩

end JanetCartan.FixedDomainInverse
