module

public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.L2

/-!
# Real compression of bounded sector operators

The solver in `app:ch_response:eq:response-actual-solver-formula` can have
source and target fibers of different dimensions. These compression identities
retain both measures, both Euclidean fibers, and the actual complex norm bound.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RegularSector.Realization

variable {ι κ α β : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- Real compression with possibly different output fibers and measures
(`app:ch_regular_base:eq:real-sector-normalization`). -/
def realCompression (A : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ]
    Lp (EuclideanSpace ℂ κ) 2 ν) :
    Lp (EuclideanSpace ℝ ι) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ κ) 2 ν :=
  l2RealPart ν ∘L A.restrictScalars ℝ ∘L l2ComplexInclusion μ

/-- This is the existing endomorphism compression on equal fibers
(`app:ch_regular_base:eq:two-residual-conventions`). -/
theorem realCompression_eq_realOutputCompression
    (A : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    realCompression A = realOutputCompression A := rfl

/-- Compression preserves the supplied operator norm bound without loss
(`app:ch_regular_base:eq:real-sector-normalization`). -/
theorem realCompression_norm_le (A : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ]
    Lp (EuclideanSpace ℂ κ) 2 ν) : ‖realCompression A‖ ≤ ‖A‖ := by
  calc
    ‖realCompression A‖ ≤ ‖l2RealPart (ι := κ) ν‖ *
        (‖A.restrictScalars ℝ‖ * ‖l2ComplexInclusion (ι := ι) μ‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖A‖ * 1) := by
      rw [ContinuousLinearMap.norm_restrictScalars]
      gcongr
      · exact l2RealPart_norm_le ν
      · exact l2ComplexInclusion_norm_le μ
    _ = ‖A‖ := by ring

/-- The inclusion intertwines real compression with the supplied complex operator
(`app:ch_regular_base:eq:real-sector-normalization`). The only reality premise
is whole-operator conjugation, not the desired intertwining. -/
theorem inclusion_realCompression (A : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ]
    Lp (EuclideanSpace ℂ κ) 2 ν) (hA : conjugateOperator A.toLinearMap = A.toLinearMap)
    (f : Lp (EuclideanSpace ℝ ι) 2 μ) :
    l2ComplexInclusion ν (realCompression A f) = A (l2ComplexInclusion μ f) := by
  apply inclusion_realPart_of_star_eq
  change star (A (l2ComplexInclusion μ f)) = A (l2ComplexInclusion μ f)
  have h := LinearMap.congr_fun hA (l2ComplexInclusion μ f)
  simpa only [conjugateOperator_apply, star_inclusion, ContinuousLinearMap.coe_coe] using h

/-- The complex action on both real quadratures is that of the very same bounded
operator (`app:ch_response:eq:response-actual-solver-formula`). -/
theorem realCompression_quadratures (A : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ]
    Lp (EuclideanSpace ℂ κ) 2 ν) (hA : conjugateOperator A.toLinearMap = A.toLinearMap)
    (f g : Lp (EuclideanSpace ℝ ι) 2 μ) :
    A (l2ComplexInclusion μ f + Complex.I • l2ComplexInclusion μ g) =
      l2ComplexInclusion ν (realCompression A f) +
        Complex.I • l2ComplexInclusion ν (realCompression A g) := by
  rw [map_add, map_smul, inclusion_realCompression A hA, inclusion_realCompression A hA]

/-- On every complex input, the real solver's complex extension is the original
bounded construction (`app:ch_response:eq:response-actual-solver-formula`). -/
theorem realCompression_complex_extension (A : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ]
    Lp (EuclideanSpace ℂ κ) 2 ν) (hA : conjugateOperator A.toLinearMap = A.toLinearMap)
    (z : Lp (EuclideanSpace ℂ ι) 2 μ) :
    A z = l2ComplexInclusion ν (realCompression A (l2RealPart μ z)) +
      Complex.I • l2ComplexInclusion ν (realCompression A (l2RealPart μ (-Complex.I • z))) := by
  rw [← realCompression_quadratures A hA, quadrature_decomposition]

/-- Uniqueness of the complex-linear extension used in
`app:ch_response:eq:response-actual-solver-formula`. -/
theorem complex_operator_eq_of_inclusion
    (A B : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (h : ∀ f, A (l2ComplexInclusion μ f) = B (l2ComplexInclusion μ f)) : A = B := by
  ext1 z
  conv_lhs => rw [← quadrature_decomposition z]
  rw [map_add, map_smul, h, h, ← map_smul, ← map_add, quadrature_decomposition]

end JanetCartan.RegularSector.Realization
