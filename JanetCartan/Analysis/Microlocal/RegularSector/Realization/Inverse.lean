module

public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.Compression
public import JanetCartan.Analysis.Operator.GradedInverse.Neumann

/-!
# The same Neumann inverse over real and complex data

For the supplied complete residual, `app:ch_regular:eq:neumann-series` is used
on both base spaces. Uniqueness proves compatibility; no intertwining premise or
independent choice of inverse is introduced. This is the inverse needed by
`app:ch_response:eq:response-actual-solver-formula`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RegularSector.Realization

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α] {μ : Measure α}

/-- Inclusion intertwines the two actual Neumann series
(`app:ch_regular:eq:neumann-series`). The complex residual must be the complete
bounded residual, including all cutoff and low-frequency errors. -/
theorem inclusion_neumannInverse
    (K : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hreal : conjugateOperator K.toLinearMap = K.toLinearMap) (hK : ‖K‖ < 1)
    (f : Lp (EuclideanSpace ℝ ι) 2 μ) :
    l2ComplexInclusion μ (neumannInverse (realOutputCompression K) f) =
      neumannInverse (K.restrictScalars ℝ) (l2ComplexInclusion μ f) := by
  have hKr : ‖realOutputCompression K‖ < 1 := (realOutputCompression_norm_le K).trans_lt hK
  have hKc : ‖K.restrictScalars ℝ‖ < 1 := by simpa using hK
  apply eq_neumannInverse_of_add_eq _ hKc
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [← inclusion_realCompression K hreal]
  change l2ComplexInclusion μ (neumannInverse (realOutputCompression K) f) +
    l2ComplexInclusion μ (realOutputCompression K (neumannInverse (realOutputCompression K) f)) = _
  rw [← map_add]
  exact congrArg (l2ComplexInclusion μ)
    (eq_sub_iff_add_eq.mp (neumannInverse_eq_sub _ hKr f))

/-- The same base-space inverse is complex-linear, by uniqueness
(`app:ch_regular:eq:neumann-series`). -/
theorem neumannInverse_complex_smul
    (K : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hK : ‖K‖ < 1) (c : ℂ) (z : Lp (EuclideanSpace ℂ ι) 2 μ) :
    neumannInverse (K.restrictScalars ℝ) (c • z) =
      c • neumannInverse (K.restrictScalars ℝ) z := by
  have hKc : ‖K.restrictScalars ℝ‖ < 1 := by simpa using hK
  symm
  apply eq_neumannInverse_of_add_eq _ hKc
  change c • neumannInverse (K.restrictScalars ℝ) z +
    K (c • neumannInverse (K.restrictScalars ℝ) z) = c • z
  rw [map_smul, ← smul_add]
  exact congrArg (c • ·) (eq_sub_iff_add_eq.mp (neumannInverse_eq_sub _ hKc z))

/-- Bundle the already constructed Neumann series as complex-linear; the
underlying map is definitionally the existing `neumannInverse`, not a choice of
another inverse (`app:ch_regular:eq:neumann-series`). -/
def complexNeumannInverse
    (K : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hK : ‖K‖ < 1) : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ where
  toFun := neumannInverse (K.restrictScalars ℝ)
  map_add' := map_add _
  map_smul' c z := neumannInverse_complex_smul K hK c z
  cont := (neumannInverse (K.restrictScalars ℝ)).continuous

/-- Restricting scalars recovers the very same series
(`app:ch_regular:eq:neumann-series`). -/
@[simp] theorem complexNeumannInverse_restrictScalars
    (K : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hK : ‖K‖ < 1) :
    (complexNeumannInverse K hK).restrictScalars ℝ = neumannInverse (K.restrictScalars ℝ) := rfl

/-- The complete complex inverse agrees with the real inverse on both quadratures
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem neumannInverse_quadratures
    (K : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hreal : conjugateOperator K.toLinearMap = K.toLinearMap) (hK : ‖K‖ < 1)
    (f g : Lp (EuclideanSpace ℝ ι) 2 μ) :
    complexNeumannInverse K hK (l2ComplexInclusion μ f + Complex.I • l2ComplexInclusion μ g) =
      l2ComplexInclusion μ (neumannInverse (realOutputCompression K) f) +
        Complex.I • l2ComplexInclusion μ (neumannInverse (realOutputCompression K) g) := by
  rw [map_add, map_smul, inclusion_neumannInverse K hreal hK,
    inclusion_neumannInverse K hreal hK]
  rfl

/-- The complex extension of the real inverse is the original bounded series on
all complex inputs (`app:ch_response:eq:response-actual-solver-formula`). -/
theorem neumannInverse_complex_extension
    (K : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hreal : conjugateOperator K.toLinearMap = K.toLinearMap) (hK : ‖K‖ < 1)
    (z : Lp (EuclideanSpace ℂ ι) 2 μ) :
    complexNeumannInverse K hK z =
      l2ComplexInclusion μ (neumannInverse (realOutputCompression K) (l2RealPart μ z)) +
        Complex.I • l2ComplexInclusion μ
          (neumannInverse (realOutputCompression K) (l2RealPart μ (-Complex.I • z))) := by
  rw [← neumannInverse_quadratures K hreal hK, quadrature_decomposition]

/-- Compressing the same complex series gives exactly the real series
(`app:ch_regular:eq:neumann-series`). -/
theorem realOutputCompression_complexNeumannInverse
    (K : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hreal : conjugateOperator K.toLinearMap = K.toLinearMap) (hK : ‖K‖ < 1) :
    realOutputCompression (complexNeumannInverse K hK) =
      neumannInverse (realOutputCompression K) := by
  ext1 f
  change l2RealPart μ (neumannInverse (K.restrictScalars ℝ) (l2ComplexInclusion μ f)) = _
  rw [← inclusion_neumannInverse K hreal hK, realPart_inclusion]

/-- Both real and complex inverses retain the supplied quantitative contraction
bound (`app:ch_regular:eq:inverse-tame`, base order). -/
theorem real_complex_neumannInverse_norm_le
    (K : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    {θ : ℝ} (hK : ‖K‖ ≤ θ) (hθ : θ < 1) :
    ‖neumannInverse (realOutputCompression K)‖ ≤ (1 - θ)⁻¹ ∧
      ‖complexNeumannInverse K (hK.trans_lt hθ)‖ ≤ (1 - θ)⁻¹ := by
  refine ⟨norm_neumannInverse_le _ ((realOutputCompression_norm_le K).trans hK) hθ, ?_⟩
  rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ), complexNeumannInverse_restrictScalars]
  exact norm_neumannInverse_le _ (by simpa using hK) hθ

end JanetCartan.RegularSector.Realization
