module

public import JanetCartan.Analysis.Operator.HilbertSchmidt.Integral
public import JanetCartan.Analysis.Operator.HilbertSchmidt.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ShiftLaw.Expectation

/-!
# Compactly weighted whole-output expectations

Conditional deductions for `app:ch_waves:eq:sampling-prefix-normal` and
`app:ch_waves:eq:sampling-operator-bounds`. The row producer must supply continuity
and Hilbert–Schmidt summability; integrability, compactness and trace bounds are
proved here. All parameter integrals use literal Lebesgue measure on `Point`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators
namespace JanetCartan.SamplingKernelBounds.Expectation
open SeparatedSampling Sampling

variable {E F ι κ C : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [Fintype C]

/-- Analytic inputs for the weighted expectation in
`app:ch_waves:eq:sampling-prefix-normal`. These are supplied by the annular row
construction and the actual scalar sampling weights. -/
structure WeightedFamily (b : HilbertBasis ι ℂ E) (C : Type*) where
  operator : C → Point → E →L[ℂ] F
  weight : C → Point → ℝ
  continuous_operator : ∀ c, Continuous (operator c)
  hilbertSchmidt : ∀ c z, IsHilbertSchmidt b (operator c z)
  continuous_hilbertSchmidtSq : ∀ c, Continuous (fun z ↦ hilbertSchmidtSq b (operator c z))
  continuous_weight : ∀ c, Continuous (weight c)
  compactSupport_weight : ∀ c, HasCompactSupport (weight c)
  nonneg_weight : ∀ c z, 0 ≤ weight c z

namespace WeightedFamily
variable {b : HilbertBasis ι ℂ E} (D : WeightedFamily (F := F) b C)

/-- The actual finite sum of Lebesgue integrals in
`app:ch_waves:eq:sampling-prefix-normal`. -/
def expectation : F →L[ℂ] F :=
  ∑ c, ∫ z, D.weight c z • atomNormal (D.operator c z)

/-- Scalar continuum mass in `app:ch_waves:eq:sampling-operator-bounds`. -/
def mass : ℝ := ∑ c, ∫ z, D.weight c z

omit [Fintype C] in
/-- Operator integrability follows from the scalar support, without an operator
integrability premise (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_normal (c : C) :
    Integrable (fun z ↦ D.weight c z • atomNormal (D.operator c z)) :=
  ((D.continuous_weight c).smul ((D.continuous_operator c).clm_comp
    (ContinuousLinearMap.adjoint.continuous.comp (D.continuous_operator c)))).integrable_of_hasCompactSupport
    (D.compactSupport_weight c).smul_right

omit [CompleteSpace E] [CompleteSpace F] [Fintype C] in
/-- Weighted trace integrability in `app:ch_waves:eq:sampling-operator-bounds`. -/
theorem integrable_weightedTrace (c : C) :
    Integrable (fun z ↦ D.weight c z * hilbertSchmidtSq b (D.operator c z)) :=
  ((D.continuous_weight c).mul (D.continuous_hilbertSchmidtSq c)).integrable_of_hasCompactSupport
    (D.compactSupport_weight c).mul_right

omit [CompleteSpace E] [CompleteSpace F] [Fintype C] in
/-- Scalar weight integrability in `app:ch_waves:eq:sampling-prefix-normal`. -/
theorem integrable_weight (c : C) : Integrable (D.weight c) :=
  (D.continuous_weight c).integrable_of_hasCompactSupport (D.compactSupport_weight c)

/-- Positivity in the operator order (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem expectation_nonneg : 0 ≤ D.expectation :=
  Finset.sum_nonneg fun c _ ↦ integral_nonneg fun z ↦
    smul_nonneg (D.nonneg_weight c z) (atomNormal_nonneg _)

omit [Fintype C] in
/-- Compactness of each Lebesgue integral, via the closed subspace of compact
operators (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem compact_integral (c : C) :
    IsCompactOperator (∫ z, D.weight c z • atomNormal (D.operator c z) : F →L[ℂ] F) := by
  let S := (compactOperator (RingHom.id ℂ) F F).restrictScalars ℝ
  let f : Point → S := fun z ↦ ⟨D.weight c z • atomNormal (D.operator c z),
    ((D.hilbertSchmidt c z).isCompactOperator.comp_clm (D.operator c z).adjoint).smul _⟩
  have hc : Continuous f :=
    ((D.continuous_weight c).smul ((D.continuous_operator c).clm_comp
      (ContinuousLinearMap.adjoint.continuous.comp (D.continuous_operator c)))).subtype_mk _
  have hs : HasCompactSupport f := by
    apply HasCompactSupport.intro (D.compactSupport_weight c)
    intro z hz
    apply Subtype.ext
    change D.weight c z • atomNormal (D.operator c z) = 0
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  have : IsClosed (S : Set (F →L[ℂ] F)) := isClosed_setOfPred_isCompactOperator
  have : CompleteSpace S := IsClosed.completeSpace_coe
  have he := S.subtypeL.integral_comp_comm (hc.integrable_of_hasCompactSupport (μ := volume) hs)
  change (∫ z, D.weight c z • atomNormal (D.operator c z)) ∈ S
  rw [show (∫ z, D.weight c z • atomNormal (D.operator c z)) =
    S.subtypeL (∫ z, f z) from he]
  exact (∫ z, f z).property

/-- Compactness of the full expectation (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem expectation_compact : IsCompactOperator D.expectation := by
  change D.expectation ∈ compactOperator (RingHom.id ℂ) F F
  exact Submodule.sum_mem _ (fun c _ ↦ D.compact_integral c)

omit [Fintype C] in
private theorem weighted_diagonal (c : C) (z : Point) (y : F) :
    diagonalCLM y (D.weight c z • atomNormal (D.operator c z)) =
      D.weight c z * ‖(D.operator c z).adjoint y‖ ^ 2 := by
  rw [map_smul]
  simp only [diagonalCLM_apply, atomNormal, ContinuousLinearMap.comp_apply,
    ← (D.operator c z).adjoint_inner_left, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, RCLike.ofReal_re, smul_eq_mul]

/-- The convergent full-output diagonal sum, with its exact value
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem hasSum_diagonal [Countable κ] (a : HilbertBasis κ ℂ F) :
    HasSum (fun i ↦ diagonalCLM (a i) D.expectation)
      (∑ c, ∫ z, D.weight c z * hilbertSchmidtSq b (D.operator c z)) := by
  have hc (c : C) := hasSum_diagonal_integral a _ (D.integrable_normal c)
    (fun z y ↦ by
      change 0 ≤ diagonalCLM (𝕜 := ℂ) y (D.weight c z • atomNormal (D.operator c z))
      rw [D.weighted_diagonal]
      exact mul_nonneg (D.nonneg_weight c z) (sq_nonneg _))
    (fun z ↦ by
      change Summable (fun i ↦ diagonalCLM (𝕜 := ℂ) (a i) (D.weight c z • atomNormal (D.operator c z)))
      simp_rw [D.weighted_diagonal]
      exact (isHilbertSchmidt_adjoint b a _ (D.hilbertSchmidt c z)).1.mul_left _)
    (by
      have he (z : Point) : positiveTrace a (D.weight c z • atomNormal (D.operator c z)) =
          D.weight c z * hilbertSchmidtSq b (D.operator c z) := by
        change (∑' i, diagonalCLM (𝕜 := ℂ) (a i) (D.weight c z • atomNormal (D.operator c z))) = _
        simp_rw [D.weighted_diagonal, tsum_mul_left]
        exact congrArg (fun r ↦ D.weight c z * r)
          (isHilbertSchmidt_adjoint b a _ (D.hilbertSchmidt c z)).2
      simpa only [he] using D.integrable_weightedTrace c)
  have hv (c : C) := positiveTrace_integral_weighted_normal b a (D.operator c)
    (D.weight c) (D.hilbertSchmidt c) (D.nonneg_weight c)
    (D.integrable_normal c) (D.integrable_weightedTrace c)
  have hc' (c : C) : HasSum (fun i ↦ diagonalCLM (a i)
      (∫ z, D.weight c z • atomNormal (D.operator c z)))
      (∫ z, D.weight c z * hilbertSchmidtSq b (D.operator c z)) := by
    have h := (hc c).summable.hasSum
    exact hv c ▸ h
  simpa only [expectation, map_sum] using hasSum_sum (fun c (_ : c ∈ Finset.univ) ↦ hc' c)

/-- Exact Tonelli identity for the full-output trace
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem trace_eq [Countable κ] (a : HilbertBasis κ ℂ F) :
    positiveTrace a D.expectation =
      ∑ c, ∫ z, D.weight c z * hilbertSchmidtSq b (D.operator c z) :=
  (D.hasSum_diagonal a).tsum_eq

/-- A uniform squared Hilbert–Schmidt bound times the actual scalar mass bounds
trace (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem trace_le_mass [Countable κ] (a : HilbertBasis κ ℂ F) (H : ℝ)
    (hH : ∀ c z, hilbertSchmidtSq b (D.operator c z) ≤ H) :
    positiveTrace a D.expectation ≤ H * D.mass := by
  rw [D.trace_eq, mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [← integral_const_mul]
  exact integral_mono (D.integrable_weightedTrace c) ((D.integrable_weight c).const_mul H)
    (fun z ↦ by simpa [mul_comm] using mul_le_mul_of_nonneg_left (hH c z) (D.nonneg_weight c z))

/-- The explicit `C Λ^n` trace bound once the scalar mass is bounded
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem trace_le_scale [Countable κ] (a : HilbertBasis κ ℂ F)
    (n : ℕ) (Λ C_HS M : ℝ) (hH : 0 ≤ C_HS * Λ ^ n)
    (hHS : ∀ c z, hilbertSchmidtSq b (D.operator c z) ≤ C_HS * Λ ^ n)
    (hM : D.mass ≤ M) : positiveTrace a D.expectation ≤ (C_HS * M) * Λ ^ n := by
  calc
    _ ≤ (C_HS * Λ ^ n) * D.mass := D.trace_le_mass a _ hHS
    _ ≤ (C_HS * Λ ^ n) * M := mul_le_mul_of_nonneg_left hM hH
    _ = _ := by ring

private def compressionTrace (U : Submodule ℂ F) [FiniteDimensional ℂ U] :
    (F →L[ℂ] F) →L[ℝ] ℝ :=
  ∑ i, diagonalCLM ((stdOrthonormalBasis ℂ U i : U) : F)

private theorem compressionTrace_eq (U : Submodule ℂ F) [FiniteDimensional ℂ U]
    (A : F →L[ℂ] F) : compressionTrace U A =
      Complex.re (LinearMap.trace ℂ U (finiteCompression U A).toLinearMap) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ U)]
  simp only [compressionTrace, sum_apply, diagonalCLM_apply,
    Complex.re_sum, ContinuousLinearMap.coe_coe, finiteCompression_inner]
  rfl

/-- Every finite compression has the same integrated Hilbert–Schmidt upper bound
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem trace_finiteCompression_le (U : Submodule ℂ F) [FiniteDimensional ℂ U] :
    Complex.re (LinearMap.trace ℂ U (finiteCompression U D.expectation).toLinearMap) ≤
      ∑ c, ∫ z, D.weight c z * hilbertSchmidtSq b (D.operator c z) := by
  rw [← compressionTrace_eq, expectation, map_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [← (compressionTrace U).integral_comp_comm (D.integrable_normal c)]
  apply integral_mono ((compressionTrace U).integrable_comp (D.integrable_normal c))
    (D.integrable_weightedTrace c)
  intro z
  dsimp only
  rw [map_smul, smul_eq_mul, compressionTrace_eq]
  exact mul_le_mul_of_nonneg_left
    (trace_finiteCompression_normal_le b _ (D.hilbertSchmidt c z) U) (D.nonneg_weight c z)

/-- Every finite compression is bounded by the full-output trace
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem trace_finiteCompression_le_trace [Countable κ] (a : HilbertBasis κ ℂ F)
    (U : Submodule ℂ F) [FiniteDimensional ℂ U] :
    Complex.re (LinearMap.trace ℂ U (finiteCompression U D.expectation).toLinearMap) ≤
      positiveTrace a D.expectation := by
  rw [D.trace_eq a]
  exact D.trace_finiteCompression_le U

/-- The explicit scale bound also controls every finite compression
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem trace_finiteCompression_le_scale [Countable κ] (a : HilbertBasis κ ℂ F)
    (U : Submodule ℂ F) [FiniteDimensional ℂ U]
    (n : ℕ) (Λ C_HS M : ℝ) (hH : 0 ≤ C_HS * Λ ^ n)
    (hHS : ∀ c z, hilbertSchmidtSq b (D.operator c z) ≤ C_HS * Λ ^ n)
    (hM : D.mass ≤ M) :
    Complex.re (LinearMap.trace ℂ U (finiteCompression U D.expectation).toLinearMap) ≤
      (C_HS * M) * Λ ^ n :=
  (D.trace_finiteCompression_le_trace a U).trans (D.trace_le_scale a n Λ C_HS M hH hHS hM)

end WeightedFamily
end JanetCartan.SamplingKernelBounds.Expectation
