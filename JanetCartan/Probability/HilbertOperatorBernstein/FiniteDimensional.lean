module

public import JanetCartan.Probability.HilbertOperatorBernstein.Moments
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Bernstein on a finite-dimensional Hilbert space

The matrix Bernstein application for each compression in
`app:ch_waves:thm:sampling`, including all measure and coordinate transfers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Matrix.Norms.Frobenius BigOperators ComplexOrder

namespace JanetCartan.HilbertOperatorBernstein

variable {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E] [Fintype ι]
  [MeasurableSpace Ω] [MeasurableSpace (E →L[ℂ] E)] [BorelSpace (E →L[ℂ] E)]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ι → Ω → E →L[ℂ] E}

/-- Bernstein for finite-dimensional Hilbert operators, deduced from matrix
Bernstein in `app:ch_waves:thm:sampling`. The two quadratic bounds supplied here
are obtained from the ambient variance by orthogonal compression. -/
theorem finiteDimensional_bernstein
    (hIndep : iIndepFun Y μ) (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hsa : ∀ i, ∀ᵐ ω ∂μ, IsSelfAdjoint (Y i ω))
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    {R v τ t : ℝ} (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ R)
    (hR : 0 < R) (hv : 0 < v)
    (hvariance : ∀ x, ∑ i, ∫ ω, ‖Y i ω x‖ ^ 2 ∂μ ≤ v * ‖x‖ ^ 2)
    (B : E →L[ℂ] E)
    (hB : ∀ x, ∑ i, ∫ ω, ‖Y i ω x‖ ^ 2 ∂μ ≤ Complex.re ⟪x, B x⟫_ℂ)
    (htrace : Complex.re (LinearMap.trace ℂ E B.toLinearMap) ≤ τ)
    (ht : 0 < t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    μ {ω | t < ‖∑ i, Y i ω‖} ≤ OperatorCompression.bernsteinTail R v τ t := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let Z : ι → Ω → Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
    fun i ω => matrixEquiv b (Y i ω)
  have hZ : ∀ i, AEStronglyMeasurable (Z i) μ :=
    fun i => (matrixCLM b).continuous.comp_aestronglyMeasurable (hY i)
  have hZH : ∀ i, ∀ᵐ ω ∂μ, (Z i ω).IsHermitian := by
    intro i
    filter_upwards [hsa i] with ω hω
    exact (hω.map (matrixEquiv b)).isHermitian
  have hZbound : ∀ i, ∀ᵐ ω ∂μ, OperatorBernstein.operatorNorm (Z i ω) ≤ R := by
    simpa only [Z, operatorNorm_matrixEquiv] using hbound
  have hZcenter : ∀ i, ∫ ω, Z i ω ∂μ = 0 := by
    intro i
    change (∫ ω, matrixCLM b (Y i ω) ∂μ) = 0
    rw [(matrixCLM b).integral_comp_comm (Integrable.of_bound (hY i) R (hbound i)),
      hcenter i, map_zero]
  let W : E →L[ℂ] E := ∑ i, ∫ ω, Y i ω * Y i ω ∂μ
  have hWmatrix : matrixEquiv b W = OperatorBernstein.variance μ Z := by
    unfold W OperatorBernstein.variance
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change matrixCLM b (∫ ω, Y i ω * Y i ω ∂μ) = _
    rw [← (matrixCLM b).integral_comp_comm (integrable_square (hY i) (hbound i))]
    simp only [matrixCLM_apply, map_mul, Z]
  have hWsa : IsSelfAdjoint W := by
    apply IsSelfAdjoint.of_map (matrixEquiv b) (matrixEquiv b).injective
    rw [hWmatrix]
    exact (OperatorBernstein.variance_posSemidef hZH).isHermitian.isSelfAdjoint
  have hWq (x : E) : Complex.re ⟪x, W x⟫_ℂ = ∑ i, ∫ ω, ‖Y i ω x‖ ^ 2 ∂μ := by
    simp only [W, sum_apply, inner_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => re_inner_integral_square (hY i) (hbound i) (hsa i) x
  have hWnorm : ‖W‖ ≤ v := by
    apply norm_le_of_quadratic_bounds W hWsa hv.le
    · intro x
      rw [hWq]
      exact Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
    · simpa only [hWq] using hvariance
  have hWtrace : Complex.re (LinearMap.trace ℂ E W.toLinearMap) ≤ τ := by
    apply (OperatorCompression.re_trace_le_of_quadratic_le W B ?_).trans htrace
    simpa only [RCLike.re_to_complex, hWq] using hB
  have htail := OperatorBernstein.operatorBernstein_of_trace_le (Y := Z) (τ := τ)
    (hIndep.comp (fun _ => matrixCLM b) (fun _ => (matrixCLM b).measurable))
    hZ hZH hZcenter hZbound hR hv
    (by rw [← hWmatrix, operatorNorm_matrixEquiv]; exact hWnorm)
    (by rw [← hWmatrix, realTrace_matrixEquiv]; exact hWtrace) ht hthreshold
  have hevent : {ω | t < OperatorBernstein.operatorNorm (∑ i, Z i ω)} =
      {ω | t < ‖∑ i, Y i ω‖} := by
    ext ω
    simp only [Z, ← map_sum, operatorNorm_matrixEquiv]
  rw [hevent] at htail
  have h := ENNReal.ofReal_le_ofReal htail
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _),
    OperatorBernstein.tailBound, OperatorCompression.bernsteinTail] using h

end JanetCartan.HilbertOperatorBernstein
