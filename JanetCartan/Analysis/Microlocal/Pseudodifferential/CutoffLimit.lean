module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Regularization
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The frequency-cutoff defect on Schwartz tests

For `app:ch_regular_base:eq:actual-pdo-remainder`, the derivative-of-cutoff
error vanishes against each Schwartz frequency test, even for coefficients
of polynomial growth. The quantitative bound is proportional to `R⁻¹`.
These tests concern frequency at fixed physical positions; identifying the
full physical distributional kernel still requires integration in those positions.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology

namespace JanetCartan.Pseudodifferential
universe u v
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: polynomial growth is sufficient
for the absolute integrability of the norm against a Schwartz frequency test. -/
theorem integrable_schwartz_norm_mul_of_polynomial_bound
    {G : Type*} [NormedAddCommGroup G] (B : V → G) (hB : Continuous B)
    (A : ℝ) (N : ℕ) (hbound : ∀ ξ, ‖B ξ‖ ≤ A * (1 + ‖ξ‖ ^ N))
    (ψ : 𝓢(V, ℂ)) : Integrable (fun ξ ↦ ‖ψ ξ‖ * ‖B ξ‖) := by
  have hi : Integrable (fun ξ ↦ A * (‖ψ ξ‖ + ‖ξ‖ ^ N * ‖ψ ξ‖)) :=
    (ψ.integrable.norm.add (ψ.integrable_pow_mul volume N)).const_mul A
  apply hi.mono' (ψ.continuous.norm.mul hB.norm).aestronglyMeasurable
  filter_upwards [] with ξ
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖ψ ξ‖ * (A * (1 + ‖ξ‖ ^ N)) :=
      mul_le_mul_of_nonneg_left (hbound ξ) (norm_nonneg _)
    _ = _ := by ring

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the integrated cutoff defect
has an explicit inverse-radius bound. Only the displayed weighted absolute
integrability is needed; no integrability of the untested coefficient is imposed. -/
theorem norm_integral_smul_frequencyCutoffError_rescaled_le
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (χ : V → ℝ) (B : V → V →L[ℝ] F) (ψ : V → ℂ)
    (hχ : Differentiable ℝ χ) (R : ℝ) (hR : 0 < R) (D : ℝ)
    (hD : ∀ ξ, ‖fderiv ℝ χ ξ‖ ≤ D)
    (hint : Integrable (fun ξ ↦ ‖ψ ξ‖ * ‖B ξ‖)) :
    ‖∫ ξ, ψ ξ • frequencyCutoffError b (fun η ↦ χ (R⁻¹ • η)) B ξ‖ ≤
      (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * D / R) *
        ∫ ξ, ‖ψ ξ‖ * ‖B ξ‖ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hint.const_mul _)
  filter_upwards [] with ξ
  rw [norm_smul]
  calc
    _ ≤ ‖ψ ξ‖ * ((‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * D / R) * ‖B ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_frequencyCutoffError_rescaled_le b χ B hχ R hR D hD ξ) (norm_nonneg _)
    _ = _ := by ring

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the tested cutoff defect
vanishes as the frequency radius tends to infinity. The test may be any function
satisfying the stated weighted integrability condition. -/
theorem tendsto_integral_smul_frequencyCutoffError_rescaled
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (χ : V → ℝ) (B : V → V →L[ℝ] F) (ψ : V → ℂ)
    (hχ : Differentiable ℝ χ) (D : ℝ) (hD : ∀ ξ, ‖fderiv ℝ χ ξ‖ ≤ D)
    (hint : Integrable (fun ξ ↦ ‖ψ ξ‖ * ‖B ξ‖)) :
    Tendsto (fun R : ℝ ↦ ∫ ξ, ψ ξ •
      frequencyCutoffError b (fun η ↦ χ (R⁻¹ • η)) B ξ) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun R : ℝ ↦
    (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * D / R) *
      ∫ ξ, ‖ψ ξ‖ * ‖B ξ‖)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_integral_smul_frequencyCutoffError_rescaled_le b χ B ψ hχ R hR D hD hint
  · simpa using (tendsto_const_nhds.div_atTop tendsto_id).mul_const
      (∫ ξ, ‖ψ ξ‖ * ‖B ξ‖)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: polynomially growing Taylor
coefficients have vanishing cutoff defects against every Schwartz frequency test. -/
theorem tendsto_schwartz_frequencyCutoffError_rescaled
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (χ : V → ℝ) (B : V → V →L[ℝ] F) (hχ : Differentiable ℝ χ)
    (D : ℝ) (hD : ∀ ξ, ‖fderiv ℝ χ ξ‖ ≤ D) (hB : Continuous B)
    (A : ℝ) (N : ℕ) (hbound : ∀ ξ, ‖B ξ‖ ≤ A * (1 + ‖ξ‖ ^ N)) (ψ : 𝓢(V, ℂ)) :
    Tendsto (fun R : ℝ ↦ ∫ ξ, ψ ξ •
      frequencyCutoffError b (fun η ↦ χ (R⁻¹ • η)) B ξ) atTop (𝓝 0) :=
  tendsto_integral_smul_frequencyCutoffError_rescaled b χ B ψ hχ D hD
    (integrable_schwartz_norm_mul_of_polynomial_bound B hB A N hbound ψ)

end JanetCartan.Pseudodifferential
