module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.Pairing
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.PhysicalFrequency

/-!
# Physical negative norms of real components

The finite-dimensional real version of the physical-frequency conversion needed
by `app:ch_regular:eq:inverse-remainder`. These are the same orthonormal
components and the same Lebesgue measure used in the local pairing. Both the
unnormalized transform and the paper's additional `(2π)^(-n)` factor are kept.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ArbitraryAccuracy

open LocalSobolev Pseudodifferential JanetCartan.Localization

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι]

/-- The physical negative norm in orthonormal real components, for the source
of `app:ch_regular:eq:inverse-remainder`. It is defined for every L² class. -/
def componentPhysicalNegativeNorm (b : OrthonormalBasis ι ℝ F) (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) : ℝ :=
  Real.sqrt (∑ i, (fourierWeightedL2Norm volume (-(N : ℝ))
    (physicalL2Fourier (realComponentL2 b i u))) ^ 2)

/-- The paper-normalized physical negative norm in real components, for
`app:ch_regular:eq:inverse-remainder`. -/
def componentPaperNegativeNorm (b : OrthonormalBasis ι ℝ F) (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) : ℝ :=
  Real.sqrt (∑ i, (fourierWeightedL2Norm volume (-(N : ℝ))
    (fun ξ ↦ ((2 * Real.pi) ^ n)⁻¹ • physicalL2Fourier (realComponentL2 b i u) ξ)) ^ 2)

/-- Every component of an L² datum has finite physical negative energy,
with no L¹ assumption (`app:ch_regular_base:eq:negative-duality`). -/
theorem integrable_component_physical_negative_energy
    (b : OrthonormalBasis ι ℝ F) (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) (i : ι) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-(N : ℝ)) *
      ‖physicalL2Fourier (realComponentL2 b i u) ξ‖ ^ 2) :=
  integrable_negative_energy_physicalL2Fourier N _

/-- The normalized components also have finite negative energy
(`app:ch_regular_base:eq:negative-duality`). -/
theorem integrable_component_paper_negative_energy
    (b : OrthonormalBasis ι ℝ F) (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) (i : ι) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-(N : ℝ)) *
      ‖((2 * Real.pi) ^ n)⁻¹ • physicalL2Fourier (realComponentL2 b i u) ξ‖ ^ 2) :=
  integrable_negative_energy_paperL2Fourier N _

private theorem sqrt_sum_sq_le {f g : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ c * g i) :
    Real.sqrt (∑ i, f i ^ 2) ≤ c * Real.sqrt (∑ i, g i ^ 2) := by
  calc
    _ ≤ Real.sqrt (∑ i, (c * g i) ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (hf i) (h i) 2
    _ = c * Real.sqrt (∑ i, g i ^ 2) := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- The component norm conversion with the physical Jacobian retained:
`(2π)^(N-n/2)` controls the shared negative norm
(`app:ch_regular:eq:inverse-remainder`). -/
theorem componentFourierSobolevNorm_negative_le_physical
    (b : OrthonormalBasis ι ℝ F) (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) :
    componentFourierSobolevNorm b (-(N : ℝ)) u ≤
      (2 * Real.pi) ^ ((N : ℝ) - (n : ℝ) / 2) * componentPhysicalNegativeNorm b N u := by
  apply sqrt_sum_sq_le (physical_negative_comparison_constant_pos n N).le
    (fun i ↦ fourierSobolevNorm_nonneg _ _)
  exact fun i ↦ fourierSobolevNorm_negative_le_physicalL2Fourier N _

/-- The component norm conversion in the paper's normalization, with factor
`(2π)^(N+n/2)` (`app:ch_regular:eq:inverse-remainder`). -/
theorem componentFourierSobolevNorm_negative_le_paper
    (b : OrthonormalBasis ι ℝ F) (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) F 2) :
    componentFourierSobolevNorm b (-(N : ℝ)) u ≤
      (2 * Real.pi) ^ ((N : ℝ) + (n : ℝ) / 2) * componentPaperNegativeNorm b N u := by
  apply sqrt_sum_sq_le (paper_negative_comparison_constant_pos n N).le
    (fun i ↦ fourierSobolevNorm_nonneg _ _)
  exact fun i ↦ fourierSobolevNorm_negative_le_paperL2Fourier N _

/-- Projection and zero extension agree as actual L² classes, preserving the
source identification in `app:ch_regular_base:eq:negative-duality`. -/
theorem realComponentL2_zeroExtend (b : OrthonormalBasis ι ℝ F) (i : ι)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : MeasurableSet W) (h : LocalL2 W F) :
    realComponentL2 b i (SmallSupport.zeroExtend hW h) =
      SmallSupport.zeroExtend hW (realComponentL2 b i h) := by
  apply Lp.ext
  have he := (ae_restrict_iff' hW).mp (realComponentL2_coeFn b i h)
  filter_upwards [realComponentL2_coeFn b i (SmallSupport.zeroExtend hW h),
    SmallSupport.zeroExtend_coeFn hW h,
    SmallSupport.zeroExtend_coeFn hW (realComponentL2 b i h), he] with x hx hx' hx'' he
  rw [hx, hx', hx'']
  by_cases hxW : x ∈ W
  · simp only [indicator_of_mem hxW, he hxW]
  · simp [hxW]

/-- The real local pairing expressed in the unnormalized physical convention
(`app:ch_regular_base:eq:negative-duality`). -/
theorem abs_inner_le_physicalNegativeNorm_mul_restrictionSobolevNorm
    (b : OrthonormalBasis ι ℝ F) {W : Set (EuclideanSpace ℝ (Fin n))}
    (hW : MeasurableSet W) (N : ℕ) (h v : LocalL2 W F)
    (hv : MemRestrictionSobolev W N v) :
    |inner ℝ h v| ≤ (localDualityConstant n N b *
      (2 * Real.pi) ^ ((N : ℝ) - (n : ℝ) / 2)) *
      componentPhysicalNegativeNorm b N (SmallSupport.zeroExtend hW h) *
        restrictionSobolevNorm W N v := by
  apply (abs_inner_le_negativeNorm_mul_restrictionSobolevNorm b hW N h v hv).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (componentFourierSobolevNorm_negative_le_physical b N (SmallSupport.zeroExtend hW h))
      (localDualityConstant_pos n N b).le) restrictionSobolevNorm_nonneg

/-- The real local pairing in the paper's physical normalization
(`app:ch_regular_base:eq:negative-duality`). -/
theorem abs_inner_le_paperNegativeNorm_mul_restrictionSobolevNorm
    (b : OrthonormalBasis ι ℝ F) {W : Set (EuclideanSpace ℝ (Fin n))}
    (hW : MeasurableSet W) (N : ℕ) (h v : LocalL2 W F)
    (hv : MemRestrictionSobolev W N v) :
    |inner ℝ h v| ≤ (localDualityConstant n N b *
      (2 * Real.pi) ^ ((N : ℝ) + (n : ℝ) / 2)) *
      componentPaperNegativeNorm b N (SmallSupport.zeroExtend hW h) *
        restrictionSobolevNorm W N v := by
  apply (abs_inner_le_negativeNorm_mul_restrictionSobolevNorm b hW N h v hv).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (componentFourierSobolevNorm_negative_le_paper b N (SmallSupport.zeroExtend hW h))
      (localDualityConstant_pos n N b).le) restrictionSobolevNorm_nonneg

end JanetCartan.ArbitraryAccuracy
