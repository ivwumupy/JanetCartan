module

public import JanetCartan.Iteration.PhysicalSampling.Kernel

/-!
# A fixed carrier extension without changing the sampled scalar row

The common event requires a kernel bound at all parameter points. A fixed unit
carrier cutoff may be inserted into the global scalar kernel when it is one on
the support of the original sampling weight. The identities below hold even at
zero-weight labels and preserve the original kernels, columns and annular rows
exactly after weighting. No division by weights and no new sample is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.PhysicalSampling

open SamplingKernelBounds Sampling RawInputPartition

variable {P : Type*} [TopologicalSpace P] {n : ℕ}

/-- Insert only a fixed unit-bounded parameter cutoff; phase, physical support,
angular/high mask and radial amplitude remain the original ones. -/
def parameterCutKernel (D : BandKernelData P n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1) : BandKernelData P n where
  phase := D.phase
  phase_continuous := D.phase_continuous
  mask := D.mask
  mask_continuous := D.mask_continuous
  amplitude := fun q ↦ (β q.1.1 : ℂ) • D.amplitude q
  amplitude_continuous := (Complex.continuous_ofReal.comp
    (hβ.comp (continuous_fst.comp continuous_fst))).smul D.amplitude_continuous
  physicalSupport := D.physicalSupport
  physicalSupport_compact := D.physicalSupport_compact
  amplitude_eq_zero := by
    intro p η x hx
    simp only [D.amplitude_eq_zero p η x hx, smul_zero]
  amplitudeBound := D.amplitudeBound
  amplitudeBound_nonneg := D.amplitudeBound_nonneg
  amplitude_le := by
    intro p η x
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hβone p) (norm_nonneg _)).trans
      (by simpa only [one_mul] using D.amplitude_le p η x)
  maskBound := D.maskBound
  maskBound_nonneg := D.maskBound_nonneg
  mask_le := D.mask_le

/-- The cutoff changes only the global extension outside the retained carrier
support, and introduces no new kernel normalization. -/
theorem parameterCutKernel_kernel (D : BandKernelData P n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1)
    (p : P) (η : Euclidean (n - 1)) (x : Euclidean n) :
    (parameterCutKernel D β hβ hβone).kernel p η x = (β p : ℂ) • D.kernel p η x := by
  simp only [BandKernelData.kernel, bandKernel, parameterCutKernel]
  rw [smul_comm]

/-- The fixed extension cutoff does not enlarge the squared-kernel constant. -/
theorem parameterCutKernel_squaredKernelConstant (D : BandKernelData P n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1) :
    (parameterCutKernel D β hβ hβone).squaredKernelConstant = D.squaredKernelConstant := rfl

/-- Exact physical L²-column identity, not only an almost-everywhere kernel
comparison (`new:eq:amplitude-test`). -/
theorem parameterCutKernel_column (D : BandKernelData P n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1)
    (p : P) (η : Euclidean (n - 1)) :
    (parameterCutKernel D β hβ hβone).column p η = (β p : ℂ) • D.column p η := by
  apply Lp.ext
  filter_upwards [(parameterCutKernel D β hβ hβone).column_coe p η,
    D.column_coe p η, Lp.coeFn_smul (β p : ℂ) (D.column p η)] with x hx hD hs
  rw [hx, hs]
  change (parameterCutKernel D β hβ hβone).kernel p η x = (β p : ℂ) • (D.column p η) x
  rw [hD]
  exact parameterCutKernel_kernel D β hβ hβone p η x

variable [FirstCountableTopology P] [LocallyCompactSpace P]

/-- Each original annular operator is multiplied by the same carrier scalar;
both sharp refinements are retained unchanged. -/
theorem parameterCutKernel_operator (D : BandKernelData P n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1) (R : ℝ) (p : P) :
    (parameterCutKernel D β hβ hβone).operator R p = (β p : ℂ) • D.operator R p := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [BandKernelData.operator_apply, parameterCutKernel_column, smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  exact smul_comm _ _ _

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- The actual weighted kernel is unchanged, including every zero-weight
label. This is the interface for the original sample×annular-input realization. -/
theorem parameterCutKernel_weighted_kernel (D : BandKernelData P n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1)
    (w : P → ℝ) (hplateau : ∀ p, w p ≠ 0 → β p = 1)
    (p : P) (η : Euclidean (n - 1)) (x : Euclidean n) :
    (Real.sqrt (w p) : ℂ) • (parameterCutKernel D β hβ hβone).kernel p η x =
      (Real.sqrt (w p) : ℂ) • D.kernel p η x := by
  by_cases hw : w p = 0
  · simp only [hw, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
  · rw [parameterCutKernel_kernel, hplateau p hw, Complex.ofReal_one, one_smul]

/-- The original weighted annular row is exactly unchanged, with no inverse
weight and no cardinality-dependent comparison. -/
theorem parameterCutKernel_weighted_operator (D : BandKernelData P n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1)
    (w : P → ℝ) (hplateau : ∀ p, w p ≠ 0 → β p = 1) (R : ℝ) (p : P) :
    (Real.sqrt (w p) : ℂ) • (parameterCutKernel D β hβ hβone).operator R p =
      (Real.sqrt (w p) : ℂ) • D.operator R p := by
  by_cases hw : w p = 0
  · apply ContinuousLinearMap.ext
    intro f
    simp only [hw, Real.sqrt_zero, Complex.ofReal_zero, smul_apply, zero_smul]
  · rw [parameterCutKernel_operator, hplateau p hw, Complex.ofReal_one, one_smul]

/-- The same weighted continuum normal integrand, including zero patch weight.
Thus the fixed parameter extension cannot change the original continuum mean. -/
theorem parameterCutKernel_weighted_normal (D : BandKernelData P n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1)
    (w : P → ℝ) (hplateau : ∀ p, w p ≠ 0 → β p = 1) (R : ℝ) (p : P) :
    w p • atomNormal ((parameterCutKernel D β hβ hβone).operator R p) =
      w p • atomNormal (D.operator R p) := by
  by_cases hw : w p = 0
  · simp only [hw, zero_smul]
  · rw [parameterCutKernel_operator, hplateau p hw, Complex.ofReal_one, one_smul]

/-- A sharp bound needed only on the fixed carrier support becomes the
all-parameter bound required by the original Bernstein event. Zero extension
points are handled directly, not by an artificial inverse parameter weight. -/
theorem parameterCutKernel_operator_sq_le
    (D : BandKernelData P n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1)
    (R B : ℝ) (hB : 0 ≤ B) (p : P)
    (hlocal : β p ≠ 0 → ‖D.operator R p‖ ^ 2 ≤ B) :
    ‖(parameterCutKernel D β hβ hβone).operator R p‖ ^ 2 ≤ B := by
  rw [parameterCutKernel_operator]
  by_cases hp : β p = 0
  · have hz : (0 : ℂ) • D.operator R p = 0 := by
      apply ContinuousLinearMap.ext
      intro f
      simp only [smul_apply, zero_smul, zero_apply]
    rw [hp, Complex.ofReal_zero, hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact hB
  · apply (pow_le_pow_left₀ (norm_nonneg _) ?_ 2).trans (hlocal hp)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hβone p) (norm_nonneg _)).trans_eq (one_mul _)

/-- The same fixed scalar multiplies every grouped prefix. Both original sharp
refinements and all physical inputs remain unchanged. -/
theorem parameterCutKernel_refinedKernelPrefix {J : ℕ}
    (D : BandKernelData (Fin J × P) n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1) (L : ℕ) (p : P) :
    refinedKernelPrefix
      (parameterCutKernel D (fun q ↦ β q.2) (hβ.comp continuous_snd) (fun q ↦ hβone q.2)) L p =
        (β p : ℂ) • refinedKernelPrefix D L p := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [refinedKernelPrefix, prefixRow_apply,
    parameterCutKernel_operator, smul_apply, Finset.smul_sum]

/-- Weighted grouped normals, hence every original continuum and sampled
prefix, are unaffected by the global carrier extension. -/
theorem parameterCutKernel_weighted_prefix_normal {J : ℕ}
    (D : BandKernelData (Fin J × P) n) (β : P → ℝ)
    (hβ : Continuous β) (hβone : ∀ p, |β p| ≤ 1)
    (w : P → ℝ) (hplateau : ∀ p, w p ≠ 0 → β p = 1) (L : ℕ) (p : P) :
    w p • atomNormal (refinedKernelPrefix
      (parameterCutKernel D (fun q ↦ β q.2) (hβ.comp continuous_snd) (fun q ↦ hβone q.2)) L p) =
        w p • atomNormal (refinedKernelPrefix D L p) := by
  by_cases hw : w p = 0
  · simp only [hw, zero_smul]
  · rw [parameterCutKernel_refinedKernelPrefix D β hβ hβone, hplateau p hw,
      Complex.ofReal_one, one_smul]

end JanetCartan.PhysicalSampling
