module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.RemainderBounds

/-!
# The exact frequency-cutoff defect

Compact frequency regularization in `app:ch_regular_base:eq:actual-pdo-remainder`
introduces a derivative of the frequency cutoff. This module retains that term
in the literal kernel identity and bounds it by one inverse frequency radius.
No decay or integrability of the unregularized amplitude is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform

namespace JanetCartan.Pseudodifferential

universe u v
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the term where frequency
integration by parts differentiates the frequency cutoff. -/
def frequencyCutoffError {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (χ : V → ℝ) (B : V → V →L[ℝ] F) (ξ : V) : F :=
  (2 * Real.pi * Complex.I)⁻¹ • ∑ j, (fderiv ℝ χ ξ (b j)) • B ξ (b j)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the exact product rule retains
both the cut-off remainder and the derivative of the frequency cutoff. -/
theorem normalizedFrequencyDivergence_smul {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (χ : V → ℝ) (B : V → V →L[ℝ] F) (ξ : V)
    (hχ : DifferentiableAt ℝ χ ξ) (hB : DifferentiableAt ℝ B ξ) :
    normalizedFrequencyDivergence b (fun η ↦ χ η • B η) ξ =
      χ ξ • normalizedFrequencyDivergence b B ξ + frequencyCutoffError b χ B ξ := by
  simp only [normalizedFrequencyDivergence, frequencyDivergence, frequencyCutoffError,
    fderiv_fun_smul hχ hB, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, Finset.sum_add_distrib,
    smul_add, ← Finset.smul_sum]
  rw [smul_comm]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the cutoff defect costs one
cutoff derivative, with the `2π` normalization and dimension explicit. -/
theorem norm_frequencyCutoffError_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (χ : V → ℝ) (B : V → V →L[ℝ] F) (ξ : V) :
    ‖frequencyCutoffError b χ B ξ‖ ≤
      ‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * ‖fderiv ℝ χ ξ‖ * ‖B ξ‖ := by
  rw [frequencyCutoffError, norm_smul]
  calc
    _ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ * ∑ j, ‖(fderiv ℝ χ ξ (b j)) • B ξ (b j)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ * ∑ _j : ι, ‖fderiv ℝ χ ξ‖ * ‖B ξ‖ := by
      gcongr with j
      rw [norm_smul]
      exact mul_le_mul (by simpa using (fderiv ℝ χ ξ).le_opNorm (b j))
        (by simpa using (B ξ).le_opNorm (b j)) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: inverse-radius gain from the
rescaled frequency cutoff. This bound does not require frequency decay of `B`. -/
theorem norm_frequencyCutoffError_rescaled_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (χ : V → ℝ) (B : V → V →L[ℝ] F)
    (hχ : Differentiable ℝ χ) (R : ℝ) (hR : 0 < R) (D : ℝ)
    (hD : ∀ ξ, ‖fderiv ℝ χ ξ‖ ≤ D) (ξ : V) :
    ‖frequencyCutoffError b (fun η ↦ χ (R⁻¹ • η)) B ξ‖ ≤
      (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * D / R) * ‖B ξ‖ := by
  have hd : fderiv ℝ (fun η ↦ χ (R⁻¹ • η)) ξ = R⁻¹ • fderiv ℝ χ (R⁻¹ • ξ) := by
    have hcomp : fderiv ℝ (fun η ↦ χ (R⁻¹ • η)) ξ =
        (fderiv ℝ χ (R⁻¹ • ξ)).comp (R⁻¹ • ContinuousLinearMap.id ℝ V) :=
      ((hχ _).hasFDerivAt.comp ξ ((hasFDerivAt_id ξ).const_smul R⁻¹)).fderiv
    rw [hcomp]
    ext v
    simp
  apply (norm_frequencyCutoffError_le b _ B ξ).trans
  rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  calc
    _ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * (R⁻¹ * D) * ‖B ξ‖ := by gcongr; exact hD _
    _ = _ := by ring

variable [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: a frequency multiplier passes
through the explicit source Taylor integral. -/
theorem fullTaylorCoefficient_frequency_smul (c : V → V → V → F)
    (β χ : V → ℝ) (x y ξ : V) (hc : Differentiable ℝ (fun z ↦ c x z ξ)) :
    fullTaylorCoefficient (fun x y ξ ↦ χ ξ • c x y ξ) β x y ξ =
      χ ξ • fullTaylorCoefficient c β x y ξ := by
  simp only [fullTaylorCoefficient, sourceTaylorCoefficient]
  simp_rw [fderiv_fun_const_smul (hc _) (χ ξ)]
  rw [intervalIntegral.integral_smul, smul_comm]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the full remainder of a
frequency-regularized amplitude includes the explicit cutoff defect. -/
theorem diagonalRemainderAmplitude_frequency_smul {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (c : V → V → V → F) (β χ : V → ℝ)
    (x y ξ : V) (hc : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2))
    (hχ : DifferentiableAt ℝ χ ξ) :
    diagonalRemainderAmplitude b (fun x y ξ ↦ χ ξ • c x y ξ) β x y ξ =
      χ ξ • diagonalRemainderAmplitude b c β x y ξ +
        frequencyCutoffError b χ (fullTaylorCoefficient c β x y) ξ := by
  have heq : fullTaylorCoefficient (fun x y ξ ↦ χ ξ • c x y ξ) β x y =
      fun ξ ↦ χ ξ • fullTaylorCoefficient c β x y ξ := by
    funext η
    exact fullTaylorCoefficient_frequency_smul c β χ x y η
      ((hc.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp))
  unfold diagonalRemainderAmplitude
  rw [heq]
  exact normalizedFrequencyDivergence_smul b χ _ ξ hχ
    ((contDiff_fullTaylorCoefficient_frequency c β x y hc).differentiable (by simp) ξ)

variable [MeasurableSpace V] [BorelSpace V] [CompleteSpace F]
local instance : ContinuousENorm (V →L[ℝ] V →L[ℝ] F) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (V →L[ℝ] V →L[ℝ] F) inferInstance).toContinuousENorm

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: compact frequency cutoff
makes the actual diagonal identity valid without any integrability assumptions
on the original symbol. The remainder here is that of the cut-off amplitude. -/
theorem amplitudeKernel_frequency_smul_eq_diagonal_add_remainder
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β χ : V → ℝ) (x y : V)
    (hc : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2))
    (hβ : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    amplitudeKernel (fun x y ξ ↦ χ ξ • c x y ξ) x y =
      amplitudeKernel (diagonalAmplitude (fun x y ξ ↦ χ ξ • c x y ξ) β) x y +
      amplitudeKernel (diagonalRemainderAmplitude b (fun x y ξ ↦ χ ξ • c x y ξ) β) x y := by
  let cχ := fun x y ξ ↦ χ ξ • c x y ξ
  have hcχ : ContDiff ℝ ∞ (fun p : V × V ↦ cχ x p.1 p.2) :=
    (hχ.comp contDiff_snd).smul hc
  have hB : ContDiff ℝ ∞ (fullTaylorCoefficient cχ β x y) :=
    contDiff_fullTaylorCoefficient_frequency cχ β x y hcχ
  have heq : fullTaylorCoefficient cχ β x y =
      fun ξ ↦ χ ξ • fullTaylorCoefficient c β x y ξ := by
    funext ξ
    exact fullTaylorCoefficient_frequency_smul c β χ x y ξ
      ((hc.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp))
  have hsupp : HasCompactSupport (fullTaylorCoefficient cχ β x y) := by
    rw [heq]
    exact hχc.smul_right
  apply amplitudeKernel_eq_diagonal_add_remainder_of_contDiff b cχ β x y hcχ
  · intro ξ z hz
    apply hβ ξ z
    intro hzero
    exact hz (by simp [cχ, hzero])
  · apply Continuous.integrable_of_hasCompactSupport
    · exact ((hχ.continuous.smul
        (hc.continuous.comp (continuous_const.prodMk continuous_id))).const_smul (β y))
    · exact HasCompactSupport.smul_left hχc.smul_right
  · exact hB.continuous.integrable_of_hasCompactSupport hsupp
  · exact (hB.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hsupp.fderiv ℝ)


omit [CompleteSpace F] in
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the cutoff defect is absolutely
integrable for a compact smooth cutoff, even when the coefficient has no decay. -/
theorem integrable_frequencyCutoffError {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (χ : V → ℝ) (B : V → V →L[ℝ] F)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hB : Continuous B) :
    Integrable (frequencyCutoffError b χ B) := by
  apply Integrable.smul
  apply integrable_finsetSum
  intro j _
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).smul
      (hB.clm_apply continuous_const)
  · exact (hχc.fderiv_apply ℝ (b j)).smul_right

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the literal regularized kernel
is the regularized diagonal plus the regularized uncut remainder and the exact
frequency-cutoff defect. All frequency integrability follows from compact support. -/
theorem amplitudeKernel_frequency_smul_eq_diagonal_add_remainder_add_error
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β χ : V → ℝ) (x y : V)
    (hc : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2))
    (hβ : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    amplitudeKernel (fun x y ξ ↦ χ ξ • c x y ξ) x y =
      amplitudeKernel (fun x y ξ ↦ χ ξ • diagonalAmplitude c β x y ξ) x y +
      amplitudeKernel (fun x y ξ ↦ χ ξ • diagonalRemainderAmplitude b c β x y ξ) x y +
      amplitudeKernel (fun x y ξ ↦ frequencyCutoffError b χ
        (fullTaylorCoefficient c β x y) ξ) x y := by
  have hB := contDiff_fullTaylorCoefficient_frequency c β x y hc
  have hr : Continuous (diagonalRemainderAmplitude b c β x y) := by
    apply Continuous.const_smul
    apply continuous_finsetSum
    intro j _
    exact ((hB.continuous_fderiv (by simp)).clm_apply continuous_const).clm_apply
      continuous_const
  have hir : Integrable (fun ξ ↦ χ ξ • diagonalRemainderAmplitude b c β x y ξ) :=
    (hχ.continuous.smul hr).integrable_of_hasCompactSupport hχc.smul_right
  have hie := integrable_frequencyCutoffError b χ (fullTaylorCoefficient c β x y)
    (hχ.of_le (by simp)) hχc hB.continuous
  rw [amplitudeKernel_frequency_smul_eq_diagonal_add_remainder b c β χ x y hc hβ hχ hχc]
  have hdiag : diagonalAmplitude (fun x y ξ ↦ χ ξ • c x y ξ) β =
      (fun x y ξ ↦ χ ξ • diagonalAmplitude c β x y ξ) := by
    funext x y ξ
    exact smul_comm _ _ _
  rw [hdiag, add_assoc]
  congr 1
  simp only [amplitudeKernel, Real.fourier_eq]
  simp_rw [diagonalRemainderAmplitude_frequency_smul b c β χ x y _ hc
    (hχ.differentiable (by simp) _), smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff (y - x)).mpr hir)
    ((Real.fourierIntegral_convergent_iff (y - x)).mpr hie)

end JanetCartan.Pseudodifferential
