module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.FullOperator

/-!
# The cutoff defect after physical source integration

For `app:ch_regular_base:eq:actual-pdo-remainder`, integrating against a physical
source test preserves the explicit cutoff defect. The resulting operator error
is `O(R⁻¹)` provided the source Fourier transform of the Taylor coefficient is
integrable. `SourceDecay` supplies finite derivative criteria for that input.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace Topology ContDiff

namespace JanetCartan.Pseudodifferential
universe u v
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the frequency-cutoff defect
commutes exactly with integration against the physical source test. -/
theorem sourceAmplitudeTransform_frequencyCutoffError
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : V → V → V → V →L[ℝ] F) (u : V → ℂ) (χ : V → ℝ) (x ξ : V)
    (hi : Integrable (fun y ↦ u y • B x y ξ)) :
    sourceAmplitudeTransform (fun x y ξ ↦ frequencyCutoffError b χ (B x y) ξ) u x ξ =
      frequencyCutoffError b χ (sourceAmplitudeTransform B u x) ξ := by
  have hf : Integrable (fun y ↦ Real.fourierChar (-⟪y, ξ⟫) • (u y • B x y ξ)) :=
    (Real.fourierIntegral_convergent_iff ξ).mpr hi
  have heval (j : ι) : Integrable (fun y ↦
      Real.fourierChar (-⟪y, ξ⟫) • (u y • B x y ξ (b j))) := by
    simpa only [Circle.smul_def, smul_apply] using
      hf.apply_continuousLinearMap (b j)
  simp only [sourceAmplitudeTransform, Real.fourier_eq, frequencyCutoffError]
  simp_rw [smul_comm (u _) ((2 * Real.pi * Complex.I)⁻¹),
    smul_comm (Real.fourierChar _) ((2 * Real.pi * Complex.I)⁻¹), integral_smul]
  congr 1
  simp_rw [Finset.smul_sum, smul_comm (u _) ((fderiv ℝ χ ξ) (b _)),
    smul_comm (Real.fourierChar _) ((fderiv ℝ χ ξ) (b _))]
  rw [integral_finsetSum]
  swap
  · intro j _
    exact (heval j).smul _
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_smul, ContinuousLinearMap.integral_apply hf]
  simp only [Circle.smul_def, smul_apply]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the actual source-integrated
operator error has an inverse-radius bound, using the full Taylor coefficient's
source Fourier transform, rather than a test at fixed physical positions. -/
theorem norm_fullAmplitudeOperator_frequencyCutoffError_rescaled_le
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : V → V → V → V →L[ℝ] F) (u : V → ℂ) (x : V)
    (hsource : ∀ ξ, Integrable (fun y ↦ u y • B x y ξ))
    (hi : Integrable (sourceAmplitudeTransform B u x))
    (χ : V → ℝ) (hχ : Differentiable ℝ χ) (R : ℝ) (hR : 0 < R)
    (D : ℝ) (hD : ∀ ξ, ‖fderiv ℝ χ ξ‖ ≤ D) :
    ‖fullAmplitudeOperator (fun x y ξ ↦
      frequencyCutoffError b (fun η ↦ χ (R⁻¹ • η)) (B x y) ξ) u x‖ ≤
      (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * D / R) *
        ∫ ξ, ‖sourceAmplitudeTransform B u x ξ‖ := by
  simp only [fullAmplitudeOperator, Real.fourierInv_eq]
  simp_rw [sourceAmplitudeTransform_frequencyCutoffError b B u _ x _ (hsource _)]
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hi.norm.const_mul _)
  filter_upwards [] with ξ
  rw [Circle.norm_smul]
  exact norm_frequencyCutoffError_rescaled_le b χ (sourceAmplitudeTransform B u x) hχ R hR D hD ξ

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the complete physical
source-tested cutoff defect tends to zero. -/
theorem tendsto_fullAmplitudeOperator_frequencyCutoffError_rescaled
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : V → V → V → V →L[ℝ] F) (u : V → ℂ) (x : V)
    (hsource : ∀ ξ, Integrable (fun y ↦ u y • B x y ξ))
    (hi : Integrable (sourceAmplitudeTransform B u x))
    (χ : V → ℝ) (hχ : Differentiable ℝ χ)
    (D : ℝ) (hD : ∀ ξ, ‖fderiv ℝ χ ξ‖ ≤ D) :
    Tendsto (fun R : ℝ ↦ fullAmplitudeOperator (fun x y ξ ↦
      frequencyCutoffError b (fun η ↦ χ (R⁻¹ • η)) (B x y) ξ) u x) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun R : ℝ ↦
    (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * D / R) *
      ∫ ξ, ‖sourceAmplitudeTransform B u x ξ‖)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_fullAmplitudeOperator_frequencyCutoffError_rescaled_le b B u x hsource hi χ hχ R hR D hD
  · simpa using (tendsto_const_nhds.div_atTop tendsto_id).mul_const
      (∫ ξ, ‖sourceAmplitudeTransform B u x ξ‖)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: a finite source-derivative
budget discharges the convergence assumptions for the physically tested defect.
The derivative reserve is explicit and independent of the cutoff radius. -/
theorem tendsto_fullAmplitudeOperator_frequencyCutoffError_of_derivativeMass
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : V → V → V → V →L[ℝ] F) (u : V → ℂ) (x : V)
    (hB : Continuous (fun p : V × V ↦ B x p.2 p.1))
    (hu : Continuous u) (huc : HasCompactSupport u) (m : ℕ)
    (hs : ∀ ξ, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun y ↦ u y • B x y ξ))
    (A : ℝ) (hA : ∀ ξ, sourceDerivativeMass (fun y ↦ u y • B x y ξ)
      (m + Module.finrank ℝ V + 1) ≤ A * (1 + ‖ξ‖) ^ m)
    (χ : V → ℝ) (hχ : Differentiable ℝ χ)
    (D : ℝ) (hD : ∀ ξ, ‖fderiv ℝ χ ξ‖ ≤ D) :
    Tendsto (fun R : ℝ ↦ fullAmplitudeOperator (fun x y ξ ↦
      frequencyCutoffError b (fun η ↦ χ (R⁻¹ • η)) (B x y) ξ) u x) atTop (𝓝 0) := by
  apply tendsto_fullAmplitudeOperator_frequencyCutoffError_rescaled b B u x _ _ χ hχ D hD
  · intro ξ
    exact (hs ξ).continuous.integrable_of_hasCompactSupport huc.smul_right
  · exact integrable_sourceFourier_of_compact_derivativeMass (fun ξ y ↦ u y • B x y ξ)
      ((hu.comp continuous_snd).smul hB) m _ (Nat.lt_succ_self _) hs
      (fun _ ↦ huc.smul_right) A hA

end JanetCartan.Pseudodifferential
