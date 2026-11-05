module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SourceDecay
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SymbolOperator

/-!
# Full amplitudes after source integration

The two-position operator for `app:ch_regular_base:thm:actual-calculus` is an
iterated integral, with source integration first. Finite source-derivative
budgets give its absolute frequency convergence. Frequency regularizations
converge to this same operator. Identifying the regularizations with the literal
physical kernels uses Fubini and retains both physical positions.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace Topology ContDiff SchwartzMap

namespace JanetCartan.Pseudodifferential
universe u v
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:thm:actual-calculus`: integrate a full amplitude against
the datum in its source position, keeping the output position and frequency. -/
def sourceAmplitudeTransform (c : V → V → V → F) (u : V → ℂ) (x ξ : V) : F :=
  𝓕 (fun y ↦ u y • c x y ξ) ξ

/-- `app:ch_regular_base:thm:actual-calculus`: the actual full-amplitude operator,
with source integration before the final inverse Fourier integral. -/
def fullAmplitudeOperator (c : V → V → V → F) (u : V → ℂ) (x : V) : F :=
  𝓕⁻ (sourceAmplitudeTransform c u x) x

/-- `app:ch_regular_base:thm:actual-calculus`: source-independent amplitudes
recover the previously constructed symbol operator. -/
theorem fullAmplitudeOperator_sourceIndependent [CompleteSpace F]
    (a : V → V → F) (u : 𝓢(V, ℂ)) (x : V) :
    fullAmplitudeOperator (fun x _y ξ ↦ a x ξ) u x = sourceIndependentOperator a u x := by
  unfold fullAmplitudeOperator sourceAmplitudeTransform sourceIndependentOperator
  have heq : (fun ξ ↦ 𝓕 (fun y ↦ u y • a x ξ) ξ) =
      (fun ξ ↦ (𝓕 u : 𝓢(V, ℂ)) ξ • a x ξ) := by
    funext ξ
    change 𝓕 (fun y ↦ u y • a x ξ) ξ = 𝓕 (u : V → ℂ) ξ • a x ξ
    simp only [Real.fourier_eq, Circle.smul_def, smul_smul, integral_smul_const]
    rfl
  rw [heq]

/-- `app:ch_regular_base:thm:actual-calculus`: explicit finite source-derivative
budgets suffice for convergence of the full-amplitude frequency integral. -/
theorem integrable_sourceAmplitudeTransform_of_derivativeMass
    (c : V → V → V → F) (u : V → ℂ) (x : V)
    (hc : Continuous (fun p : V × V ↦ u p.2 • c x p.2 p.1)) (m n : ℕ)
    (hn : m + Module.finrank ℝ V < n)
    (hs : ∀ ξ, ContDiff ℝ n (fun y ↦ u y • c x y ξ))
    (hi : ∀ ξ j, j ≤ n → Integrable (iteratedFDeriv ℝ j (fun y ↦ u y • c x y ξ)))
    (A : ℝ) (hA : ∀ ξ, sourceDerivativeMass (fun y ↦ u y • c x y ξ) n ≤
      A * (1 + ‖ξ‖) ^ m) : Integrable (sourceAmplitudeTransform c u x) :=
  integrable_sourceFourier_of_derivativeMass (fun ξ y ↦ u y • c x y ξ) hc m n hn hs hi A hA

/-- `app:ch_regular_base:thm:actual-calculus`: a frequency cutoff commutes with
source integration, without discarding the source dependence of the amplitude. -/
theorem sourceAmplitudeTransform_frequency_smul
    (c : V → V → V → F) (u : V → ℂ) (χ : V → ℝ) (x ξ : V) :
    sourceAmplitudeTransform (fun x y ξ ↦ χ ξ • c x y ξ) u x ξ =
      χ ξ • sourceAmplitudeTransform c u x ξ := by
  simp only [sourceAmplitudeTransform, Real.fourier_eq]
  simp_rw [smul_comm (u _) (χ ξ), smul_comm (Real.fourierChar _) (χ ξ)]
  rw [integral_smul]

/-- `app:ch_regular_base:thm:actual-calculus`: bounded frequency cutoffs converge
for the full two-position operator once source integration is integrable. The
preceding finite-derivative theorem supplies this hypothesis. -/
theorem tendsto_fullAmplitudeOperator_frequency_cutoff
    (c : V → V → V → F) (u : V → ℂ) (x : V)
    (hi : Integrable (sourceAmplitudeTransform c u x))
    (χ : V → ℝ) (hχ : Continuous χ) (hχ0 : χ 0 = 1)
    (C : ℝ) (hC : ∀ ξ, |χ ξ| ≤ C) :
    Tendsto (fun R : ℝ ↦ fullAmplitudeOperator
      (fun x y ξ ↦ χ (R⁻¹ • ξ) • c x y ξ) u x) atTop
        (𝓝 (fullAmplitudeOperator c u x)) := by
  simp only [fullAmplitudeOperator, Real.fourierInv_eq,
    sourceAmplitudeTransform_frequency_smul]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ξ ↦ C * ‖sourceAmplitudeTransform c u x ξ‖)
  · apply Eventually.of_forall
    intro R
    have hphase : Continuous (fun ξ : V ↦ Real.fourierChar ⟪ξ, x⟫) := by fun_prop
    exact hphase.aestronglyMeasurable.smul
      ((hχ.comp (continuous_const.smul continuous_id)).aestronglyMeasurable.smul
        hi.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro R
    filter_upwards [] with ξ
    simp only [Circle.norm_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · exact hi.norm.const_mul C
  · filter_upwards [] with ξ
    have hzero : Tendsto (fun R : ℝ ↦ R⁻¹ • ξ) atTop (𝓝 (0 : V)) := by
      simpa using (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).smul_const ξ
    have hlim : Tendsto (fun R : ℝ ↦ χ (R⁻¹ • ξ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [hχ0, Function.comp_def] using hχ.continuousAt.tendsto.comp hzero
    have hh : Tendsto (fun R : ℝ ↦ χ (R⁻¹ • ξ) • sourceAmplitudeTransform c u x ξ)
        atTop (𝓝 (sourceAmplitudeTransform c u x ξ)) := by
      have h := hlim.smul_const (sourceAmplitudeTransform c u x ξ)
      rw [one_smul] at h
      exact h
    exact (tendsto_const_nhds (x := Real.fourierChar ⟪ξ, x⟫)).smul hh

/-- `app:ch_regular_base:thm:actual-calculus`: Fubini identifies the full
source-first integral with the literal physical kernel whenever the unphased
joint amplitude times the datum is absolutely integrable. -/
theorem fullAmplitudeOperator_eq_integral_amplitudeKernel [CompleteSpace F]
    (c : V → V → V → F) (u : V → ℂ) (x : V)
    (hi : Integrable (fun p : V × V ↦ u p.2 • c x p.2 p.1)) :
    fullAmplitudeOperator c u x = ∫ y, u y • amplitudeKernel c x y := by
  let H : V × V → F := fun p ↦
    Real.fourierChar ⟪p.1, x⟫ • (Real.fourierChar (-⟪p.2, p.1⟫) • (u p.2 • c x p.2 p.1))
  have hH : Integrable H := by
    apply hi.norm.mono'
    · have h1 : Continuous (fun p : V × V ↦ Real.fourierChar ⟪p.1, x⟫) := by fun_prop
      have h2 : Continuous (fun p : V × V ↦ Real.fourierChar (-⟪p.2, p.1⟫)) := by fun_prop
      exact h1.aestronglyMeasurable.smul (h2.aestronglyMeasurable.smul hi.aestronglyMeasurable)
    · filter_upwards [] with p
      simp [H]
  simp only [fullAmplitudeOperator, sourceAmplitudeTransform, Real.fourierInv_eq,
    Real.fourier_eq, amplitudeKernel]
  simp_rw [Circle.smul_def, ← integral_smul]
  change (∫ ξ, ∫ y, H (ξ, y)) = _
  rw [integral_integral_swap hH]
  apply integral_congr_ae
  filter_upwards [] with y
  apply integral_congr_ae
  filter_upwards [] with ξ
  change H (ξ, y) = u y • (Real.fourierChar (-⟪ξ, y - x⟫) • c x y ξ)
  rw [smul_comm (u y)]
  simp only [H, ← mul_smul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [inner_sub_right, real_inner_comm]
  ring

/-- `app:ch_regular_base:thm:actual-calculus`: joint amplitude integrability
also gives integrability of the literal kernel against its physical test. -/
theorem integrable_amplitudeKernel_test [CompleteSpace F]
    (c : V → V → V → F) (u : V → ℂ) (x : V)
    (hi : Integrable (fun p : V × V ↦ u p.2 • c x p.2 p.1)) :
    Integrable (fun y ↦ u y • amplitudeKernel c x y) := by
  have hH : Integrable (fun p : V × V ↦
      u p.2 • (Real.fourierChar (-⟪p.1, p.2 - x⟫) • c x p.2 p.1)) := by
    have hphase : Continuous (fun p : V × V ↦ Real.fourierChar (-⟪p.1, p.2 - x⟫)) := by fun_prop
    have hsm := hphase.aestronglyMeasurable.smul hi.aestronglyMeasurable
    change AEStronglyMeasurable (fun p : V × V ↦
      Real.fourierChar (-⟪p.1, p.2 - x⟫) • (u p.2 • c x p.2 p.1)) at hsm
    simp_rw [smul_comm (Real.fourierChar _)] at hsm
    apply hi.norm.mono' hsm
    filter_upwards [] with p
    simp only [norm_smul, Circle.norm_smul]
    exact le_rfl
  have h := hH.integral_prod_right
  simpa only [amplitudeKernel, Real.fourier_eq, integral_smul] using h

/-- `app:ch_regular_base:thm:actual-calculus`: compact frequency regularization
and compact physical test support ensure joint absolute integrability. -/
theorem integrable_frequency_cutoff_amplitude_test
    (c : V → V → V → F) (u : V → ℂ) (χ : V → ℝ) (x : V)
    (hc : Continuous (fun p : V × V ↦ c x p.2 p.1))
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun p : V × V ↦ u p.2 • (χ p.1 • c x p.2 p.1)) := by
  apply ((hu.comp continuous_snd).smul ((hχ.comp continuous_fst).smul hc)).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (hχc.isCompact.prod huc.isCompact)
  intro p hp
  by_cases hξ : p.1 ∈ tsupport χ
  · have hy : p.2 ∉ tsupport u := fun hy ↦ hp ⟨hξ, hy⟩
    simp [image_eq_zero_of_notMem_tsupport hy]
  · simp [image_eq_zero_of_notMem_tsupport hξ]

/-- `app:ch_regular_base:thm:actual-calculus`: the literal regularized physical
kernels converge on compact source tests to the full source-first operator. -/
theorem tendsto_integral_full_amplitudeKernel_frequency_cutoff [CompleteSpace F]
    (c : V → V → V → F) (u : V → ℂ) (x : V)
    (hc : Continuous (fun p : V × V ↦ c x p.2 p.1))
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hi : Integrable (sourceAmplitudeTransform c u x))
    (χ : V → ℝ) (hχ : Continuous χ) (hχ0 : χ 0 = 1) (hχc : HasCompactSupport χ)
    (C : ℝ) (hC : ∀ ξ, |χ ξ| ≤ C) :
    Tendsto (fun R : ℝ ↦ ∫ y, u y •
      amplitudeKernel (fun x y ξ ↦ χ (R⁻¹ • ξ) • c x y ξ) x y) atTop
        (𝓝 (fullAmplitudeOperator c u x)) := by
  apply (tendsto_fullAmplitudeOperator_frequency_cutoff c u x hi χ hχ hχ0 C hC).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  apply fullAmplitudeOperator_eq_integral_amplitudeKernel
  exact integrable_frequency_cutoff_amplitude_test c u _ x hc hu huc
    (hχ.comp (continuous_const.smul continuous_id)) (hχc.comp_smul (inv_ne_zero hR.ne'))

/-- `app:ch_regular_base:thm:actual-calculus`: an explicit derivative reserve
`m + dim V + 1` constructs the full operator as the limit of its actual physical
kernels. Only the stated finite integral budget of source derivatives is used. -/
theorem tendsto_integral_full_amplitudeKernel_of_derivativeMass [CompleteSpace F]
    (c : V → V → V → F) (u : V → ℂ) (x : V)
    (hc : Continuous (fun p : V × V ↦ c x p.2 p.1))
    (hu : Continuous u) (huc : HasCompactSupport u) (m : ℕ)
    (hs : ∀ ξ, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun y ↦ u y • c x y ξ))
    (A : ℝ) (hA : ∀ ξ, sourceDerivativeMass (fun y ↦ u y • c x y ξ)
      (m + Module.finrank ℝ V + 1) ≤ A * (1 + ‖ξ‖) ^ m)
    (χ : V → ℝ) (hχ : Continuous χ) (hχ0 : χ 0 = 1) (hχc : HasCompactSupport χ)
    (C : ℝ) (hC : ∀ ξ, |χ ξ| ≤ C) :
    Tendsto (fun R : ℝ ↦ ∫ y, u y •
      amplitudeKernel (fun x y ξ ↦ χ (R⁻¹ • ξ) • c x y ξ) x y) atTop
        (𝓝 (fullAmplitudeOperator c u x)) := by
  apply tendsto_integral_full_amplitudeKernel_frequency_cutoff c u x hc hu huc _ χ hχ hχ0 hχc C hC
  exact integrable_sourceFourier_of_compact_derivativeMass (fun ξ y ↦ u y • c x y ξ)
    ((hu.comp continuous_snd).smul hc) m _ (Nat.lt_succ_self _) hs (fun _ ↦ huc.smul_right) A hA

end JanetCartan.Pseudodifferential
