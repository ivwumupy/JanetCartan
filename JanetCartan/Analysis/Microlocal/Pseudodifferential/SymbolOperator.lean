module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.CutoffLimit
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Source-independent symbols on Schwartz data

The source-independent case of `app:ch_regular_base:thm:actual-calculus` admits
an absolutely convergent frequency integral after the Fourier transform of the
datum. Polynomial growth of the symbol suffices. The actual frequency cutoffs
converge to this operator, with the unit-frequency `2π` convention.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace Topology

namespace JanetCartan.Pseudodifferential
universe u v
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:thm:actual-calculus`: the actual inverse Fourier integral
for a source-independent symbol, applied to a scalar Schwartz datum. The values
may be vectors or matrices; this definition does not assert an `L²` extension. -/
def sourceIndependentOperator (a : V → V → F) (u : 𝓢(V, ℂ)) (x : V) : F :=
  𝓕⁻ (fun ξ ↦ (𝓕 u : 𝓢(V, ℂ)) ξ • a x ξ) x

/-- `app:ch_regular_base:thm:actual-calculus`: the literal integral with the
project's `2π` phase normalization. -/
theorem sourceIndependentOperator_eq_integral (a : V → V → F) (u : 𝓢(V, ℂ)) (x : V) :
    sourceIndependentOperator a u x = ∫ ξ,
      Complex.exp ((2 * Real.pi * ⟪ξ, x⟫ : ℝ) * Complex.I) • ((𝓕 u : 𝓢(V, ℂ)) ξ • a x ξ) :=
  Real.fourierInv_eq' _ _

/-- `app:ch_regular_base:thm:actual-calculus`: polynomial growth suffices for
absolute frequency integrability after taking the Fourier transform of the datum. -/
theorem integrable_sourceIndependentOperator_symbol (a : V → V → F) (u : 𝓢(V, ℂ))
    (x : V) (ha : Continuous (a x)) (A : ℝ) (N : ℕ)
    (hbound : ∀ ξ, ‖a x ξ‖ ≤ A * (1 + ‖ξ‖ ^ N)) :
    Integrable (fun ξ ↦ (𝓕 u : 𝓢(V, ℂ)) ξ • a x ξ) := by
  apply (integrable_norm_iff ((𝓕 u : 𝓢(V, ℂ)).continuous.smul ha).aestronglyMeasurable).mp
  change Integrable (fun ξ ↦ ‖(𝓕 u : 𝓢(V, ℂ)) ξ • a x ξ‖)
  simpa only [norm_smul] using
    integrable_schwartz_norm_mul_of_polynomial_bound (a x) ha A N hbound (𝓕 u : 𝓢(V, ℂ))

/-- `app:ch_regular_base:thm:actual-calculus`: an absolute bound for the actual
source-independent operator on Schwartz data. -/
theorem norm_sourceIndependentOperator_le (a : V → V → F) (u : 𝓢(V, ℂ)) (x : V) :
    ‖sourceIndependentOperator a u x‖ ≤ ∫ ξ, ‖(𝓕 u : 𝓢(V, ℂ)) ξ‖ * ‖a x ξ‖ := by
  rw [sourceIndependentOperator, Real.fourierInv_eq_fourier_neg]
  apply (Real.norm_fourier_le_integral_norm (fun ξ ↦ (𝓕 u : 𝓢(V, ℂ)) ξ • a x ξ) (-x)).trans_eq
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ ↦ norm_smul ((𝓕 u : 𝓢(V, ℂ)) ξ) (a x ξ)

/-- `app:ch_regular_base:thm:actual-calculus`: bounded continuous frequency
cutoffs equal to one at the origin converge to the actual source-independent
operator. Compact support is allowed but is unnecessary for this limit theorem. -/
theorem tendsto_sourceIndependentOperator_frequency_cutoff
    (a : V → V → F) (u : 𝓢(V, ℂ)) (x : V) (ha : Continuous (a x))
    (A : ℝ) (N : ℕ) (hbound : ∀ ξ, ‖a x ξ‖ ≤ A * (1 + ‖ξ‖ ^ N))
    (χ : V → ℝ) (hχ : Continuous χ) (hχ0 : χ 0 = 1)
    (C : ℝ) (hC : ∀ ξ, |χ ξ| ≤ C) :
    Tendsto (fun R : ℝ ↦ sourceIndependentOperator
      (fun x ξ ↦ χ (R⁻¹ • ξ) • a x ξ) u x) atTop
        (𝓝 (sourceIndependentOperator a u x)) := by
  simp only [sourceIndependentOperator, Real.fourierInv_eq]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ξ ↦ C * (‖(𝓕 u : 𝓢(V, ℂ)) ξ‖ * ‖a x ξ‖))
  · apply Eventually.of_forall
    intro R
    have hχR : Continuous (fun ξ : V ↦ χ (R⁻¹ • ξ)) :=
      hχ.comp (continuous_const.smul continuous_id)
    have hh : Continuous (fun ξ : V ↦ Real.fourierChar ⟪ξ, x⟫) := by fun_prop
    exact (hh.smul ((𝓕 u : 𝓢(V, ℂ)).continuous.smul (hχR.smul ha))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro R
    filter_upwards [] with ξ
    simp only [Circle.norm_smul, norm_smul, Real.norm_eq_abs]
    change ‖(𝓕 u : 𝓢(V, ℂ)) ξ‖ * (|χ (R⁻¹ • ξ)| * ‖a x ξ‖) ≤ _
    calc
      _ = |χ (R⁻¹ • ξ)| * (‖(𝓕 u : 𝓢(V, ℂ)) ξ‖ * ‖a x ξ‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hC _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · exact (integrable_schwartz_norm_mul_of_polynomial_bound (a x) ha A N hbound (𝓕 u : 𝓢(V, ℂ))).const_mul C
  · filter_upwards [] with ξ
    have hzero : Tendsto (fun R : ℝ ↦ R⁻¹ • ξ) atTop (𝓝 (0 : V)) := by
      convert (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).smul_const ξ using 1
      rw [zero_smul]
    have hlim : Tendsto (fun R : ℝ ↦ χ (R⁻¹ • ξ)) atTop (𝓝 (1 : ℝ)) := by
      have hh := hχ.continuousAt.tendsto.comp hzero
      rw [hχ0] at hh
      exact hh
    simpa using (tendsto_const_nhds.smul
      (tendsto_const_nhds.smul (hlim.smul_const (a x ξ))))


/-- `app:ch_regular_base:thm:actual-calculus`: for integrable symbols, the
source-independent Fourier formula is the literal physical kernel operator.
Fubini, rather than an abstract composition law, supplies the equality. -/
theorem sourceIndependentOperator_eq_integral_amplitudeKernel [CompleteSpace F]
    (a : V → V → F) (u : 𝓢(V, ℂ)) (x : V) (ha : Integrable (a x)) :
    sourceIndependentOperator a u x =
      ∫ y, u y • amplitudeKernel (fun x _y ξ ↦ a x ξ) x y := by
  let g : V → F := fun ξ ↦ Real.fourierChar ⟪ξ, x⟫ • a x ξ
  have hg : Integrable g := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).mpr ha
  have hswap : (∫ ξ, (𝓕 u : 𝓢(V, ℂ)) ξ • g ξ) = ∫ y, u y • 𝓕 g y := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner u.integrable hg)
  have hkernel (y : V) : 𝓕 g y = amplitudeKernel (fun x _y ξ ↦ a x ξ) x y := by
    simp only [Real.fourier_eq, amplitudeKernel, g]
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [← mul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [inner_sub_right]
    ring
  rw [sourceIndependentOperator, Real.fourierInv_eq]
  calc
    _ = ∫ ξ, (𝓕 u : 𝓢(V, ℂ)) ξ • g ξ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ ↦ smul_comm _ _ _
    _ = _ := hswap
    _ = _ := by simp_rw [hkernel]


/-- `app:ch_regular_base:thm:actual-calculus`: compact frequency regularizations
of the literal physical kernels converge to the unregularized source-independent
operator on scalar Schwartz data. No integrability of the original symbol is needed. -/
theorem tendsto_integral_amplitudeKernel_frequency_cutoff [CompleteSpace F]
    (a : V → V → F) (u : 𝓢(V, ℂ)) (x : V) (ha : Continuous (a x))
    (A : ℝ) (N : ℕ) (hbound : ∀ ξ, ‖a x ξ‖ ≤ A * (1 + ‖ξ‖ ^ N))
    (χ : V → ℝ) (hχ : Continuous χ) (hχ0 : χ 0 = 1) (hχc : HasCompactSupport χ)
    (C : ℝ) (hC : ∀ ξ, |χ ξ| ≤ C) :
    Tendsto (fun R : ℝ ↦ ∫ y, u y •
      amplitudeKernel (fun x _y ξ ↦ χ (R⁻¹ • ξ) • a x ξ) x y) atTop
        (𝓝 (sourceIndependentOperator a u x)) := by
  apply (tendsto_sourceIndependentOperator_frequency_cutoff a u x ha A N hbound
    χ hχ hχ0 C hC).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  apply sourceIndependentOperator_eq_integral_amplitudeKernel
  exact ((hχ.comp (continuous_const.smul continuous_id)).smul ha).integrable_of_hasCompactSupport
    (hχc.comp_smul (inv_ne_zero hR.ne')).smul_right

end JanetCartan.Pseudodifferential
