module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SymbolOperator

/-!
# Complementary symbols on Schwartz data

The identity term in `app:ch_regular:eq:chain-tail` is recovered by Fourier
inversion. Only the output symbol, and each finite frequency cutoff, have compact
frequency support. This is the inner product domain step for
`tendsto_leftOperator_complementarySymbol`.

These scalar statements allow the domain to lie in any universe. The general
vector-valued `sourceIndependentOperator` API requires the codomain universe to
be at least the domain universe; its Fubini argument is specialized here.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace Topology
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
open Pseudodifferential
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Scalar Fubini for the fixed output section of a left symbol. Consumed by
`tendsto_complementary_cyclesKernel` (`app:ch_regular:eq:chain-tail`). -/
theorem schwartz_fourierInv_mul_eq_integral_kernel (a : V → ℂ)
    (u : 𝓢(V, ℂ)) (x : V) (ha : Integrable a) :
    𝓕⁻ (fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ • a ξ) x =
      ∫ y, u y • amplitudeKernel (fun _x _y ξ => a ξ) x y := by
  let g : V → ℂ := fun ξ => Real.fourierChar ⟪ξ, x⟫ • a ξ
  have hg : Integrable g := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).mpr ha
  have hswap : (∫ ξ, (𝓕 u : 𝓢(V, ℂ)) ξ • g ξ) = ∫ y, u y • 𝓕 g y := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner u.integrable hg)
  have hkernel (y : V) : 𝓕 g y = amplitudeKernel (fun _x _y ξ => a ξ) x y := by
    simp only [Real.fourier_eq, amplitudeKernel, g]
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [← mul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [inner_sub_right]
    ring
  rw [Real.fourierInv_eq]
  calc
    _ = ∫ ξ, (𝓕 u : 𝓢(V, ℂ)) ξ • g ξ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => smul_comm _ _ _
    _ = _ := hswap
    _ = _ := by simp_rw [hkernel]

/-- Fourier inversion separates the identity contribution from the compact
output symbol in `app:ch_regular:eq:chain-tail`. All Fourier integrability follows
from Schwartz decay and compact support. -/
theorem schwartz_fourierInv_complement (m : V → ℂ)
    (u : 𝓢(V, ℂ)) (x : V) (hm : Continuous m)
    (hmc : HasCompactSupport m) :
    𝓕⁻ (fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ • (1 - m ξ)) x =
      u x - 𝓕⁻ (fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ • m ξ) x := by
  have hi : Integrable (fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ • m ξ) :=
    ((𝓕 u : 𝓢(V, ℂ)).continuous.smul hm).integrable_of_hasCompactSupport hmc.smul_left
  have h1 := (Real.fourierIntegral_convergent_iff (-x)).mpr ((𝓕 u : 𝓢(V, ℂ)).integrable (μ := volume))
  have h2 := (Real.fourierIntegral_convergent_iff (-x)).mpr hi
  simp only [inner_neg_right, neg_neg] at h1 h2
  have hinv : 𝓕⁻ (fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ) x = u x := by
    rw [SchwartzMap.fourier_coe, u.continuous.fourierInv_fourier_eq u.integrable
      (by simpa only [← SchwartzMap.fourier_coe] using (𝓕 u : 𝓢(V, ℂ)).integrable)]
  simp only [Real.fourierInv_eq, smul_eq_mul, mul_sub, mul_one, smul_sub] at *
  rw [integral_sub h1 h2, hinv]

/-- The literal cutoff kernels converge to identity minus the output operator
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). The Fourier
integrable majorant is constructed from the datum and the compact symbol. -/
theorem tendsto_complementary_cyclesKernel (m : V → ℂ)
    (u : 𝓢(V, ℂ)) (x : V) (hm : Continuous m)
    (hmc : HasCompactSupport m) (χ : V → ℝ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1) :
    Tendsto (fun R : ℝ => ∫ y, u y • amplitudeKernel
      (fun _x _y ξ => χ (R⁻¹ • ξ) • (1 - m ξ)) x y) atTop
      (𝓝 (u x - ∫ y, u y • amplitudeKernel (fun _x _y ξ => m ξ) x y)) := by
  let f : V → ℂ := fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ • (1 - m ξ)
  have hi : Integrable f := by
    have hi2 : Integrable (fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ • m ξ) :=
      ((𝓕 u : 𝓢(V, ℂ)).continuous.smul hm).integrable_of_hasCompactSupport
      hmc.smul_left
    have hid : Integrable (fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ - (𝓕 u : 𝓢(V, ℂ)) ξ • m ξ) :=
      (𝓕 u : 𝓢(V, ℂ)).integrable.sub hi2
    simpa only [f, smul_eq_mul, mul_sub, mul_one] using hid
  obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuous hχ
  have hlim : Tendsto (fun R : ℝ => 𝓕⁻ (fun ξ => χ (R⁻¹ • ξ) • f ξ) x)
      atTop (𝓝 (𝓕⁻ f x)) := by
    simp only [Real.fourierInv_eq]
    apply tendsto_integral_filter_of_dominated_convergence (fun ξ => C * ‖f ξ‖)
    · apply Eventually.of_forall
      intro R
      have hp : Continuous (fun ξ : V => Real.fourierChar ⟪ξ, x⟫) := by fun_prop
      exact hp.aestronglyMeasurable.smul
        ((hχ.comp (continuous_const.smul continuous_id)).aestronglyMeasurable.smul
          hi.aestronglyMeasurable)
    · apply Eventually.of_forall
      intro R
      filter_upwards [] with ξ
      simp only [Circle.norm_smul, norm_smul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    · exact hi.norm.const_mul C
    · filter_upwards [] with ξ
      have hzero : Tendsto (fun R : ℝ => R⁻¹ • ξ) atTop (𝓝 (0 : V)) := by
        simpa using (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).smul_const ξ
      have hχlim : Tendsto (fun R : ℝ => χ (R⁻¹ • ξ)) atTop (𝓝 (1 : ℝ)) := by
        simpa only [hχ0, Function.comp_def] using hχ.continuousAt.tendsto.comp hzero
      simpa using tendsto_const_nhds.smul (hχlim.smul_const (f ξ))
  rw [show 𝓕⁻ f x = u x - 𝓕⁻ (fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ • m ξ) x from
    schwartz_fourierInv_complement m u x hm hmc,
    schwartz_fourierInv_mul_eq_integral_kernel m u x (hm.integrable_of_hasCompactSupport hmc)] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have ha : Integrable (fun ξ => χ (R⁻¹ • ξ) • (1 - m ξ)) :=
    ((hχ.comp (continuous_const.smul continuous_id)).smul (continuous_const.sub hm)).integrable_of_hasCompactSupport
      (hχc.comp_smul (inv_ne_zero hR.ne')).smul_right
  rw [show (fun ξ => χ (R⁻¹ • ξ) • f ξ) =
      (fun ξ => (𝓕 u : 𝓢(V, ℂ)) ξ • (χ (R⁻¹ • ξ) • (1 - m ξ))) by
        funext ξ; exact smul_comm _ _ _]
  exact schwartz_fourierInv_mul_eq_integral_kernel _ u x ha

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
