module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Support
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.PhysicalFourier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier recovery of the complementary output

The identity in `app:ch_regular:eq:joint-kernel-phase` is recovered by Fourier
inversion, including the physical normalization. The cutoff outputs can have
tails. Only their limit is identified with the identity minus the left localizer.
The input here is a genuine Schwartz field; identifying the graph output with
such a field is a separate obligation of the composition construction.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Filter
open scoped RealInnerProductSpace Topology ContDiff
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- The physical Fourier transform of a finite-channel test field, with the
normalization required by `app:ch_regular:eq:joint-kernel-phase`. -/
def channelFourierTransform (g : SchwartzMap (Euclidean n) (Fin r → ℂ)) :
    SchwartzMap (Euclidean n) (Fin r → ℂ) :=
  ((2 * Real.pi) ^ n : ℝ)⁻¹ •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean n)
        (Units.mk0 (2 * Real.pi)⁻¹ (by positivity))) (𝓕 g)

/-- Literal normalized physical Fourier integral for the channel field in
`app:ch_regular:eq:joint-kernel-phase`. -/
theorem channelFourierTransform_eq_integral
    (g : SchwartzMap (Euclidean n) (Fin r → ℂ)) (ξ : Euclidean n) :
    channelFourierTransform g ξ = ((2 * Real.pi) ^ n : ℂ)⁻¹ •
      ∫ y, Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) • g y := by
  change ((2 * Real.pi) ^ n : ℝ)⁻¹ •
    𝓕 (g : Euclidean n → Fin r → ℂ) ((2 * Real.pi)⁻¹ • ξ) = _
  rw [Real.fourier_eq']
  have hphase (y : Euclidean n) :
      (-2 * Real.pi * inner ℝ y ((2 * Real.pi)⁻¹ • ξ) : ℝ) = -inner ℝ y ξ := by
    rw [real_inner_smul_right]
    field_simp
  simp only [hphase, mul_comm _ Complex.I]
  norm_cast

/-- Fourier inversion recovers the finite-channel identity contribution in
`app:ch_regular:eq:joint-kernel-phase`. No integral of a constant symbol is
silently discarded. -/
theorem channelFourierTransform_inversion
    (g : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n) :
    (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
      channelFourierTransform g ξ) = g x := by
  have hscale := Measure.integral_comp_inv_smul_of_nonneg volume
    (fun ξ : Euclidean n ↦ Complex.exp ((2 * Real.pi * inner ℝ ξ x : ℝ) * Complex.I) •
      𝓕 (g : Euclidean n → Fin r → ℂ) ξ) (show 0 ≤ 2 * Real.pi by positivity)
  simp only [Euclidean, finrank_euclideanSpace_fin] at hscale
  have hphase (ξ : Euclidean n) :
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) =
        Complex.exp ((2 * Real.pi * inner ℝ ((2 * Real.pi)⁻¹ • ξ) x : ℝ) * Complex.I) := by
    rw [real_inner_smul_left, real_inner_comm ξ x]
    congr 1
    push_cast
    field_simp
  change (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
    (((2 * Real.pi) ^ n : ℝ)⁻¹ •
      𝓕 (g : Euclidean n → Fin r → ℂ) ((2 * Real.pi)⁻¹ • ξ))) = _
  simp_rw [hphase, smul_comm _ (((2 * Real.pi) ^ n : ℝ)⁻¹)]
  rw [integral_smul, hscale, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  have hinv := congrArg (fun f : SchwartzMap (Euclidean n) (Fin r → ℂ) ↦ f x)
    (fourierInv_fourier_eq (F := SchwartzMap (Euclidean n) (Fin r → ℂ)) g)
  simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe,
    Real.fourierInv_eq'] using hinv

/-- The literal left localizer on test fields is its physical Fourier action.
Consumer: cutoff removal for `app:ch_regular:eq:joint-kernel-phase`. -/
theorem leftLocalizer_eq_channelFourierIntegral (ρ : ℝ) (m : LocalizerSymbol n)
    (g : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n) :
    leftLocalizer ρ m g x = ∫ ξ,
      (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * (m (x, ρ⁻¹ • ξ) : ℂ)) •
        channelFourierTransform g ξ := by
  have hphase (y ξ : Euclidean n) :
      graphOscillation (fun a b => inner ℝ a b) x y ξ =
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
          Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) := by
    unfold graphOscillation
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [leftLocalizer, graphOperator, Matrix.smul_mulVec, Matrix.one_mulVec,
    hphase, channelFourierTransform_eq_integral, smul_smul]
  simp_rw [show ∀ (a b c : ℂ), a * b * c = (a * c) * b from fun _ _ _ => by ring]
  simp only [mul_smul, integral_smul]
  simp_rw [smul_comm _ (((2 * Real.pi) ^ n : ℂ)⁻¹)]
  rw [integral_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  congr 1
  simp_rw [smul_comm _ (m (x, ρ⁻¹ • ξ) : ℂ), integral_smul]

/-- Absolute integrability of a bounded output symbol against the Schwartz
Fourier density. This also handles the noncompact identity symbol in
`app:ch_regular:eq:joint-kernel-phase`. -/
theorem channelFourierIntegrand_integrable
    (g : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (a : Euclidean n → ℝ) (ha : Continuous a) (B : ℝ)
    (hb : ∀ ξ, |a ξ| ≤ B) :
    Integrable (fun ξ => (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
      (a ξ : ℂ)) • channelFourierTransform g ξ) := by
  apply ((channelFourierTransform g).integrable.norm.const_mul B).mono'
  · exact (by fun_prop : Continuous (fun ξ =>
      (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * (a ξ : ℂ)) •
        channelFourierTransform g ξ)).aestronglyMeasurable
  · filter_upwards [] with ξ
    simp only [norm_smul, norm_mul, mul_comm Complex.I,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _)

/-- The unregularized complement on Schwartz fields is the actual identity
minus the literal left localizer (`app:ch_regular:eq:joint-kernel-phase`).
Boundedness is required only on the fixed output slice of the symbol. -/
theorem complementary_channelFourierIntegral (ρ : ℝ) (m : LocalizerSymbol n)
    (g : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (hm : Continuous (fun ξ => m (x, ρ⁻¹ • ξ))) (B : ℝ)
    (hb : ∀ ξ, |m (x, ρ⁻¹ • ξ)| ≤ B) :
    (∫ ξ, (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
      ((1 - m (x, ρ⁻¹ • ξ) : ℝ) : ℂ)) • channelFourierTransform g ξ) =
      g x - leftLocalizer ρ m g x := by
  have h1 := channelFourierIntegrand_integrable g x (fun _ => 1)
    continuous_const 1 (fun _ => by simp)
  have h2 := channelFourierIntegrand_integrable g x _ hm B hb
  simp only [Complex.ofReal_one, mul_one] at h1
  simp only [Complex.ofReal_sub, Complex.ofReal_one, mul_sub, mul_one, sub_smul]
  rw [integral_sub h1 h2, channelFourierTransform_inversion,
    leftLocalizer_eq_channelFourierIntegral]

/-- Removing bounded frequency regularizers recovers `I - Mout` pointwise on
finite-channel Schwartz fields, including the identity contribution and its
noncompact regularized tails (`app:ch_regular:eq:joint-kernel-phase`). This is
an actual limit of the literal left operators, not a convergence hypothesis. -/
theorem tendsto_regularized_complementary_leftLocalizer
    (ρ : ℝ) (m : LocalizerSymbol n)
    (g : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (hm : Continuous (fun ξ => m (x, ρ⁻¹ • ξ))) (B : ℝ)
    (hb : ∀ ξ, |m (x, ρ⁻¹ • ξ)| ≤ B)
    (χ : ℕ → Euclidean n → ℝ) (hχ : ∀ k, Continuous (χ k))
    (hχb : ∀ k ξ, |χ k ξ| ≤ 1)
    (hχlim : ∀ ξ, Tendsto (fun k => χ k ξ) atTop (𝓝 1))
    (hρ : ρ ≠ 0) :
    Tendsto (fun k => leftLocalizer ρ
      (fun q => χ k (ρ • q.2) * (1 - m q)) g x) atTop
        (𝓝 (g x - leftLocalizer ρ m g x)) := by
  rw [← complementary_channelFourierIntegral ρ m g x hm B hb]
  simp only [leftLocalizer_eq_channelFourierIntegral, smul_smul,
    mul_inv_cancel₀ hρ, one_smul]
  apply tendsto_integral_of_dominated_convergence
    (fun ξ => (1 + B) * ‖channelFourierTransform g ξ‖)
  · intro k
    have hc : Continuous (fun ξ => χ k ξ * (1 - m (x, ρ⁻¹ • ξ))) :=
      (hχ k).mul (continuous_const.sub hm)
    exact (by fun_prop : Continuous (fun ξ =>
      (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        ((χ k ξ * (1 - m (x, ρ⁻¹ • ξ)) : ℝ) : ℂ)) •
          channelFourierTransform g ξ)).aestronglyMeasurable
  · exact (channelFourierTransform g).integrable.norm.const_mul (1 + B)
  · intro k
    filter_upwards [] with ξ
    simp only [norm_smul, norm_mul, mul_comm Complex.I,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      |χ k ξ| * |1 - m (x, ρ⁻¹ • ξ)| ≤ |1 - m (x, ρ⁻¹ • ξ)| :=
        mul_le_of_le_one_left (abs_nonneg _) (hχb k ξ)
      _ ≤ 1 + B := (abs_sub _ _).trans (by simpa using add_le_add_left (hb ξ) 1)
  · filter_upwards [] with ξ
    have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((hχlim ξ).mul_const (1 - m (x, ρ⁻¹ • ξ)))).const_mul
        (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)))
    simpa only [one_mul, Function.comp_def] using h.smul_const (channelFourierTransform g ξ)

/-- Cutoff removal on smooth compact outputs gives the actual complement with
compact support only at the limiting stage. Consumer: applying the supported
Sobolev bridge after identity recovery in `app:ch_regular:eq:chain-tail`. -/
theorem tendsto_regularized_complementary_output
    (ρ : ℝ) (m : LocalizerSymbol n) (g : Euclidean n → Fin r → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g)
    (hm : Continuous m) (B : ℝ) (hb : ∀ x ξ, |m (x, ξ)| ≤ B)
    (t : Set (Euclidean n)) (ht : IsCompact t)
    (hmt : ∀ x ∉ t, ∀ ξ, m (x, ξ) = 0)
    (χ : ℕ → Euclidean n → ℝ) (hχ : ∀ k, Continuous (χ k))
    (hχb : ∀ k ξ, |χ k ξ| ≤ 1)
    (hχlim : ∀ ξ, Tendsto (fun k => χ k ξ) atTop (𝓝 1)) (hρ : ρ ≠ 0) :
    (∀ x, Tendsto (fun k => leftLocalizer ρ
      (fun q => χ k (ρ • q.2) * (1 - m q)) g x) atTop
        (𝓝 ((g - leftLocalizer ρ m g) x))) ∧
      HasCompactSupport (g - leftLocalizer ρ m g) := by
  refine ⟨?_, complementaryOutput_hasCompactSupport ρ m g hgs t ht hmt⟩
  intro x
  exact tendsto_regularized_complementary_leftLocalizer ρ m (hgs.toSchwartzMap hg) x
    (hm.comp (continuous_const.prodMk (continuous_id.const_smul ρ⁻¹))) B
    (fun ξ => hb x (ρ⁻¹ • ξ)) χ hχ hχb hχlim hρ

end JanetCartan.FiniteChain.Graph.KernelLimits
