module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.FrequencyLocalization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalKernel
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.TestOutputs

/-!
# The literal identity between the same proof localizers

Fourier inversion identifies `(1 - Mo) Mi` with its two-position scalar
kernel. The original strict diagonal plateau yields a uniform neighborhood
where that kernel vanishes exactly. This is the identity contribution to
`finiteChain_observation_rapidDecayAt.hleak`; quantitative Sobolev extension
is a separate obligation (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Filter Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph KernelLimits
open FiniteChain.Retarded.KernelDecay
variable {n r : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem exists_inverse_channelFourierTransform (h : SchwartzMap E (Fin r → ℂ)) :
    ∃ g : SchwartzMap E (Fin r → ℂ), channelFourierTransform g = h := by
  let T := ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E)
    (Units.mk0 (2 * Real.pi) (by positivity))
  let g : SchwartzMap E (Fin r → ℂ) :=
    𝓕⁻ (((2 * Real.pi) ^ n : ℝ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ T h)
  refine ⟨g, ?_⟩
  ext ξ i
  change ((((2 * Real.pi) ^ n : ℝ)⁻¹ • (𝓕 g) ((2 * Real.pi)⁻¹ • ξ)) i) = h ξ i
  dsimp only [g]
  rw [fourier_fourierInv_eq]
  change ((((2 * Real.pi) ^ n : ℝ)⁻¹ •
    (((2 * Real.pi) ^ n : ℝ) • h ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ)))) i) = _
  simp only [smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul,
    inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ^ n ≠ 0)]

/-- Physical Fourier density of the actual right quantization; the source
base and the original `2π` normalization are unchanged
(`app:ch_regular:eq:joint-kernel-phase`). -/
def rightLocalizerFourierDensity (ρ : ℝ) (mi : LocalizerSymbol n)
    (f : E → Fin r → ℂ) (ξ : E) : Fin r → ℂ :=
  (((2 * Real.pi) ^ n : ℂ)⁻¹) • ∫ y,
    (Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) *
      (mi (y, ρ⁻¹ • ξ) : ℂ)) • f y

private theorem rightLocalizerFourierDensity_smooth_compact {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (f : E → Fin r → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rightLocalizerFourierDensity ρ mi f) ∧
      HasCompactSupport (rightLocalizerFourierDensity ρ mi f) := by
  let F : E × E → Fin r → ℂ := fun p ↦
    (Complex.exp (Complex.I * (-(inner ℝ p.2 p.1) : ℝ)) *
      (mi (p.2, ρ⁻¹ • p.1) : ℂ)) • f p.2
  have hF : ContDiff ℝ ∞ F := by
    have hp : ContDiff ℝ ∞ (fun p : E × E ↦ -(inner ℝ p.2 p.1)) :=
      (contDiff_snd.inner ℝ contDiff_fst).neg
    exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hp)).cexp.mul
      (Complex.ofRealCLM.contDiff.comp
        (hi.comp (contDiff_snd.prodMk (contDiff_fst.const_smul ρ⁻¹))))).smul
      (hf.comp contDiff_snd)
  have hs y (hy : y ∉ Prod.fst '' tsupport mi) ξ : F (ξ, y) = 0 := by
    have hm : mi (y, ρ⁻¹ • ξ) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hy ⟨_, h, rfl⟩)
    simp only [F, hm, Complex.ofReal_zero, mul_zero, zero_smul]
  refine ⟨(contDiff_integral_commonCarrier hF (his.image continuous_fst)
    (fun ξ y hy ↦ hs y hy ξ)).const_smul _, ?_⟩
  apply HasCompactSupport.intro
    ((his.image continuous_snd).image (continuous_id.const_smul ρ))
  intro ξ hξ
  have hm y : mi (y, ρ⁻¹ • ξ) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    exact hξ ⟨ρ⁻¹ • ξ, ⟨(y, ρ⁻¹ • ξ), hh, rfl⟩, by simp [smul_smul, hρ]⟩
  simp only [rightLocalizerFourierDensity, hm, Complex.ofReal_zero, mul_zero, zero_smul,
    integral_zero, smul_zero]

/-- The right localizer of a smooth test field is the actual inverse of its
compact physical Fourier density. This proves Schwartz regularity as well as
identification, with no assumption on the output or the datum's derivatives
in a norm estimate (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem exists_rightLocalizer_schwartz {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (f : E → Fin r → ℂ) (hf : ContDiff ℝ ∞ f) :
    ∃ g : SchwartzMap E (Fin r → ℂ),
      (∀ x, g x = rightLocalizer ρ mi f x) ∧
      ∀ ξ, channelFourierTransform g ξ = rightLocalizerFourierDensity ρ mi f ξ := by
  obtain ⟨hd, hds⟩ := rightLocalizerFourierDensity_smooth_compact hρ mi hi his f hf
  obtain ⟨g, hg⟩ := exists_inverse_channelFourierTransform (hds.toSchwartzMap hd)
  refine ⟨g, ?_, fun ξ ↦ DFunLike.congr_fun hg ξ⟩
  intro x
  rw [← channelFourierTransform_inversion g x, hg]
  change (∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
    rightLocalizerFourierDensity ρ mi f ξ) = _
  simp only [rightLocalizerFourierDensity, rightLocalizer, graphOperator,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  simp_rw [smul_comm _ (((2 * Real.pi) ^ n : ℂ)⁻¹), integral_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_smul]
  congr 1
  unfold graphOscillation
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The scalar kernel of `(1-Mo) Mi` for the SAME left/right localizers.
The complementary identity is retained in the amplitude
(`app:ch_regular:eq:chain-tail`). -/
def identityLeakageScalarKernel (ρ : ℝ) (mi mo : LocalizerSymbol n) (x y : E) : ℂ :=
  (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) * ∫ ξ,
    Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) *
      (((1 - mo (x, ρ⁻¹ • ξ)) * mi (y, ρ⁻¹ • ξ) : ℝ) : ℂ)

/-- Exact identity leakage on smooth tests. Fourier inversion, followed by
Fubini on the compact input base/frequency carrier, proves the literal
composition formula. No localized estimate is a hypothesis
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem identityLeakage_eq_integral_scalarKernel {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : Continuous mo) (horange : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    (f : E → Fin r → ℂ) (hf : ContDiff ℝ ∞ f) (x : E) :
    rightLocalizer ρ mi f x - leftLocalizer ρ mo (rightLocalizer ρ mi f) x =
      ∫ y, identityLeakageScalarKernel ρ mi mo x y • f y := by
  obtain ⟨g, hg, hgf⟩ := exists_rightLocalizer_schwartz hρ mi hi his f hf
  have hgfun : (g : E → Fin r → ℂ) = rightLocalizer ρ mi f := funext hg
  rw [← hgfun, ← complementary_channelFourierIntegral ρ mo g x
    (ho.comp (continuous_const.prodMk (continuous_id.const_smul ρ⁻¹))) 1
    (fun ξ ↦ by rw [abs_of_nonneg (horange _).1]; exact (horange _).2)]
  simp_rw [hgf]
  let a : E × E → ℂ := fun p ↦ (mi (p.1, ρ⁻¹ • p.2) : ℂ)
  have ha : Continuous a := Complex.continuous_ofReal.comp
    (hi.continuous.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
  have hca : HasCompactSupport a := by
    apply HasCompactSupport.intro
      (his.image (continuous_fst.prodMk (continuous_snd.const_smul ρ)))
    intro p hp
    have hz : mi (p.1, ρ⁻¹ • p.2) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hp ⟨(p.1, ρ⁻¹ • p.2), h, by simp [smul_smul, hρ]⟩
    simp only [a, hz, Complex.ofReal_zero]
  let F : E × E → Fin r → ℂ := fun p ↦
    (Complex.exp (Complex.I * (inner ℝ (x - p.1) p.2 : ℂ)) *
      ((1 - mo (x, ρ⁻¹ • p.2) : ℝ) : ℂ) * a p) • f p.1
  have hF : Continuous F := by
    have hp : Continuous (fun p : E × E ↦
        Complex.exp (Complex.I * (inner ℝ (x - p.1) p.2 : ℂ))) := by fun_prop
    exact ((hp.mul (Complex.continuous_ofReal.comp (continuous_const.sub
      (ho.comp (continuous_const.prodMk (continuous_snd.const_smul ρ⁻¹)))))).mul ha).smul
      (hf.continuous.comp continuous_fst)
  have hcF : HasCompactSupport F := hca.mul_left.smul_right
  have hint : Integrable F (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hF.integrable_of_hasCompactSupport hcF
  have he : (∫ ξ, (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
      ((1 - mo (x, ρ⁻¹ • ξ) : ℝ) : ℂ)) • rightLocalizerFourierDensity ρ mi f ξ) =
      (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) • ∫ ξ, ∫ y, F (y, ξ) := by
    simp only [rightLocalizerFourierDensity]
    simp_rw [smul_comm _ (((2 * Real.pi) ^ n : ℂ)⁻¹), ← integral_smul]
    simp only [smul_smul]
    push_cast
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [F, a]
    simp only [smul_smul]
    congr 1
    have hp : Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) =
        Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) := by
      rw [← Complex.exp_add, inner_sub_left]
      congr 1
      push_cast
      ring
    simp only [Complex.ofReal_neg] at hp
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    rw [show ∀ a b c d : ℂ, (a * b) * (c * d) = (a * c) * b * d from fun _ _ _ _ ↦ by ring, hp]
  rw [he, ← integral_integral_swap hint]
  simp only [identityLeakageScalarKernel, mul_smul, integral_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [F, a, Complex.ofReal_mul, ← mul_assoc, integral_smul_const]

/-- The strict diagonal plateau supplies one uniform spatial gap for the
actual identity-leakage amplitude. The geometric premise is exactly the
output of `exists_diagonal_bufferedLocalizers_joint_gap`; no product-shaped
replacement of either localizer is used (`app:ch_regular:lem:finite-chain`). -/
theorem exists_identityLeakage_amplitude_gap
    (mi mo : LocalizerSymbol n) (his : HasCompactSupport mi)
    (hplateau : tsupport mi ⊆ interior {p | mo p = 1}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : E, ‖x - y‖ ≤ δ → ∀ η : E,
      (1 - mo (x, η)) * mi (y, η) = 0 := by
  have hd : Disjoint (tsupport mi) (tsupport (fun p ↦ 1 - mo p)) := by
    apply disjoint_left.mpr
    intro p hp
    exact notMem_complement_tsupport_of_mem_plateau (hplateau hp)
  obtain ⟨δ, hδ, hgap⟩ := CompatibleResponse.exists_uniform_source_gap his
    (isClosed_tsupport _) hd
  refine ⟨δ, hδ, fun x y hxy η ↦ ?_⟩
  by_cases hi : mi (y, η) = 0
  · rw [hi, mul_zero]
  by_cases ho : 1 - mo (x, η) = 0
  · rw [ho, zero_mul]
  have h := hgap (y, η) (subset_tsupport mi hi) (x, η)
    (subset_tsupport (fun p ↦ 1 - mo p) ho)
  have he : dist (y, η) (x, η) = ‖x - y‖ := by
    simp [dist_eq_norm, Prod.norm_def, norm_sub_rev]
  rw [he] at h
  exact (h.not_ge hxy).elim

/-- Exact cancellation of the identity-leakage kernel in a fixed diagonal
neighborhood. Both localizers are fixed before `ρ`; the identity has not
been estimated separately (`app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageScalarKernel_zero_near_diagonal
    (mi mo : LocalizerSymbol n) (his : HasCompactSupport mi)
    (hplateau : tsupport mi ⊆ interior {p | mo p = 1}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : ℝ) (x y : E), ‖x - y‖ ≤ δ →
      identityLeakageScalarKernel ρ mi mo x y = 0 := by
  obtain ⟨δ, hδ, h⟩ := exists_identityLeakage_amplitude_gap mi mo his hplateau
  refine ⟨δ, hδ, fun ρ x y hxy ↦ ?_⟩
  simp only [identityLeakageScalarKernel, h x y hxy, Complex.ofReal_zero,
    mul_zero, integral_zero]

/-- The identity leakage retains the exact compact source carrier of its
right input localizer (`app:ch_regular:eq:chain-tail`). -/
theorem identityLeakageScalarKernel_zero_off_input
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (x y : E)
    (hy : y ∉ Prod.fst '' tsupport mi) : identityLeakageScalarKernel ρ mi mo x y = 0 := by
  have hm η : mi (y, η) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hy ⟨(y, η), h, rfl⟩)
  simp only [identityLeakageScalarKernel, hm, mul_zero, Complex.ofReal_zero, integral_zero]

/-- The literal bounded localizers have the identity-leakage kernel proved
above, on every Schwartz test field. The representatives are precisely those
of `exists_bounded_physicalLocalizers`; no new bounded operator is substituted.
This identification is used by the L²/Sobolev extension of the kernel estimate
(`app:ch_regular:eq:chain-tail`). -/
theorem bounded_identityLeakage_schwartz_ae_scalarKernel {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : Continuous mo) (horange : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    (Mi Mo : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E))
    (hMi : ∀ u, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hMo : ∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (f : SchwartzMap E (Fin r → ℂ)) :
    (1 - Mo) (Mi ((LowBounds.FrequencyCutoff.toEuclideanSchwartz f).toLp 2))
      =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (∫ y, identityLeakageScalarKernel ρ mi mo x y • f y) := by
  let u := (LowBounds.FrequencyCutoff.toEuclideanSchwartz f).toLp 2
  have hu := (LowBounds.FrequencyCutoff.toEuclideanSchwartz f).coeFn_toLp 2
  obtain ⟨g, hg, _⟩ := exists_rightLocalizer_schwartz hρ mi hi his f (f.smooth ⊤)
  have hRi : Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2 (g x) := by
    refine (hMi u).trans (Eventually.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    rw [hg]
    unfold rightLocalizer graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [hu] with y hy
    rw [show u y = WithLp.toLp 2 (f y) from hy]
  have hint i : Integrable (fun y ↦ Mi u y i) := by
    apply (g.integrable.eval i).congr
    filter_upwards [hRi] with y hy
    exact (congrArg (fun v : EuclideanSpace ℂ (Fin r) ↦ v i) hy).symm
  have hLo : Mo (Mi u) =ᵐ[volume] fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo g x) := by
    refine (hMo (Mi u) hint).trans (Eventually.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    unfold leftLocalizer graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [hRi] with y hy
    rw [hy]
  have hgfun : (g : E → Fin r → ℂ) = rightLocalizer ρ mi f := funext hg
  have hsub := Lp.coeFn_sub (Mi u) (Mo (Mi u))
  change Mi u - Mo (Mi u) =ᵐ[volume] _
  filter_upwards [hsub, hRi, hLo] with x hx hi' ho'
  rw [hx, Pi.sub_apply, hi', ho']
  change WithLp.toLp 2 (g x - leftLocalizer ρ mo g x) = _
  apply congrArg (WithLp.toLp 2)
  rw [hg x, hgfun, identityLeakage_eq_integral_scalarKernel hρ mi mo hi his ho horange f (f.smooth ⊤)]

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
