module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalKernel
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# The signed physical-tail kernel

The operator in `actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails`
uses `χ - 1`. Its kernel is the negative of the kernel estimated by
`PhysicalTailJets`. This leaf retains the sign, the original source-base
symbol and the physical `2π` normalization. Joint smoothness is proved by
integration over the actual compact frequency carrier.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral FiniteChain.Graph FiniteChain.Retarded.KernelDecay

variable {n : ℕ}
local notation "E" => Euclidean n

/-- The literal signed kernel of `(sourceCutMultiplier χ - 1).comp R`,
where `R` is the original right localizer. Consumer: both physical tails
in `app:ch_regular:eq:resolved-angular-tail`. -/
def signedRightLocalizerPhysicalTailKernel (ρ : ℝ) (mi : LocalizerSymbol n)
    (χ : E → ℝ) (x y : E) : ℂ :=
  ((χ x - 1 : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y

/-- The literal signed tail is the negative of the kernel whose jets are
estimated by `PhysicalTailJets` (`app:ch_regular:eq:chain-tail`). -/
theorem signedRightLocalizerPhysicalTailKernel_eq_neg (ρ : ℝ) (mi : LocalizerSymbol n)
    (χ : E → ℝ) (x y : E) :
    signedRightLocalizerPhysicalTailKernel ρ mi χ x y =
      -(((1 - χ x : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y) := by
  simp only [signedRightLocalizerPhysicalTailKernel, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- Exact transfer of every output-jet norm from `1 - χ` to the literal
signed physical tail (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_signedRightLocalizerPhysicalTailKernel
    (ρ : ℝ) (mi : LocalizerSymbol n) (χ : E → ℝ) (j : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ j (fun z ↦ signedRightLocalizerPhysicalTailKernel ρ mi χ z y) x‖ =
      ‖iteratedFDeriv ℝ j
        (fun z ↦ ((1 - χ z : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi z y) x‖ := by
  simp_rw [signedRightLocalizerPhysicalTailKernel_eq_neg]
  change ‖iteratedFDeriv ℝ j
    (-(fun z ↦ ((1 - χ z : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi z y)) x‖ = _
  rw [iteratedFDeriv_neg_apply, norm_neg]

private theorem contDiff_rightLocalizerScalarKernel_joint {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) :
    ContDiff ℝ ∞ (Function.uncurry (rightLocalizerScalarKernel ρ mi)) := by
  let K : Set E := (fun η : E ↦ ρ • η) '' (Prod.snd '' tsupport mi)
  have hK : IsCompact K := (his.image continuous_snd).image (by fun_prop)
  let f : (E × E) × E → ℂ := fun p ↦
    Complex.exp (Complex.I * (inner ℝ (p.1.1 - p.1.2) p.2 : ℂ)) *
      (mi (p.1.2, ρ⁻¹ • p.2) : ℂ)
  have hf : ContDiff ℝ ∞ f := by
    have hm : ContDiff ℝ ∞ (fun p : (E × E) × E ↦ (mi (p.1.2, ρ⁻¹ • p.2) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        (hi.comp (contDiff_fst.snd.prodMk (contDiff_snd.const_smul ρ⁻¹)))
    apply ContDiff.mul _ hm
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      ((contDiff_fst.fst.sub contDiff_fst.snd).inner ℝ contDiff_snd))).cexp
  have hz : ∀ p η, η ∉ K → f (p, η) = 0 := by
    intro p η hη
    have hm : mi (p.2, ρ⁻¹ • η) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hp
      apply hη
      exact ⟨ρ⁻¹ • η, ⟨(p.2, ρ⁻¹ • η), hp, rfl⟩, by simp [smul_smul, hρ]⟩
    simp only [f, hm, Complex.ofReal_zero, mul_zero]
  exact contDiff_const.mul (contDiff_integral_commonCarrier hf hK hz)

/-- Smoothness of the actual signed tail follows from the fixed smooth
compact symbol and the physical mask. No kernel regularity premise is
added to the Sobolev deduction (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_signedRightLocalizerPhysicalTailKernel_joint
    {ρ : ℝ} (hρ : ρ ≠ 0) (mi : LocalizerSymbol n)
    (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (Function.uncurry (signedRightLocalizerPhysicalTailKernel ρ mi χ)) :=
  (Complex.ofRealCLM.contDiff.comp ((hχ.comp contDiff_fst).sub contDiff_const)).mul
    (contDiff_rightLocalizerScalarKernel_joint hρ mi hi his)

/-- The signed tail keeps the exact compact source carrier of the right
localizer (`app:ch_regular:eq:chain-tail`). -/
theorem signedRightLocalizerPhysicalTailKernel_zero_off_input
    (ρ : ℝ) (mi : LocalizerSymbol n) (χ : E → ℝ) (x y : E)
    (hy : y ∉ Prod.fst '' tsupport mi) :
    signedRightLocalizerPhysicalTailKernel ρ mi χ x y = 0 := by
  rw [signedRightLocalizerPhysicalTailKernel, rightLocalizerScalarKernel_zero_off_input ρ mi x y hy,
    mul_zero]

/-- Literal signed-kernel action on continuous tests, with source
multiplication remaining inside the original right localizer. Consumer:
the bounded-operator identification in `app:ch_regular:eq:resolved-angular-tail`. -/
theorem signedRightLocalizerPhysicalTailKernel_integral {r : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi : LocalizerSymbol n) (hi : Continuous mi) (his : HasCompactSupport mi)
    (χ : E → ℝ) (g : E → Fin r → ℂ) (hg : Continuous g) (x : E) :
    ∫ y, signedRightLocalizerPhysicalTailKernel ρ mi χ x y • g y =
      ((χ x - 1 : ℝ) : ℂ) • rightLocalizer ρ mi g x := by
  rw [rightLocalizer_eq_integral_scalarKernel hρ mi hi his g hg]
  simp only [signedRightLocalizerPhysicalTailKernel, mul_smul, integral_smul]

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
