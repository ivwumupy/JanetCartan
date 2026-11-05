module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailJets.Frequency
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# Differentiation of the original physical tail integral

Compact frequency support justifies differentiation under the original integral.
Exact Fourier rescaling then identifies all output jets, with one power of the
physical frequency per derivative. Consumer: the physical cutoff tail estimate
in `app:ch_regular:eq:chain-tail` and `app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph FiniteChain.Retarded.KernelDecay
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Joint smoothness of the actual kernel follows from its original compact
frequency integral, with Euclidean volume and the physical normalization
unchanged (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_rightLocalizerScalarKernel {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) :
    ContDiff ℝ ∞ (fun p : E × E ↦ rightLocalizerScalarKernel ρ mi p.1 p.2) := by
  let f : (E × E) × E → ℂ := fun p ↦
    Complex.exp (Complex.I * (inner ℝ (p.1.1 - p.1.2) p.2 : ℂ)) *
      (mi (p.1.2, ρ⁻¹ • p.2) : ℂ)
  have hf : ContDiff ℝ ∞ f := by
    apply ContDiff.mul
    · exact Complex.contDiff_exp.comp (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp
          ((contDiff_fst.fst.sub contDiff_fst.snd).inner ℝ contDiff_snd)))
    · exact Complex.ofRealCLM.contDiff.comp
        (hi.comp (contDiff_fst.snd.prodMk (contDiff_snd.const_smul ρ⁻¹)))
  have hK := (his.image continuous_snd).image (continuous_const_smul ρ)
  have hs : ∀ p ξ, ξ ∉ (fun η : E ↦ ρ • η) '' (Prod.snd '' tsupport mi) →
      f (p, ξ) = 0 := by
    intro p ξ hξ
    have hm : mi (p.2, ρ⁻¹ • ξ) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      exact hξ ⟨ρ⁻¹ • ξ, ⟨(p.2, ρ⁻¹ • ξ), hh, rfl⟩, by simp [smul_smul, hρ]⟩
    simp [f, hm]
  exact contDiff_const.mul (contDiff_integral_commonCarrier hf hK hs)

/-- Every output jet of the SAME literal cutoff tail passes under the original
compact frequency integral. The derivative retains the complete cutoff and
phase product and the exact physical normalization; no derivative bound is
assumed (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem iteratedFDeriv_rightLocalizerScalarKernel_physicalTail_eq_integral
    {ρ : ℝ} (hρ : ρ ≠ 0) (mi : LocalizerSymbol n)
    (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (j : ℕ) (x y : E) :
    iteratedFDeriv ℝ j
        (fun x ↦ ((1 - χ x : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y) x =
      (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) • ∫ ξ,
        iteratedFDeriv ℝ j (fun x ↦ ((1 - χ x : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) *
            (mi (y, ρ⁻¹ • ξ) : ℂ)) x := by
  let f : E × E → ℂ := fun p ↦ ((1 - χ p.1 : ℝ) : ℂ) *
    Complex.exp (Complex.I * (inner ℝ (p.1 - y) p.2 : ℂ)) *
      (mi (y, ρ⁻¹ • p.2) : ℂ)
  have hf : ContDiff ℝ ∞ f := by
    apply ContDiff.mul
    · apply ContDiff.mul
      · exact Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (hχ.comp contDiff_fst))
      · exact Complex.contDiff_exp.comp (contDiff_const.mul
          (Complex.ofRealCLM.contDiff.comp
            ((contDiff_fst.sub contDiff_const).inner ℝ contDiff_snd)))
    · exact Complex.ofRealCLM.contDiff.comp
        (hi.comp (contDiff_const.prodMk (contDiff_snd.const_smul ρ⁻¹)))
  have hK := (his.image continuous_snd).image (continuous_const_smul ρ)
  have hs : ∀ x ξ, ξ ∉ (fun η : E ↦ ρ • η) '' (Prod.snd '' tsupport mi) →
      f (x, ξ) = 0 := by
    intro x ξ hξ
    have hm : mi (y, ρ⁻¹ • ξ) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      exact hξ ⟨ρ⁻¹ • ξ, ⟨(y, ρ⁻¹ • ξ), hh, rfl⟩, by simp [smul_smul, hρ]⟩
    simp [f, hm]
  have he : (fun x ↦ ((1 - χ x : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y) =
      fun x ↦ (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) • ∫ ξ, f (x, ξ) := by
    funext x
    simp only [rightLocalizerScalarKernel, f, mul_assoc, integral_const_mul, smul_eq_mul]
    ring
  rw [he, iteratedFDeriv_const_smul_apply'
    ((contDiff_integral_commonCarrier hf hK hs).contDiffAt.of_le (by simp)),
    iteratedFDeriv_integral_commonCarrier hf hK hs]

/-- The actual output jets vanish off exactly the original source-base carrier;
output differentiation does not enlarge this carrier
(`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_rightLocalizerScalarKernel_physicalTail_zero_off_input
    (ρ : ℝ) (mi : LocalizerSymbol n) (χ : E → ℝ) (j : ℕ) (x y : E)
    (hy : y ∉ Prod.fst '' tsupport mi) :
    iteratedFDeriv ℝ j
      (fun x ↦ ((1 - χ x : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y) x = 0 := by
  have he : (fun x ↦ ((1 - χ x : ℝ) : ℂ) * rightLocalizerScalarKernel ρ mi x y) =
      fun _ ↦ 0 := by
    funext x
    rw [rightLocalizerScalarKernel_zero_off_input ρ mi x y hy, mul_zero]
  rw [he]
  simp

/-- Exact norm identity for physical kernel jets. Translation introduces no
loss, and rescaling introduces precisely one power of `ρ / (2π)` per output
derivative (`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_rightLocalizerScalarKernel_eq_fourier
    {ρ : ℝ} (hρ : 0 < ρ) (mi : LocalizerSymbol n)
    (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) (j : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ j (fun x ↦ rightLocalizerScalarKernel ρ mi x y) x‖ =
      (ρ / (2 * Real.pi)) ^ (n + j) *
        ‖iteratedFDeriv ℝ j (𝓕 (fun η ↦ (mi (y, η) : ℂ)))
          (-(ρ / (2 * Real.pi)) • (x - y))‖ := by
  have hf : ContDiff ℝ ∞ (𝓕 (fun η ↦ (mi (y, η) : ℂ))) :=
    Real.contDiff_fourier (N := ⊤) (fun k _ ↦ by
      simpa only [norm_iteratedFDeriv_zero] using
        PhysicalTailJets.integrable_frequencySlice_jet_moment mi hi his y k 0)
  have he := funext (fun x ↦ rightLocalizerScalarKernel_eq_fourier hρ mi x y)
  have hs : ContDiff ℝ ∞ (fun z : E ↦
      𝓕 (fun η ↦ (mi (y, η) : ℂ)) (-(ρ / (2 * Real.pi)) • (z - y))) :=
    hf.comp ((contDiff_id.sub contDiff_const).const_smul _)
  rw [he, iteratedFDeriv_const_smul_apply'
    (hs.contDiffAt.of_le (by simp))]
  rw [iteratedFDeriv_comp_sub (f := fun z ↦
    𝓕 (fun η ↦ (mi (y, η) : ℂ)) (-(ρ / (2 * Real.pi)) • z)),
    iteratedFDeriv_comp_const_smul _ (hf.of_le (by simp))]
  simp only [norm_smul, norm_pow, norm_neg,
    Real.norm_of_nonneg (by positivity : 0 ≤ ρ / (2 * Real.pi)), pow_add, mul_assoc]

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
