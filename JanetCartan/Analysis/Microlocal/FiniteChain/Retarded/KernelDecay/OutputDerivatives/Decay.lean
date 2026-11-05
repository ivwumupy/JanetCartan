module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Integral
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Grades
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Supports

/-!
# Decay of the actual output derivatives

The common kernel estimate in `app:ch_regular:lem:finite-chain` follows from
primitive profiles and the buffered half-space gaps. The amplitude, its output
jets, their supports and the derivative-under-integral identity are constructed.
The fixed losses in `app:ch_regular:eq:chain-tail` include both frequency
measures, the symbol orders and the prescribed output order, independently of
integration order. The constants use the fixed rectangular volume carrier.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel HalfSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

local instance outputDecayBaseVolumeHaar : (volume : Measure (ℝ × E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure E)
local instance outputDecayFrequenciesVolumeHaar : (volume : Measure ((ℝ × E) × (ℝ × E))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × E)) (volume : Measure (ℝ × E))
local instance outputDecayTangentialVolumeHaar : (volume : Measure (TangentialVariables E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × E))
    (volume : Measure ((ℝ × E) × (ℝ × E)))

private theorem collarDecayConstant_le_of_subset
    {K C : Set (ℝ × TangentialVariables E)} (hC : IsCompact C) (hKC : K ⊆ C)
    (eT : ι → TangentialVariables E) (eI : κ → ℝ × TangentialVariables E)
    (δT δI GT GI : ℝ) (P : ℕ → ℝ) {H A : ℕ → ℝ}
    (hH : ∀ j, 0 ≤ H j) (hA : ∀ j, 0 ≤ A j) (q : ℕ) :
    collarDecayConstant volume K eT eI δT δI GT GI P H A q ≤
      collarDecayConstant volume C eT eI δT δI GT GI P H A q := by
  have hprof := collarAmplitudeProfile_nonneg hH hA
  have ht := decayConstant_nonneg eT δT GT P _ hprof q
  have hi := decayConstant_nonneg eI δI GI P _ hprof q
  have hfst := measureReal_mono (μ := volume) (image_mono hKC)
    (hC.image continuous_fst).measure_lt_top.ne
  have hsnd := measureReal_mono (μ := volume) (image_mono hKC)
    (hC.image continuous_snd).measure_lt_top.ne
  have hvol := measureReal_mono (μ := volume.prod volume) hKC hC.measure_lt_top.ne
  unfold collarDecayConstant
  exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hfst ht) hsnd
    measureReal_nonneg (mul_nonneg ht measureReal_nonneg))
    (mul_le_mul_of_nonneg_left hvol hi)

/-- Every fixed scalar output derivative of either actual Fourier kernel has
`C(m,q) ρ^(m+C_A) L^b (L/ρ)^q` decay. Here
`C_A = 2(1+dim E)+pr+max 0 po+pi` and `b = br+bi+m+bo` are independent of `q`.
The displayed constant depends only on fixed primitive profiles, carriers and
geometric bounds, not on bases, unit directions, `ρ` or `L`. The remaining
geometric hypotheses are precisely the buffered tangential/interior gaps;
no differentiated identity, support or amplitude bound is assumed
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_fourierKernel_apply_le_of_primitive_profiles
    (upper : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r)
    {Kα Kβ Ko Ki : Set (ℝ × E)}
    (hKα : IsCompact Kα) (hKβ : IsCompact Kβ) (hKo : IsCompact Ko) (hKi : IsCompact Ki)
    (hsα : tsupport α ⊆ Kα) (hsβ : tsupport β ⊆ Kβ)
    (hsr : tsupport (fun ξ => r (ρ • ξ)) ⊆ Ko)
    (hsi : tsupport (fun ξ => mi xi (ρ • ξ)) ⊆ Ki)
    {UT UI : Set (ℝ × TangentialVariables E)} (hUT : IsOpen UT) (hUI : IsOpen UI)
    (eT : ι → TangentialVariables E) (eI : κ → ℝ × TangentialVariables E)
    (χ : ℝ × TangentialVariables E → ℂ) (hχ : ContDiff ℝ ∞ χ)
    {δT δI GT GI : ℝ} (hδT : 0 < δT) (hδI : 0 < δI)
    (hχT : outputDerivativeCarrier ρ mi mo xi xo (amplitudeCarrier Kα Kβ Ko Ki) ∩
      tsupport χ ⊆ UT)
    (hχI : (outputDerivativeCarrier ρ mi mo xi xo (amplitudeCarrier Kα Kβ Ko Ki) ∩
      tsupport (1 - χ)) ∩ {x | 0 < x.1} ⊆ UI)
    {ε : ℝ} (hε : 0 < ε) (hχ_one : ∀ x, |x.1| < ε → χ x = 1)
    (hgapT : ∀ d, 0 ≤ d → ∀ z, (d, z) ∈ UT →
      δT ≤ Localization.phaseGradientSquare eT (fun w => literalPhase upper xi xo (d, w)) z)
    (hupperT : ∀ d, 0 ≤ d → ∀ z, (d, z) ∈ UT →
      ‖fderiv ℝ (literalPhase upper xi xo) (d, z)‖ ≤ GT)
    (hgapI : ∀ x ∈ UI ∩ {x | 0 < x.1},
      δI ≤ Localization.phaseGradientSquare eI (literalPhase upper xi xo) x)
    (hupperI : ∀ x ∈ UI ∩ {x | 0 < x.1},
      ‖fderiv ℝ (literalPhase upper xi xo) x‖ ≤ GI)
    {P H A B I O R : ℕ → ℝ}
    (hH : ∀ j, 0 ≤ H j) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (hI : ∀ j, 0 ≤ I j) (hO : ∀ j, 0 ≤ O j) (hR : ∀ j, 0 ≤ R j)
    (pi po pr : ℝ) (bi bo br m q : ℕ) (v : Fin m → ℝ × E) (hv : ∀ i, ‖v i‖ ≤ 1)
    (ha : ∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j)
    (hi_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => mi xi (ρ • η)) ξ‖ ≤
      ρ ^ pi * I j * L ^ (j + bi))
    (hr_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => r (ρ • η)) ξ‖ ≤
      ρ ^ pr * R j * L ^ (j + br))
    (ho_bound : ∀ j ξ, ξ ∈ Ko → ‖iteratedFDeriv ℝ j (fun p : (ℝ × E) × (ℝ × E) =>
      mo (xo + ρ⁻¹ • p.1) (ρ • p.2)) (0, ξ)‖ ≤ ρ ^ po * O j * L ^ (j + bo))
    (hp : ∀ x ∈ amplitudeCarrier Kα Kβ Ko Ki, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (literalPhase upper xi xo)) x‖ ≤ P j * L ^ j)
    (hχ_bound : ∀ x ∈ amplitudeCarrier Kα Kβ Ko Ki, ∀ j,
      ‖iteratedFDeriv ℝ j χ x‖ ≤ H j) :
    ‖iteratedFDeriv ℝ m (fun y => if upper then upperFourierKernel α β mi mo r xi y
      else lowerFourierKernel α β mi mo r xi y) xo v‖ ≤
      ((normalization (E := E)) ^ 2 *
        collarDecayConstant volume (amplitudeCarrier Kα Kβ Ko Ki) eT eI δT δI GT GI P H
          (outputAmplitudeDerivativeConstant A B I O R (outputCarrierWaveProfile hKo) m) q) *
        ρ ^ ((m : ℝ) + (2 * (1 + Module.finrank ℝ E) + pr + max 0 po + pi)) *
          L ^ (br + bi + (m + bo)) * (L / ρ) ^ q := by
  let C := amplitudeCarrier Kα Kβ Ko Ki
  let K := outputDerivativeCarrier ρ mi mo xi xo C
  let a := outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v
  let S := ρ ^ m * ρ ^ (pr + max 0 po + pi)
  let D := outputAmplitudeDerivativeConstant A B I O R (outputCarrierWaveProfile hKo) m
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hS : 0 < S := mul_pos (pow_pos hρ0 _) (Real.rpow_pos_of_pos hρ0 _)
  have hD : ∀ j, 0 ≤ D j :=
    outputAmplitudeDerivativeConstant_nonneg hA hB hI hO hR (outputCarrierWaveProfile_spec hKo).1 m
  have hC : IsCompact C := isCompact_amplitudeCarrier hKα hKβ hKo hKi
  have hK : IsCompact K := isCompact_outputDerivativeCarrier ρ mi mo xi xo hC
  have hKC : K ⊆ C := fun _ hx => hx.1.1
  have has : ContDiff ℝ ∞ a :=
    contDiff_outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v hα hβ hi ho hr
  have hs : tsupport a ⊆ K := tsupport_outputDifferentiatedAmplitude_subset_carrier
    upper ρ α β mi mo r xi xo m v hKα hKβ hKo hKi hsα hsβ hsr hsi
  have hib : ContDiff ℝ ∞ (fun ξ => mi xi (ρ • ξ)) :=
    hi.comp (show ContDiff ℝ ∞ (fun ξ : ℝ × E => (xi, ρ • ξ)) from by fun_prop)
  have hrb : ContDiff ℝ ∞ (fun ξ => r (ρ • ξ)) := hr.comp (by fun_prop)
  have hab x (hx : x ∈ K) j :
      ‖iteratedFDeriv ℝ j (S⁻¹ • a) x‖ ≤ D j * L ^ (j + (br + bi + (m + bo))) := by
    rw [iteratedFDeriv_const_smul_apply (has.contDiffAt.of_le (by simp)), norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hS.le)]
    apply (inv_mul_le_iff₀ hS).2
    simpa only [S, D, a, mul_assoc] using
      outputDifferentiatedAmplitude_derivative_grades upper hρ hL α β mi mo r xi xo
        hα hβ hib ho hrb hKo hA hB hI hO hR pi po pr bi bo br m v hv
        ha hb hi_bound hr_bound ho_bound j x (hKC hx)
  have hdec := norm_halfSpaceOscillatoryIntegral_le (μ := volume) hUT hUI hK eT eI
    (literalPhase upper xi xo) (S⁻¹ • a) χ (contDiff_literalPhase upper xi xo)
    (has.const_smul (S⁻¹ : ℝ)) hχ ((tsupport_smul_subset_right (fun _ => S⁻¹) a).trans hs)
    hχT hχI hε hχ_one hδT hδI hL hρ hgapT hupperT hgapI hupperI hH hD
    (br + bi + (m + bo)) q (fun x hx => hp x (hKC hx))
    (fun x hx => hχ_bound x (hKC hx)) hab
  have hmono := collarDecayConstant_le_of_subset hC hKC eT eI δT δI GT GI P hH hD q
  have hdec' := hdec.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmono (pow_nonneg (zero_le_one.trans hL) _))
      (pow_nonneg (div_nonneg (zero_le_one.trans hL) hρ0.le) _))
  have he : halfSpaceOscillatoryIntegral volume ρ (literalPhase upper xi xo) a =
      S • halfSpaceOscillatoryIntegral volume ρ (literalPhase upper xi xo) (S⁻¹ • a) := by
    simp only [halfSpaceOscillatoryIntegral, halfSpaceIntegral, Pi.smul_apply,
      mul_smul_comm, integral_smul, smul_smul, mul_inv_cancel₀ hS.ne', one_smul]
  rw [iteratedFDeriv_fourierKernel_apply_eq_halfSpace upper hρ0 α β mi mo r xi xo m v
    hα hβ hi ho hr hKα hKβ hKo hKi hsα hsβ hsr hsi]
  change ‖((normalization (E := E)) ^ 2 * ρ ^ (2 * (1 + Module.finrank ℝ E))) •
    halfSpaceOscillatoryIntegral volume ρ (literalPhase upper xi xo) a‖ ≤ _
  rw [he, norm_smul, norm_smul, Real.norm_of_nonneg hS.le,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hρ0.le _))]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdec' hS.le)
    (mul_nonneg (sq_nonneg _) (pow_nonneg hρ0.le _))).trans_eq
  have hpowers : ρ ^ (2 * (1 + Module.finrank ℝ E)) * S =
      ρ ^ ((m : ℝ) + (2 * (1 + Module.finrank ℝ E) + pr + max 0 po + pi)) := by
    dsimp only [S]
    rw [show (m : ℝ) + (2 * (1 + Module.finrank ℝ E) + pr + max 0 po + pi) =
      ((2 * (1 + Module.finrank ℝ E) : ℕ) : ℝ) + (m : ℝ) + (pr + max 0 po + pi) by
        push_cast; ring]
    simp only [Real.rpow_add hρ0, Real.rpow_natCast]
    ring
  dsimp only [C, D] at *
  rw [← hpowers]
  ring

/-- For fixed physical output masks the joint mixed-symbol premise is
proved from the normalized mask profile, supplied by
`exists_bufferedMask_family_bounds`. Thus only input and regularizer orders
contribute to the fixed symbol loss in `app:ch_regular:eq:chain-tail`.
Both literal orientations and all output derivatives are covered. -/
theorem norm_iteratedFDeriv_fourierKernel_apply_physicalMask_le
    (upper : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
    (α β : ℝ × E → ℝ) (mi : (ℝ × E) → (ℝ × E) → ℂ) (mask : CanonicalPhase E → ℝ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (hm : ContDiff ℝ ∞ mask) (hr : ContDiff ℝ ∞ r)
    {Kα Kβ Ko Ki : Set (ℝ × E)}
    (hKα : IsCompact Kα) (hKβ : IsCompact Kβ) (hKo : IsCompact Ko) (hKi : IsCompact Ki)
    (hsα : tsupport α ⊆ Kα) (hsβ : tsupport β ⊆ Kβ)
    (hsr : tsupport (fun ξ => r (ρ • ξ)) ⊆ Ko)
    (hsi : tsupport (fun ξ => mi xi (ρ • ξ)) ⊆ Ki)
    {UT UI : Set (ℝ × TangentialVariables E)} (hUT : IsOpen UT) (hUI : IsOpen UI)
    (eT : ι → TangentialVariables E) (eI : κ → ℝ × TangentialVariables E)
    (χ : ℝ × TangentialVariables E → ℂ) (hχ : ContDiff ℝ ∞ χ)
    {δT δI GT GI : ℝ} (hδT : 0 < δT) (hδI : 0 < δI)
    (hχT : outputDerivativeCarrier ρ mi (fun y ξ => (physicalMask ρ mask (y, ξ) : ℂ))
      xi xo (amplitudeCarrier Kα Kβ Ko Ki) ∩ tsupport χ ⊆ UT)
    (hχI : (outputDerivativeCarrier ρ mi (fun y ξ => (physicalMask ρ mask (y, ξ) : ℂ))
      xi xo (amplitudeCarrier Kα Kβ Ko Ki) ∩ tsupport (1 - χ)) ∩ {x | 0 < x.1} ⊆ UI)
    {ε : ℝ} (hε : 0 < ε) (hχ_one : ∀ x, |x.1| < ε → χ x = 1)
    (hgapT : ∀ d, 0 ≤ d → ∀ z, (d, z) ∈ UT →
      δT ≤ Localization.phaseGradientSquare eT (fun w => literalPhase upper xi xo (d, w)) z)
    (hupperT : ∀ d, 0 ≤ d → ∀ z, (d, z) ∈ UT →
      ‖fderiv ℝ (literalPhase upper xi xo) (d, z)‖ ≤ GT)
    (hgapI : ∀ x ∈ UI ∩ {x | 0 < x.1},
      δI ≤ Localization.phaseGradientSquare eI (literalPhase upper xi xo) x)
    (hupperI : ∀ x ∈ UI ∩ {x | 0 < x.1},
      ‖fderiv ℝ (literalPhase upper xi xo) x‖ ≤ GI)
    {P H A B I O R : ℕ → ℝ}
    (hH : ∀ j, 0 ≤ H j) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (hI : ∀ j, 0 ≤ I j) (hO : ∀ j, 0 ≤ O j) (hR : ∀ j, 0 ≤ R j)
    (pi pr : ℝ) (bi br m q : ℕ) (v : Fin m → ℝ × E) (hv : ∀ i, ‖v i‖ ≤ 1)
    (ha : ∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j)
    (hi_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => mi xi (ρ • η)) ξ‖ ≤
      ρ ^ pi * I j * L ^ (j + bi))
    (hr_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => r (ρ • η)) ξ‖ ≤
      ρ ^ pr * R j * L ^ (j + br))
    (hm_bound : ∀ j p, ‖iteratedFDeriv ℝ j mask p‖ ≤ O j)
    (hp : ∀ x ∈ amplitudeCarrier Kα Kβ Ko Ki, ∀ j,
      ‖iteratedFDeriv ℝ j (fderiv ℝ (literalPhase upper xi xo)) x‖ ≤ P j * L ^ j)
    (hχ_bound : ∀ x ∈ amplitudeCarrier Kα Kβ Ko Ki, ∀ j,
      ‖iteratedFDeriv ℝ j χ x‖ ≤ H j) :
    ‖iteratedFDeriv ℝ m (fun y => if upper then
      upperFourierKernel α β mi (fun y ξ => (physicalMask ρ mask (y, ξ) : ℂ)) r xi y
      else lowerFourierKernel α β mi (fun y ξ => (physicalMask ρ mask (y, ξ) : ℂ)) r xi y) xo v‖ ≤
      ((normalization (E := E)) ^ 2 *
        collarDecayConstant volume (amplitudeCarrier Kα Kβ Ko Ki) eT eI δT δI GT GI P H
          (outputAmplitudeDerivativeConstant A B I O R (outputCarrierWaveProfile hKo) m) q) *
        ρ ^ ((m : ℝ) + (2 * (1 + Module.finrank ℝ E) + pr + pi)) *
          L ^ (br + bi + m) * (L / ρ) ^ q := by
  have ho : ContDiff ℝ ∞ (Function.uncurry
      (fun y ξ => (physicalMask ρ mask (y, ξ) : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_physicalMask hm ρ)
  have hob j ξ (_hξ : ξ ∈ Ko) :
      ‖iteratedFDeriv ℝ j (fun p : (ℝ × E) × (ℝ × E) =>
        (physicalMask ρ mask (xo + ρ⁻¹ • p.1, ρ • p.2) : ℂ)) (0, ξ)‖ ≤
          ρ ^ (0 : ℝ) * O j * L ^ (j + 0) := by
    simpa using norm_iteratedFDeriv_physicalMask_output_profile_le hm hO hm_bound hρ hL xo j (0, ξ)
  simpa only [max_self, add_zero] using
    norm_iteratedFDeriv_fourierKernel_apply_le_of_primitive_profiles upper hρ hL
      α β mi (fun y ξ => (physicalMask ρ mask (y, ξ) : ℂ)) r xi xo hα hβ hi ho hr
      hKα hKβ hKo hKi hsα hsβ hsr hsi hUT hUI eT eI χ hχ hδT hδI hχT hχI
      hε hχ_one hgapT hupperT hgapI hupperI hH hA hB hI hO hR
      pi 0 pr bi 0 br m q v hv ha hb hi_bound hr_bound hob hp hχ_bound

end JanetCartan.FiniteChain.Retarded.KernelDecay
