module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.AmplitudeGrades.Products
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# All-order grades of the literal normalized retarded amplitudes

The five primitive factors in `app:ch_regular:lem:finite-chain` give an
explicit Leibniz profile. Fixed symbol orders contribute an explicit power
of `ρ`; after removing it the offset in `L` is independent of integration
order. These are the amplitude data for
`KernelDecay.norm_fourierKernel_le_of_halfSpace_data` and the output
derivative estimates in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel

/-- Five-factor Leibniz profile, including the shifted weight's `2^j`
coordinate cost and the identity in `1 - mo`
(`app:ch_regular:eq:high-amplitude`). -/
def amplitudeDerivativeConstant (A B I O R : ℕ → ℝ) : ℕ → ℝ :=
  derivativeConvolution
    (derivativeConvolution (derivativeConvolution (fun j => A j * 2 ^ j) B)
      (derivativeConvolution R (fun j => 1 + O j))) I

/-- The explicit profile is nonnegative as required by the half-space
consumer (`app:ch_regular:eq:chain-tail`). -/
theorem amplitudeDerivativeConstant_nonneg {A B I O R : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (hI : ∀ j, 0 ≤ I j)
    (hO : ∀ j, 0 ≤ O j) (hR : ∀ j, 0 ≤ R j) (n : ℕ) :
    0 ≤ amplitudeDerivativeConstant A B I O R n :=
  derivativeConvolution_nonneg
    (derivativeConvolution_nonneg
      (derivativeConvolution_nonneg (fun j => mul_nonneg (hA j) (by positivity)) hB)
      (derivativeConvolution_nonneg hR (fun j => by linarith [hO j]))) hI n

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private abbrev X := ℝ × TangentialVariables E

private def baseCoordinate : X (E := E) →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.fst ℝ (ℝ × E) _).comp (ContinuousLinearMap.snd ℝ ℝ _)

private def shiftedCoordinate : X (E := E) →L[ℝ] ℝ × E :=
  ((ContinuousLinearMap.fst ℝ ℝ E).comp baseCoordinate +
    ContinuousLinearMap.fst ℝ ℝ _).prod
    ((ContinuousLinearMap.snd ℝ ℝ E).comp baseCoordinate)

private def frequencyCoordinate (input : Bool) : X (E := E) →L[ℝ] ℝ × E :=
  (if input then ContinuousLinearMap.snd ℝ (ℝ × E) (ℝ × E)
    else ContinuousLinearMap.fst ℝ (ℝ × E) (ℝ × E)).comp
    ((ContinuousLinearMap.snd ℝ (ℝ × E) _).comp (ContinuousLinearMap.snd ℝ ℝ _))

private theorem norm_baseCoordinate_le : ‖baseCoordinate (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.2.1‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using (norm_fst_le x.2).trans (norm_snd_le x)

private theorem norm_shiftedCoordinate_le : ‖shiftedCoordinate (E := E)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(x.2.1.1 + x.1, x.2.1.2)‖ ≤ _
  rw [Prod.norm_def]
  have h1 := (norm_fst_le x.2.1).trans ((norm_fst_le x.2).trans (norm_snd_le x))
  have h2 := (norm_snd_le x.2.1).trans ((norm_fst_le x.2).trans (norm_snd_le x))
  exact max_le (by linarith [norm_add_le x.2.1.1 x.1, norm_fst_le x])
    (by linarith [norm_nonneg x])

private theorem norm_frequencyCoordinate_le (input : Bool) :
    ‖frequencyCoordinate (E := E) input‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  cases input
  · change ‖x.2.2.1‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using
      (norm_fst_le x.2.2).trans ((norm_snd_le x.2).trans (norm_snd_le x))
  · change ‖x.2.2.2‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using
      (norm_snd_le x.2.2).trans ((norm_snd_le x.2).trans (norm_snd_le x))

private theorem weight_grade {w : ℝ × E → ℝ} (hw : ContDiff ℝ ∞ w)
    {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j w y‖ ≤ C j)
    (p : X (E := E) →L[ℝ] ℝ × E) {c L : ℝ} (hc : 0 ≤ c)
    (hp : ‖p‖ ≤ c) (hL : 1 ≤ L) (n : ℕ) (x : X (E := E)) :
    ‖iteratedFDeriv ℝ n (fun y => (w (p y) : ℂ)) x‖ ≤
      1 * (C n * c ^ n) * L ^ (n + 0) := by
  change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ (w ∘ p)) x‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hw.comp p.contDiff).contDiffAt
    (show (n : ℕ∞ω) ≤ ∞ by simp)]
  apply norm_iteratedFDeriv_comp_linear_le_grades hw p hc hp hC
    zero_le_one (zero_le_one.trans hL) 0 x n
  simpa only [one_mul, Nat.add_zero] using
    (hb n (p x)).trans (le_mul_of_one_le_right (hC n) (one_le_pow₀ hL))

/-- Product estimate from the primitive weight jets and the three normalized
frequency profiles. The external bases, regularizer, frequency and grade do
not enter `amplitudeDerivativeConstant`. The output scale is at least one
because the complementary symbol contains the identity
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_normalizedAmplitude_le_scales
    (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ) (xi xo : ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (fun ξ => mi xi (ρ • ξ)))
    (ho : ContDiff ℝ ∞ (fun ξ => mo xo (ρ • ξ)))
    (hr : ContDiff ℝ ∞ (fun ξ => r (ρ • ξ)))
    {A B I O R : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (hI : ∀ j, 0 ≤ I j)
    (hO : ∀ j, 0 ≤ O j) (hR : ∀ j, 0 ≤ R j)
    {Si So Sr L : ℝ} (hSi : 0 ≤ Si) (hSo : 1 ≤ So) (hSr : 0 ≤ Sr) (hL : 1 ≤ L)
    (bi bo br : ℕ)
    (ha : ∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j)
    (hi_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => mi xi (ρ • η)) ξ‖ ≤
      Si * I j * L ^ (j + bi))
    (ho_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => mo xo (ρ • η)) ξ‖ ≤
      So * O j * L ^ (j + bo))
    (hr_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => r (ρ • η)) ξ‖ ≤
      Sr * R j * L ^ (j + br)) (n : ℕ) (x : ℝ × TangentialVariables E) :
    ‖iteratedFDeriv ℝ n (normalizedAmplitude upper ρ α β mi mo r xi xo) x‖ ≤
      (Sr * So * Si) * amplitudeDerivativeConstant A B I O R n *
        L ^ (n + (br + bo + bi)) := by
  let a : X (E := E) → ℂ := fun y => (α (shiftedCoordinate y) : ℂ)
  let b : X (E := E) → ℂ := fun y => (β (baseCoordinate y) : ℂ)
  let i : X (E := E) → ℂ := (fun ξ => mi xi (ρ • ξ)) ∘ frequencyCoordinate true
  let o : X (E := E) → ℂ := (fun ξ => mo xo (ρ • ξ)) ∘ frequencyCoordinate false
  let s : X (E := E) → ℂ := (fun ξ => r (ρ • ξ)) ∘ frequencyCoordinate false
  have hsa : ContDiff ℝ ∞ a := Complex.ofRealCLM.contDiff.comp
    (hα.comp (shiftedCoordinate (E := E)).contDiff)
  have hsb : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp
    (hβ.comp (baseCoordinate (E := E)).contDiff)
  have hsi : ContDiff ℝ ∞ i := hi.comp (frequencyCoordinate (E := E) true).contDiff
  have hso : ContDiff ℝ ∞ o := ho.comp (frequencyCoordinate (E := E) false).contDiff
  have hss : ContDiff ℝ ∞ s := hr.comp (frequencyCoordinate (E := E) false).contDiff
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hSo0 : 0 ≤ So := zero_le_one.trans hSo
  have ha' j := weight_grade hα hA ha shiftedCoordinate (by norm_num)
    norm_shiftedCoordinate_le hL j x
  have hb' j : ‖iteratedFDeriv ℝ j b x‖ ≤ 1 * B j * L ^ (j + 0) := by
    simpa using weight_grade hβ hB hb baseCoordinate zero_le_one norm_baseCoordinate_le hL j x
  have hi' j : ‖iteratedFDeriv ℝ j i x‖ ≤ Si * I j * L ^ (j + bi) := by
    simpa using norm_iteratedFDeriv_comp_linear_le_grades hi (frequencyCoordinate true)
      zero_le_one (norm_frequencyCoordinate_le true) hI hSi hL0 bi x j (hi_bound j _)
  have ho' j : ‖iteratedFDeriv ℝ j o x‖ ≤ So * O j * L ^ (j + bo) := by
    simpa using norm_iteratedFDeriv_comp_linear_le_grades ho (frequencyCoordinate false)
      zero_le_one (norm_frequencyCoordinate_le false) hO hSo0 hL0 bo x j (ho_bound j _)
  have hr' j : ‖iteratedFDeriv ℝ j s x‖ ≤ Sr * R j * L ^ (j + br) := by
    simpa using norm_iteratedFDeriv_comp_linear_le_grades hr (frequencyCoordinate false)
      zero_le_one (norm_frequencyCoordinate_le false) hR hSr hL0 br x j (hr_bound j _)
  have hc j := norm_iteratedFDeriv_one_sub_le_grades hso hSo hL bo x ho' j
  have hA' j : 0 ≤ A j * 2 ^ j := mul_nonneg (hA j) (by positivity)
  have hO' j : 0 ≤ 1 + O j := by linarith [hO j]
  have hab := norm_iteratedFDeriv_mul_le_grades hsa hsb hA' hB
    zero_le_one zero_le_one hL0 0 0 x ha' hb'
  have hrc := norm_iteratedFDeriv_mul_le_grades hss (contDiff_const.sub hso) hR hO'
    hSr hSo0 hL0 br bo x hr' hc
  have habrc := norm_iteratedFDeriv_mul_le_grades (hsa.mul hsb)
    (hss.mul (contDiff_const.sub hso)) (derivativeConvolution_nonneg hA' hB)
    (derivativeConvolution_nonneg hR hO') (by norm_num : (0 : ℝ) ≤ 1 * 1)
    (mul_nonneg hSr hSo0) hL0 (0 + 0) (br + bo) x hab hrc
  let f : X (E := E) → ℂ := fun y => (a y * b y) * (s y * (1 - o y)) * i y
  have hsf : ContDiff ℝ ∞ f := ((hsa.mul hsb).mul
    (hss.mul (contDiff_const.sub hso))).mul hsi
  have hf := norm_iteratedFDeriv_mul_le_grades
    ((hsa.mul hsb).mul (hss.mul (contDiff_const.sub hso))) hsi
    (derivativeConvolution_nonneg (derivativeConvolution_nonneg hA' hB)
      (derivativeConvolution_nonneg hR hO')) hI
    (by positivity : 0 ≤ (1 : ℝ) * 1 * (Sr * So)) hSi hL0
    ((0 + 0) + (br + bo)) bi x habrc hi' n
  have he : normalizedAmplitude upper ρ α β mi mo r xi xo =
      (if upper then -Complex.I else Complex.I) • f := by
    funext y
    cases upper <;> simp [normalizedAmplitude, lowerAmplitude, upperAmplitude,
      f, a, b, s, o, i, shiftedCoordinate, baseCoordinate, frequencyCoordinate,
      smul_eq_mul] <;> ring
  rw [he, iteratedFDeriv_const_smul_apply (hsf.contDiffAt.of_le (by simp)), norm_smul]
  have hu : ‖if upper then -Complex.I else Complex.I‖ = 1 := by cases upper <;> simp
  rw [hu, one_mul]
  simpa only [f, amplitudeDerivativeConstant, zero_add, one_mul] using hf

/-- Smoothness from the normalized primitive slices alone, used to remove
the symbol-order power in `app:ch_regular:eq:chain-tail`. -/
theorem contDiff_normalizedAmplitude_of_frequency_profiles
    (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ) (xi xo : ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (fun ξ => mi xi (ρ • ξ)))
    (ho : ContDiff ℝ ∞ (fun ξ => mo xo (ρ • ξ)))
    (hr : ContDiff ℝ ∞ (fun ξ => r (ρ • ξ))) :
    ContDiff ℝ ∞ (normalizedAmplitude upper ρ α β mi mo r xi xo) := by
  have hi' : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E => mi xi (ρ • x.2.2.2)) :=
    hi.comp (frequencyCoordinate (E := E) true).contDiff
  have ho' : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E => mo xo (ρ • x.2.2.1)) :=
    ho.comp (frequencyCoordinate (E := E) false).contDiff
  have hr' : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E => r (ρ • x.2.2.1)) :=
    hr.comp (frequencyCoordinate (E := E) false).contDiff
  have hα' : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E =>
      (α (x.2.1.1 + x.1, x.2.1.2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hα.comp (shiftedCoordinate (E := E)).contDiff)
  have hβ' : ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E => (β x.2.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hβ.comp (baseCoordinate (E := E)).contDiff)
  change ContDiff ℝ ∞ (fun x : ℝ × TangentialVariables E =>
    normalizedAmplitude upper ρ α β mi mo r xi xo x)
  cases upper <;>
    simp only [normalizedAmplitude, lowerAmplitude, upperAmplitude, Bool.false_eq_true,
      ↓reduceIte, Prod.smul_fst, Prod.smul_snd]
  · exact (((contDiff_const.mul hα').mul hβ').mul
      (hr'.mul (contDiff_const.sub ho'))).mul hi'
  · exact (((contDiff_const.mul hβ').mul hα').mul
      (hr'.mul (contDiff_const.sub ho'))).mul hi'

/-- The frequency-reduced concrete amplitude. Both the literal scalar and
weight positions are inherited from `normalizedAmplitude`; only the explicit
real symbol-order factor is removed (`app:ch_regular:eq:chain-tail`). -/
def reducedNormalizedAmplitude (order : ℝ) (upper : Bool) (ρ : ℝ)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) : (ℝ × TangentialVariables E) → ℂ :=
  (ρ ^ order)⁻¹ • normalizedAmplitude upper ρ α β mi mo r xi xo

/-- Exact reconstruction, so reduction does not discard a symbol order
(`app:ch_regular:eq:chain-tail`). -/
theorem normalizedAmplitude_eq_smul_reduced {ρ : ℝ} (hρ : 0 < ρ)
    (order : ℝ) (upper : Bool) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ) (xi xo : ℝ × E) :
    normalizedAmplitude upper ρ α β mi mo r xi xo =
      ρ ^ order • reducedNormalizedAmplitude order upper ρ α β mi mo r xi xo := by
  rw [reducedNormalizedAmplitude, smul_smul, mul_inv_cancel₀ (Real.rpow_pos_of_pos hρ _).ne']
  simp

/-- All-order bounds from primitive profiles, with arbitrary real symbol
orders `pi`, `po`, `pr`. The complement has order `max 0 po`, including its
identity contribution. The original amplitude costs exactly
`ρ^(pr + max 0 po + pi)`; the reduced amplitude has grade `A_j L^(j+b)`
with `b = br + bo + bi`. Neither this offset nor the explicit constants depend
on the integration order `q`, the external bases, or the regularizer, provided
the displayed primitive profiles hold. This supplies the derivative premise
of `norm_fourierKernel_le_of_halfSpace_data` after frequency reduction
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem normalizedAmplitude_derivative_grades
    (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ) (xi xo : ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (fun ξ => mi xi (ρ • ξ)))
    (ho : ContDiff ℝ ∞ (fun ξ => mo xo (ρ • ξ)))
    (hr : ContDiff ℝ ∞ (fun ξ => r (ρ • ξ)))
    {A B I O R : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (hI : ∀ j, 0 ≤ I j)
    (hO : ∀ j, 0 ≤ O j) (hR : ∀ j, 0 ≤ R j)
    {L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
    (pi po pr : ℝ) (bi bo br : ℕ)
    (ha : ∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j)
    (hi_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => mi xi (ρ • η)) ξ‖ ≤
      ρ ^ pi * I j * L ^ (j + bi))
    (ho_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => mo xo (ρ • η)) ξ‖ ≤
      ρ ^ po * O j * L ^ (j + bo))
    (hr_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => r (ρ • η)) ξ‖ ≤
      ρ ^ pr * R j * L ^ (j + br)) (n : ℕ) (x : ℝ × TangentialVariables E) :
    (‖iteratedFDeriv ℝ n (normalizedAmplitude upper ρ α β mi mo r xi xo) x‖ ≤
      ρ ^ (pr + max 0 po + pi) * amplitudeDerivativeConstant A B I O R n *
        L ^ (n + (br + bo + bi))) ∧
    (‖iteratedFDeriv ℝ n (reducedNormalizedAmplitude (pr + max 0 po + pi)
      upper ρ α β mi mo r xi xo) x‖ ≤
        amplitudeDerivativeConstant A B I O R n * L ^ (n + (br + bo + bi))) := by
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have ho_scale : 1 ≤ ρ ^ (max 0 po) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hρ (le_max_left 0 po)
  have ho_bound' j ξ : ‖iteratedFDeriv ℝ j (fun η => mo xo (ρ • η)) ξ‖ ≤
      ρ ^ (max 0 po) * O j * L ^ (j + bo) := by
    apply (ho_bound j ξ).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hL) _)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hρ (le_max_right 0 po)) (hO j)
  have h := norm_iteratedFDeriv_normalizedAmplitude_le_scales upper ρ α β mi mo r xi xo
    hα hβ hi ho hr hA hB hI hO hR (Real.rpow_pos_of_pos hρ0 pi).le ho_scale
    (Real.rpow_pos_of_pos hρ0 pr).le hL bi bo br ha hb hi_bound ho_bound' hr_bound n x
  rw [← Real.rpow_add hρ0, ← Real.rpow_add hρ0] at h
  refine ⟨h, ?_⟩
  have hs := contDiff_normalizedAmplitude_of_frequency_profiles upper ρ α β mi mo r xi xo
    hα hβ hi ho hr
  rw [reducedNormalizedAmplitude,
    iteratedFDeriv_const_smul_apply (hs.contDiffAt.of_le (by simp)), norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.rpow_pos_of_pos hρ0 _).le)]
  calc
    _ ≤ (ρ ^ (pr + max 0 po + pi))⁻¹ *
        (ρ ^ (pr + max 0 po + pi) * amplitudeDerivativeConstant A B I O R n *
          L ^ (n + (br + bo + bi))) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Real.rpow_pos_of_pos hρ0 _).le)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hρ0 _).ne', one_mul]

end JanetCartan.FiniteChain.Retarded.KernelDecay
