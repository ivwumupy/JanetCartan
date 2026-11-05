module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Grades.SymbolJet

/-!
# Uniform grades for the actual differentiated retarded amplitudes

For `app:ch_regular:lem:finite-chain`, the exact output derivative costs `ρ^m`.
Primitive joint symbol profiles and the fixed Fourier character give an offset
`br+bi+m+bo`, independent of the integration order in
`app:ch_regular:eq:chain-tail`. Both literal orientations are preserved.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel

/-- The explicit Leibniz profile for the factored output amplitude. The zero
output symbol in the first factor leaves all actual output derivatives in the
second factor (`app:ch_regular:eq:high-amplitude`). -/
def outputAmplitudeDerivativeConstant (A B I O R W : ℕ → ℝ) (m n : ℕ) : ℝ :=
  derivativeConvolution (amplitudeDerivativeConstant A B I (fun _ => 0) R)
    (fun j => derivativeConvolution W (fun k => 1 + O k) (m + j)) n

/-- Nonnegative constants for the half-space estimate
(`app:ch_regular:eq:chain-tail`). -/
theorem outputAmplitudeDerivativeConstant_nonneg {A B I O R W : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (hI : ∀ j, 0 ≤ I j)
    (hO : ∀ j, 0 ≤ O j) (hR : ∀ j, 0 ≤ R j) (hW : ∀ j, 0 ≤ W j) (m n : ℕ) :
    0 ≤ outputAmplitudeDerivativeConstant A B I O R W m n :=
  derivativeConvolution_nonneg
    (amplitudeDerivativeConstant_nonneg hA hB hI (fun _ => le_rfl) hR)
    (fun _ => derivativeConvolution_nonneg hW (fun k => by linarith [hO k]) _) n

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def outputCovectorProjection : (ℝ × TangentialVariables E) →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.fst ℝ (ℝ × E) (ℝ × E)).comp
    ((ContinuousLinearMap.snd ℝ (ℝ × E) _).comp (ContinuousLinearMap.snd ℝ ℝ _))

private theorem norm_outputCovectorProjection_le : ‖outputCovectorProjection (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.2.2.1‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using
    (norm_fst_le x.2.2).trans ((norm_snd_le x.2).trans (norm_snd_le x))

/-- Product bounds for the actual output-differentiated amplitude, from the
primitive weights, input symbol, regularizer, joint output symbol and fixed
wave profile. No differentiated-amplitude bound is assumed. The extra grade
offset is `m`, fixed independently of integration order
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_outputDifferentiatedAmplitude_le_scales
    (upper : Bool) {ρ : ℝ} (hρ : 1 ≤ ρ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ) (xi xo : ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (fun ξ => mi xi (ρ • ξ)))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ (fun ξ => r (ρ • ξ)))
    {A B I O R W : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (hI : ∀ j, 0 ≤ I j)
    (hO : ∀ j, 0 ≤ O j) (hR : ∀ j, 0 ≤ R j) (hW : ∀ j, 0 ≤ W j)
    {Si So Sr L : ℝ} (hSi : 0 ≤ Si) (hSo : 1 ≤ So) (hSr : 0 ≤ Sr) (hL : 1 ≤ L)
    (bi bo br m : ℕ) (v : Fin m → ℝ × E) (hv : ∀ i, ‖v i‖ ≤ 1)
    (ha : ∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j)
    (hi_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => mi xi (ρ • η)) ξ‖ ≤
      Si * I j * L ^ (j + bi))
    (hr_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => r (ρ • η)) ξ‖ ≤
      Sr * R j * L ^ (j + br))
    (n : ℕ) (x : ℝ × TangentialVariables E)
    (hw : ∀ j, ‖iteratedFDeriv ℝ j
      (fun p : (ℝ × E) × (ℝ × E) => wave p.2 p.1) (0, x.2.2.1)‖ ≤ W j)
    (ho_bound : ∀ j, ‖iteratedFDeriv ℝ j (fun p : (ℝ × E) × (ℝ × E) =>
      mo (xo + ρ⁻¹ • p.1) (ρ • p.2)) (0, x.2.2.1)‖ ≤ So * O j * L ^ (j + bo)) :
    ‖iteratedFDeriv ℝ n (outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v) x‖ ≤
      ρ ^ m * (Sr * So * Si) * outputAmplitudeDerivativeConstant A B I O R W m n *
        L ^ (n + (br + bi + (m + bo))) := by
  let a := outputIndependentAmplitude upper ρ α β mi r xi
  let g := rescaledOutputSymbolJet ρ mo xo m v
  let p := outputCovectorProjection (E := E)
  have hsa : ContDiff ℝ ∞ a :=
    contDiff_normalizedAmplitude_of_frequency_profiles upper ρ α β mi (fun _ _ => 0) r xi 0
      hα hβ hi contDiff_const hr
  have hsg : ContDiff ℝ ∞ g := contDiff_rescaledOutputSymbolJet ρ ho xo m v
  have hsp : ContDiff ℝ ∞ (g ∘ p) := hsg.comp p.contDiff
  have ha' j : ‖iteratedFDeriv ℝ j a x‖ ≤
      (Sr * Si) * amplitudeDerivativeConstant A B I (fun _ => 0) R j * L ^ (j + (br + bi)) := by
    simpa only [a, outputIndependentAmplitude, mul_one, add_zero] using
      norm_iteratedFDeriv_normalizedAmplitude_le_scales upper ρ α β mi (fun _ _ => 0) r xi 0
        hα hβ hi contDiff_const hr hA hB hI (fun _ => le_rfl) hR hSi le_rfl hSr hL
        bi 0 br ha hb hi_bound (by intro k ξ; simp) hr_bound j x
  have hG j : 0 ≤ derivativeConvolution W (fun k => 1 + O k) (m + j) :=
    derivativeConvolution_nonneg hW (fun k => by linarith [hO k]) _
  have hg' j : ‖iteratedFDeriv ℝ j (g ∘ p) x‖ ≤
      So * derivativeConvolution W (fun k => 1 + O k) (m + j) * L ^ (j + (m + bo)) := by
    have hg := norm_iteratedFDeriv_rescaledOutputSymbolJet_le ρ ho xo hW hO hSo hL
      bo m j v hv x.2.2.1 hw ho_bound
    simpa only [one_pow, mul_one] using
      norm_iteratedFDeriv_comp_linear_le_grades hsg p zero_le_one
        norm_outputCovectorProjection_le hG (zero_le_one.trans hSo) (zero_le_one.trans hL)
        (m + bo) x j hg
  have hab := norm_iteratedFDeriv_mul_le_grades hsa hsp
    (amplitudeDerivativeConstant_nonneg hA hB hI (fun _ => le_rfl) hR) hG
    (mul_nonneg hSr hSi) (zero_le_one.trans hSo) (zero_le_one.trans hL)
    (br + bi) (m + bo) x ha' hg' n
  have he : outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v =
      ρ ^ m • (fun y => a y * (g ∘ p) y) := by
    funext y
    exact outputDifferentiatedAmplitude_eq_scaled_outputSymbolJet upper
      (zero_lt_one.trans_le hρ).ne' α β mi mo r xi xo m v ho y
  rw [he, iteratedFDeriv_const_smul_apply ((hsa.mul hsp).contDiffAt.of_le (by simp)), norm_smul,
    Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hρ) m)]
  apply (mul_le_mul_of_nonneg_left hab (pow_nonneg (zero_le_one.trans hρ) m)).trans_eq
  dsimp only [outputAmplitudeDerivativeConstant]
  ring

/-- A fixed carrier determines the Fourier-character constants before all
frequencies, grades, bases and directions (`app:ch_regular:eq:chain-tail`). -/
def outputCarrierWaveProfile {Ko : Set (ℝ × E)} (hKo : IsCompact Ko) : ℕ → ℝ :=
  (exists_outputJointWave_profile hKo).choose

/-- The selected carrier profile is nonnegative and bounds all joint wave jets
(`app:ch_regular:lem:finite-chain`). -/
theorem outputCarrierWaveProfile_spec {Ko : Set (ℝ × E)} (hKo : IsCompact Ko) :
    (∀ n, 0 ≤ outputCarrierWaveProfile hKo n) ∧ ∀ n ξ, ξ ∈ Ko →
      ‖iteratedFDeriv ℝ n (fun p : (ℝ × E) × (ℝ × E) => wave p.2 p.1) (0, ξ)‖ ≤
        outputCarrierWaveProfile hKo n :=
  (exists_outputJointWave_profile hKo).choose_spec

/-- Uniform all-order grades of the actual differentiated amplitude on the
common carrier, for arbitrary real primitive symbol orders. The complementary
identity changes `po` to `max 0 po`; output differentiation costs exactly `ρ^m`.
The displayed constant depends only on the primitive profiles, fixed carrier,
`m,n`, and the grade offset `br+bi+m+bo` is independent of integration order.
The joint output-symbol hypothesis is primitive; fixed buffered physical masks
supply it through `exists_bufferedMask_output_profiles`. This is the amplitude
input to the parent's half-space estimate (`app:ch_regular:eq:high-amplitude`,
`app:ch_regular:eq:chain-tail`). -/
theorem outputDifferentiatedAmplitude_derivative_grades
    (upper : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (fun ξ => mi xi (ρ • ξ)))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ (fun ξ => r (ρ • ξ)))
    {Kα Kβ Ko Ki : Set (ℝ × E)} (hKo : IsCompact Ko)
    {A B I O R : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (hI : ∀ j, 0 ≤ I j)
    (hO : ∀ j, 0 ≤ O j) (hR : ∀ j, 0 ≤ R j)
    (pi po pr : ℝ) (bi bo br m : ℕ) (v : Fin m → ℝ × E) (hv : ∀ i, ‖v i‖ ≤ 1)
    (ha : ∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j)
    (hi_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => mi xi (ρ • η)) ξ‖ ≤
      ρ ^ pi * I j * L ^ (j + bi))
    (hr_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => r (ρ • η)) ξ‖ ≤
      ρ ^ pr * R j * L ^ (j + br))
    (ho_bound : ∀ j ξ, ξ ∈ Ko → ‖iteratedFDeriv ℝ j (fun p : (ℝ × E) × (ℝ × E) =>
      mo (xo + ρ⁻¹ • p.1) (ρ • p.2)) (0, ξ)‖ ≤ ρ ^ po * O j * L ^ (j + bo))
    (n : ℕ) (x : ℝ × TangentialVariables E) (hx : x ∈ amplitudeCarrier Kα Kβ Ko Ki) :
    ‖iteratedFDeriv ℝ n (outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v) x‖ ≤
      ρ ^ m * ρ ^ (pr + max 0 po + pi) *
        outputAmplitudeDerivativeConstant A B I O R (outputCarrierWaveProfile hKo) m n *
          L ^ (n + (br + bi + (m + bo))) := by
  have hξ : x.2.2.1 ∈ Ko := by
    rcases hx with ⟨p, hp, rfl⟩
    exact hp.2.2.1
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hSo : 1 ≤ ρ ^ (max 0 po) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hρ (le_max_left 0 po)
  have ho' j : ‖iteratedFDeriv ℝ j (fun p : (ℝ × E) × (ℝ × E) =>
      mo (xo + ρ⁻¹ • p.1) (ρ • p.2)) (0, x.2.2.1)‖ ≤
      ρ ^ (max 0 po) * O j * L ^ (j + bo) := by
    apply (ho_bound j _ hξ).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hL) _)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hρ (le_max_right 0 po)) (hO j)
  have h := norm_iteratedFDeriv_outputDifferentiatedAmplitude_le_scales upper hρ
    α β mi mo r xi xo hα hβ hi ho hr hA hB hI hO hR (outputCarrierWaveProfile_spec hKo).1
    (Real.rpow_pos_of_pos hρ0 pi).le hSo (Real.rpow_pos_of_pos hρ0 pr).le hL
    bi bo br m v hv ha hb hi_bound hr_bound n x
    (fun j => (outputCarrierWaveProfile_spec hKo).2 j _ hξ) ho'
  rwa [← Real.rpow_add hρ0, ← Real.rpow_add hρ0] at h

/-- For the actual physical output mask, the joint mixed-jet premise is
discharged from the primitive normalized mask bounds. Buffered finite families
supply one such `O` uniformly for both signs through
`exists_bufferedMask_family_bounds`. Only input and regularizer orders remain
in the frequency exponent (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). -/
theorem outputDifferentiatedAmplitude_physicalMask_derivative_grades
    (upper : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L)
    (α β : ℝ × E → ℝ) (mi : (ℝ × E) → (ℝ × E) → ℂ)
    (mask : CanonicalPhase E → ℝ) (r : ℝ × E → ℂ) (xi xo : ℝ × E)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (fun ξ => mi xi (ρ • ξ))) (hm : ContDiff ℝ ∞ mask)
    (hr : ContDiff ℝ ∞ (fun ξ => r (ρ • ξ)))
    {Kα Kβ Ko Ki : Set (ℝ × E)} (hKo : IsCompact Ko)
    {A B I O R : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j) (hI : ∀ j, 0 ≤ I j)
    (hO : ∀ j, 0 ≤ O j) (hR : ∀ j, 0 ≤ R j)
    (pi pr : ℝ) (bi br m : ℕ) (v : Fin m → ℝ × E) (hv : ∀ i, ‖v i‖ ≤ 1)
    (ha : ∀ j y, ‖iteratedFDeriv ℝ j α y‖ ≤ A j)
    (hb : ∀ j y, ‖iteratedFDeriv ℝ j β y‖ ≤ B j)
    (hi_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => mi xi (ρ • η)) ξ‖ ≤
      ρ ^ pi * I j * L ^ (j + bi))
    (hr_bound : ∀ j ξ, ‖iteratedFDeriv ℝ j (fun η => r (ρ • η)) ξ‖ ≤
      ρ ^ pr * R j * L ^ (j + br))
    (hm_bound : ∀ j p, ‖iteratedFDeriv ℝ j mask p‖ ≤ O j)
    (n : ℕ) (x : ℝ × TangentialVariables E) (hx : x ∈ amplitudeCarrier Kα Kβ Ko Ki) :
    ‖iteratedFDeriv ℝ n (outputDifferentiatedAmplitude upper ρ α β mi
      (fun y ξ => (physicalMask ρ mask (y, ξ) : ℂ)) r xi xo m v) x‖ ≤
      ρ ^ m * ρ ^ (pr + pi) *
        outputAmplitudeDerivativeConstant A B I O R (outputCarrierWaveProfile hKo) m n *
          L ^ (n + (br + bi + m)) := by
  have hs : ContDiff ℝ ∞ (Function.uncurry
      (fun y ξ => (physicalMask ρ mask (y, ξ) : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_physicalMask hm ρ)
  have hp j ξ (_hξ : ξ ∈ Ko) :
      ‖iteratedFDeriv ℝ j (fun p : (ℝ × E) × (ℝ × E) =>
        (physicalMask ρ mask (xo + ρ⁻¹ • p.1, ρ • p.2) : ℂ)) (0, ξ)‖ ≤
        ρ ^ (0 : ℝ) * O j * L ^ (j + 0) := by
    simpa using norm_iteratedFDeriv_physicalMask_output_profile_le hm hO hm_bound hρ hL xo j (0, ξ)
  simpa only [max_self, add_zero] using outputDifferentiatedAmplitude_derivative_grades
    upper hρ hL α β mi (fun y ξ => (physicalMask ρ mask (y, ξ) : ℂ)) r xi xo
    hα hβ hi hs hr hKo hA hB hI hO hR pi 0 pr bi 0 br m v hv
    ha hb hi_bound hr_bound hp n x hx

end JanetCartan.FiniteChain.Retarded.KernelDecay
