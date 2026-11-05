module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Noncomparable.FrequencyIntegration

/-!
# Symbol bounds without covector differentiation

The common-base argument for `app:ch_regular:lem:finite-chain` needs only values
of the input symbol and regularizer and base jets of the output symbol. These
bounds remain usable when the two shell scales have an unbounded ratio.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The fixed normalized output carrier bounds the base derivatives of its
Fourier characters. No covector derivative is required
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_outputBaseWave_profile {Ko : Set (ℝ × E)} (hKo : IsCompact Ko) :
    ∃ W : ℕ → ℝ, (∀ j, 0 ≤ W j) ∧ ∀ j ξ, ξ ∈ Ko →
      ‖iteratedFDeriv ℝ j (wave ξ) 0‖ ≤ W j := by
  have hc j : Continuous (fun ξ : ℝ × E => iteratedFDeriv ℝ j (wave ξ) 0) := by
    exact ((contDiff_outputJet (contDiff_outputJointWave (E := E)) j).continuous.comp
      (continuous_const.prodMk continuous_id))
  have hb j := hKo.exists_bound_of_continuousOn (hc j).continuousOn
  choose C hC using hb
  exact ⟨fun j => max 0 (C j), fun j => le_max_left _ _,
    fun j ξ hξ => (hC j ξ hξ).trans (le_max_right _ _)⟩

/-- A fixed choice of Fourier-character profile on the normalized carrier,
chosen independently of both shell scales (`app:ch_regular:eq:chain-tail`). -/
def outputBaseWaveProfile {Ko : Set (ℝ × E)} (hKo : IsCompact Ko) : ℕ → ℝ :=
  (exists_outputBaseWave_profile hKo).choose

/-- The chosen profile discharges the wave-profile premise of the concrete
unequal-shell bounds (`app:ch_regular:eq:chain-tail`). -/
theorem outputBaseWaveProfile_spec {Ko : Set (ℝ × E)} (hKo : IsCompact Ko) :
    (∀ j, 0 ≤ outputBaseWaveProfile hKo j) ∧ ∀ j ξ, ξ ∈ Ko →
      ‖iteratedFDeriv ℝ j (wave ξ) 0‖ ≤ outputBaseWaveProfile hKo j :=
  (exists_outputBaseWave_profile hKo).choose_spec

/-- Only output-base symbol derivatives enter the fixed scalar jet bound.
The identity part of the complementary symbol is retained, and the output
order contributes `m+bo`, independently of the integration order `q`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_rescaledOutputSymbolJet_le_base_grades
    (ρ : ℝ) {mo : (ℝ × E) → (ℝ × E) → ℂ}
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (xo : ℝ × E)
    {W O : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    {S L : ℝ} (hS : 1 ≤ S) (hL : 1 ≤ L) (bo m : ℕ)
    (v : Fin m → ℝ × E) (hv : ∀ i, ‖v i‖ ≤ 1) (ξ : ℝ × E)
    (hw : ∀ k, ‖iteratedFDeriv ℝ k (wave ξ) 0‖ ≤ W k)
    (hb : ∀ k, ‖iteratedFDeriv ℝ k (fun y : ℝ × E =>
      mo (xo + ρ⁻¹ • y) (ρ • ξ)) 0‖ ≤ S * O k * L ^ (k + bo)) :
    ‖rescaledOutputSymbolJet ρ mo xo m v ξ‖ ≤
      S * derivativeConvolution W (fun k => 1 + O k) m * L ^ (m + bo) := by
  have hs : ContDiff ℝ ∞ (fun y : ℝ × E => mo (xo + ρ⁻¹ • y) (ρ • ξ)) :=
    ho.comp (show ContDiff ℝ ∞ (fun y : ℝ × E => (xo + ρ⁻¹ • y, ρ • ξ)) from by fun_prop)
  have hsw : ContDiff ℝ ∞ (wave ξ) :=
    contDiff_outputJointWave.comp (contDiff_id.prodMk contDiff_const)
  have hw' k : ‖iteratedFDeriv ℝ k (wave ξ) 0‖ ≤ 1 * W k * L ^ (k + 0) := by
    simpa using (hw k).trans (le_mul_of_one_le_right (hW k) (one_le_pow₀ hL))
  have hc k := norm_iteratedFDeriv_one_sub_le_grades hs hS hL bo 0 hb k
  have hp := norm_iteratedFDeriv_mul_le_grades hsw (contDiff_const.sub hs)
    hW (fun k => by linarith [hO k]) zero_le_one (zero_le_one.trans hS)
    (zero_le_one.trans hL) 0 bo 0 hw' hc m
  have hn := (iteratedFDeriv ℝ m
    (fun y => wave ξ y * (1 - mo (xo + ρ⁻¹ • y) (ρ • ξ))) 0).le_opNorm v
  have hv' : (∏ i, ‖v i‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)
  exact (hn.trans (mul_le_of_le_one_right (norm_nonneg _) hv')).trans (by simpa using hp)

/-- Primitive pointwise input/regularizer bounds and output-base jets bound
the actual frequency-only factor. No symbol is differentiated in a frequency
variable, so no ratio of the two shell scales is lost
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_outputFrequencyFactor_le_base_grades
    (ρ : ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    {W O : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    {Si So Sr I R L : ℝ} (hSi : 0 ≤ Si) (hSo : 1 ≤ So) (hSr : 0 ≤ Sr)
    (hI : 0 ≤ I) (hR : 0 ≤ R) (hL : 1 ≤ L) (bi bo br m : ℕ)
    (v : Fin m → ℝ × E) (hv : ∀ i, ‖v i‖ ≤ 1)
    (w : (ℝ × E) × (ℝ × E))
    (hi : ‖mi xi (ρ • w.2)‖ ≤ Si * I * L ^ bi)
    (hr : ‖r (ρ • w.1)‖ ≤ Sr * R * L ^ br)
    (hw : ∀ k, ‖iteratedFDeriv ℝ k (wave w.1) 0‖ ≤ W k)
    (hb : ∀ k, ‖iteratedFDeriv ℝ k (fun y : ℝ × E =>
      mo (xo + ρ⁻¹ • y) (ρ • w.1)) 0‖ ≤ So * O k * L ^ (k + bo)) :
    ‖outputFrequencyFactor ρ mi mo r xi xo m v w‖ ≤
      (R * I * derivativeConvolution W (fun k => 1 + O k) m) *
        (Sr * Si * So) * L ^ (br + bi + (m + bo)) := by
  have hj := norm_rescaledOutputSymbolJet_le_base_grades ρ ho xo hW hO hSo hL bo m v hv w.1 hw hb
  unfold outputFrequencyFactor
  rw [norm_mul, norm_mul]
  have hL0 := zero_le_one.trans hL
  have hri := mul_le_mul hr hi (norm_nonneg _)
    (mul_nonneg (mul_nonneg hSr hR) (pow_nonneg hL0 _))
  apply (mul_le_mul hri hj (norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg hSr hR) (pow_nonneg hL0 _))
      (mul_nonneg (mul_nonneg hSi hI) (pow_nonneg hL0 _)))).trans_eq
  simp only [pow_add]
  ring

/-- Replacing either shell scale by the larger scale costs only the positive
part of its fixed symbol order. This includes the bounded shoulder `σ = 1`
(`app:ch_regular:eq:chain-tail`). -/
theorem shell_symbol_order_le {σ ρ : ℝ} (hσ : 1 ≤ σ) (hσρ : σ ≤ ρ) (p : ℝ) :
    σ ^ p ≤ ρ ^ (max 0 p) := by
  exact (Real.rpow_le_rpow_of_exponent_le hσ (le_max_right 0 p)).trans
    (Real.rpow_le_rpow (zero_le_one.trans hσ) hσρ (le_max_left 0 p))

/-- Physical output-base jets imply the rescaled base-jet premise used in the
unequal-shell estimate. No frequency derivative of a smaller-shell cutoff is
introduced (`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_rescaled_output_base_derivative_le
    {ρ σ L : ℝ} (hρ : 1 ≤ ρ) (hσ : 1 ≤ σ) (hσρ : σ ≤ ρ) (hL : 0 ≤ L)
    {mo : (ℝ × E) → (ℝ × E) → ℂ} (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (xo ξ : ℝ × E) (p O : ℝ) (hO : 0 ≤ O) (k bo : ℕ)
    (hb : ‖iteratedFDeriv ℝ k (fun y => mo y (ρ • ξ)) xo‖ ≤
      σ ^ p * O * L ^ (k + bo)) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ × E => mo (xo + ρ⁻¹ • y) (ρ • ξ)) 0‖ ≤
      ρ ^ (max 0 p) * O * L ^ (k + bo) := by
  let g : ℝ × E → ℂ := fun y => mo (xo + y) (ρ • ξ)
  have hg : ContDiff ℝ ∞ g := ho.comp
    (show ContDiff ℝ ∞ (fun y : ℝ × E => (xo + y, ρ • ξ)) from by fun_prop)
  change ‖iteratedFDeriv ℝ k (fun y => g (ρ⁻¹ • y)) 0‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul ρ⁻¹ (hg.of_le (by simp))]
  dsimp only
  rw [smul_zero, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans hρ)) _)]
  have hinv : ρ⁻¹ ^ k ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hρ)
  have hb' : ‖iteratedFDeriv ℝ k g 0‖ ≤ σ ^ p * O * L ^ (k + bo) := by
    have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
      (f := fun y => mo y (ρ • ξ)) k xo (0 : ℝ × E)
    rw [add_zero] at ht
    change ‖iteratedFDeriv ℝ k (fun y => mo (xo + y) (ρ • ξ)) 0‖ ≤ _
    rw [ht]
    exact hb
  exact (mul_le_of_le_one_left (norm_nonneg _) hinv).trans
    (hb'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (shell_symbol_order_le hσ hσρ p) hO) (pow_nonneg hL _)))

end JanetCartan.FiniteChain.Retarded.KernelDecay
