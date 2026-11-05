module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.FourierKernel

/-!
# Primitive profiles for the cross-quantization Fourier kernel

The base derivative profiles are derived from the joint primitive mask
profiles. Their fixed offsets add only once under the complementary product.
All constants precede the symbols, so the statements apply to the uniform
families supplied by the protected-mask construction.
Consumer: the uniform cross estimate for `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory Set FourierTransform
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph
open FiniteChain.Retarded.KernelDecay Pseudodifferential

variable {n : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

private theorem norm_iteratedFDeriv_complex_base_slice_le
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (k : ℕ) (z η : E) :
    ‖iteratedFDeriv ℝ k (fun w ↦ (mi (w, η) : ℂ)) z‖ ≤
      ‖iteratedFDeriv ℝ k mi (z, η)‖ := by
  have hs : ContDiff ℝ ∞ (fun w ↦ mi (w, η)) :=
    hi.comp (contDiff_id.prodMk contDiff_const)
  change ‖iteratedFDeriv ℝ k (Complex.ofRealLI ∘ (fun w ↦ mi (w, η))) z‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hs.contDiffAt (by simp)]
  have h := norm_iteratedFDeriv_symbol_slice_le
    (hi.comp (contDiff_snd.prodMk contDiff_fst)) k η z
  exact h.trans_eq ((LinearIsometryEquiv.prodComm ℝ E E).norm_iteratedFDeriv_comp_right mi (η, z) k)

/-- Joint primitive mask profiles give the actual base derivatives of the
cross amplitude, with the sum of the two fixed offsets. The constant is the
existing Leibniz convolution, so accuracy never multiplies either offset
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_crossQuantization_amplitude_le
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (Di Do : ℕ → ℝ) (hDi : ∀ k, 0 ≤ Di k) (hDo : ∀ k, 0 ≤ Do k)
    (bi bo : ℕ) {L : ℝ} (hL : 1 ≤ L)
    (hij : ∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Di k * L ^ (k + bi))
    (hoj : ∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Do k * L ^ (k + bo))
    (ξ η z : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (fun w ↦ (((1 - mo (w, ξ)) * mi (w, η) : ℝ) : ℂ)) z‖ ≤
      derivativeConvolution (fun j ↦ 1 + Do j) Di k * L ^ (k + (bo + bi)) := by
  have hs : ContDiff ℝ ∞ (fun w ↦ (mi (w, η) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_id.prodMk contDiff_const))
  have ht : ContDiff ℝ ∞ (fun w ↦ (mo (w, ξ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ho.comp (contDiff_id.prodMk contDiff_const))
  have hsi j : ‖iteratedFDeriv ℝ j (fun w ↦ (mi (w, η) : ℂ)) z‖ ≤
      1 * Di j * L ^ (j + bi) := by
    simpa only [one_mul] using
      (norm_iteratedFDeriv_complex_base_slice_le mi hi j z η).trans (hij j (z, η))
  have hso j : ‖iteratedFDeriv ℝ j (fun w ↦ (mo (w, ξ) : ℂ)) z‖ ≤
      1 * Do j * L ^ (j + bo) := by
    simpa only [one_mul] using
      (norm_iteratedFDeriv_complex_base_slice_le mo ho j z ξ).trans (hoj j (z, ξ))
  have hc j := norm_iteratedFDeriv_one_sub_le_grades ht le_rfl hL bo z hso j
  have h := norm_iteratedFDeriv_mul_le_grades (contDiff_const.sub ht) hs
    (fun j ↦ by linarith [hDo j]) hDi zero_le_one zero_le_one (zero_le_one.trans hL)
    bo bi z hc hsi k
  simpa only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, one_mul] using h

/-- Uniform Fourier decay of the literal cross kernel, obtained from the
primitive joint derivative profiles and the common compact base carrier.
No kernel bound is assumed. The constants precede every varying symbol and
scale; the subsequent plateau argument converts this into `(L/ρ)^N`
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_crossQuantizationFourierKernel_frequency_decay
    (K : Set E) (hK : IsCompact K) (Di Do : ℕ → ℝ)
    (hDi : ∀ k, 0 ≤ Di k) (hDo : ∀ k, 0 ≤ Do k) (bi bo : ℕ) :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → ContDiff ℝ ∞ mo →
      Prod.fst '' tsupport mi ⊆ K →
      ∀ (ρ L : ℝ), 1 ≤ L →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Di k * L ^ (k + bi)) →
      (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Do k * L ^ (k + bo)) →
      ∀ N (ξ η : E),
        (1 + ‖(2 * Real.pi)⁻¹ • (ξ - η)‖) ^ N *
          ‖crossQuantizationFourierKernel ρ mi mo ξ η‖ ≤
            C N * L ^ (N + (bo + bi)) := by
  let D := derivativeConvolution (fun j ↦ 1 + Do j) Di
  have hD k : 0 ≤ D k := derivativeConvolution_nonneg (fun j ↦ by linarith [hDo j]) hDi k
  let B N := ∑ k ∈ Finset.range (N + 1), D k
  have hB N : 0 ≤ B N := Finset.sum_nonneg (fun k _ ↦ hD k)
  let c : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨fun N ↦ c * ((2 ^ (N - 1) * (1 + 2 ^ N)) * (volume.real K * B N)),
    fun N ↦ mul_nonneg hc (mul_nonneg (by positivity)
      (mul_nonneg measureReal_nonneg (hB N))), ?_⟩
  intro mi mo hi ho hcarrier ρ L hL hij hoj N ξ η
  let f : E → ℂ := fun z ↦ (((1 - mo (z, ρ⁻¹ • ξ)) * mi (z, ρ⁻¹ • η) : ℝ) : ℂ)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp
    ((contDiff_const.sub (ho.comp (contDiff_id.prodMk contDiff_const))).mul
      (hi.comp (contDiff_id.prodMk contDiff_const)))
  have hs : tsupport f ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    apply hcarrier
    refine ⟨(z, ρ⁻¹ • η), subset_tsupport mi ?_, rfl⟩
    intro hm
    exact hz (by simp [f, hm])
  have hfs : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport _) hs
  have hj k z : ‖iteratedFDeriv ℝ k f z‖ ≤ D k * L ^ (k + (bo + bi)) :=
    norm_iteratedFDeriv_crossQuantization_amplitude_le mi mo hi ho Di Do hDi hDo
      bi bo hL hij hoj (ρ⁻¹ • ξ) (ρ⁻¹ • η) z k
  have hint k : Integrable (iteratedFDeriv ℝ k f) :=
    ((hf.iteratedFDeriv_right (m := ∞) (i := k) (by simp)).continuous).integrable_of_hasCompactSupport
      (hfs.iteratedFDeriv k)
  have hmass : sourceDerivativeMass f N ≤
      volume.real K * B N * L ^ (N + (bo + bi)) := by
    unfold sourceDerivativeMass
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1),
          volume.real K * (D k * L ^ (N + (bo + bi))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k ≤ N := by simpa using Finset.mem_range.mp hk
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := K) (fun z hz ↦ by
            rw [image_eq_zero_of_notMem_tsupport
              (fun hh ↦ hz (hs (tsupport_iteratedFDeriv_subset k hh))), norm_zero])]
        calc
          _ ≤ ‖∫ z in K, ‖iteratedFDeriv ℝ k f z‖‖ := le_abs_self _
          _ ≤ (D k * L ^ (N + (bo + bi))) * volume.real K := by
            apply norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
            intro z _
            simpa only [norm_norm] using (hj k z).trans
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hL (Nat.add_le_add_right hkN _)) (hD k))
          _ = _ := mul_comm _ _
      _ = _ := by simp [B, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hfourier := (one_add_norm_pow_mul_norm_fourier_le_sourceDerivativeMass
    f N (hf.of_le (by simp)) (fun k _ ↦ hint k) ((2 * Real.pi)⁻¹ • (ξ - η))).trans
      (mul_le_mul_of_nonneg_left hmass (by positivity))
  rw [crossQuantizationFourierKernel_eq_fourier, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ n)]
  calc
    _ = c * ((1 + ‖(2 * Real.pi)⁻¹ • (ξ - η)‖) ^ N *
        ‖𝓕 f ((2 * Real.pi)⁻¹ • (ξ - η))‖) := by dsimp only [c, f]; ring
    _ ≤ c * ((2 ^ (N - 1) * (1 + 2 ^ N)) *
        (volume.real K * B N * L ^ (N + (bo + bi)))) :=
      mul_le_mul_of_nonneg_left hfourier hc
    _ = _ := by ring

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
