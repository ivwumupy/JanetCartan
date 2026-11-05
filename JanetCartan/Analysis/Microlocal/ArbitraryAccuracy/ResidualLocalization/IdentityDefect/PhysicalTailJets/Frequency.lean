module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalKernel

/-!
# Uniform Fourier jets of the fixed localizer slices

The constants in the physical tail jet estimate come from compactly supported
jets of the original symbol. These are the frequency estimates consumed by
`exists_rightLocalizerScalarKernel_physicalTail_jet_decay`, for
`app:ch_regular:eq:chain-tail` and `app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailJets

open FourierIntegral FiniteChain.Graph FiniteChain.Retarded.KernelDecay
variable {n : ℕ}
local notation "E" => Euclidean n

/-- The normalized frequency slice retains the compact frequency projection of
the original mask (`app:ch_regular:eq:chain-tail`). -/
theorem hasCompactSupport_frequencySlice (mi : LocalizerSymbol n)
    (his : HasCompactSupport mi) (y : E) :
    HasCompactSupport (fun η ↦ (mi (y, η) : ℂ)) := by
  apply (his.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (his.image continuous_snd).isClosed
  intro η hη
  refine ⟨(y, η), subset_tsupport mi ?_, rfl⟩
  simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hη

/-- All polynomially weighted frequency jets are integrable on the actual
Euclidean volume (`app:ch_regular:eq:chain-tail`). -/
theorem integrable_frequencySlice_jet_moment (mi : LocalizerSymbol n)
    (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) (y : E) (k q : ℕ) :
    Integrable (fun η ↦ ‖η‖ ^ k *
      ‖iteratedFDeriv ℝ q (fun η ↦ (mi (y, η) : ℂ)) η‖) := by
  have hs : ContDiff ℝ ∞ (fun η ↦ (mi (y, η) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_const.prodMk contDiff_id))
  exact ((continuous_norm.pow k).mul
    (hs.continuous_iteratedFDeriv (by simp)).norm).integrable_of_hasCompactSupport
      (((hasCompactSupport_frequencySlice mi his y).iteratedFDeriv q).norm.mul_left)

private theorem exists_uniform_frequencySlice_jet_moment (mi : LocalizerSymbol n)
    (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) (k q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E,
      (∫ η, ‖η‖ ^ k * ‖iteratedFDeriv ℝ q (fun η ↦ (mi (y, η) : ℂ)) η‖) ≤ C := by
  let a : E × E → ℂ := fun p ↦ (mi p : ℂ)
  have ha : ContDiff ℝ ∞ a := Complex.ofRealCLM.contDiff.comp hi
  have hca : HasCompactSupport a := his.comp_left (g := fun t : ℝ ↦ (t : ℂ)) rfl
  obtain ⟨B, hB, hb⟩ := hca.exists_bound_iteratedFDeriv ha q
  obtain ⟨R, hRpos, hR⟩ :=
    (his.image continuous_snd).isBounded.subset_closedBall_lt 0 (0 : E)
  refine ⟨R ^ k * B * volume.real (Metric.closedBall (0 : E) R), by positivity, ?_⟩
  intro y
  have hs : tsupport (fun η ↦ a (y, η)) ⊆ Metric.closedBall (0 : E) R := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro η hη
    apply hR
    refine ⟨(y, η), subset_tsupport mi ?_, rfl⟩
    simpa only [a, Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hη
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Metric.closedBall (0 : E) R) (fun η hη ↦ by
      rw [image_eq_zero_of_notMem_tsupport
        (fun hh ↦ hη (hs (tsupport_iteratedFDeriv_subset q hh))), norm_zero, mul_zero])]
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_setIntegral_le_of_norm_le_const
    (isCompact_closedBall (0 : E) R).measure_lt_top
  intro η hη
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (by simpa using hη) k)
    ((norm_iteratedFDeriv_symbol_slice_le ha q y η).trans (hb q le_rfl (y, η)))
    (norm_nonneg _) (by positivity)

private theorem exists_uniform_frequencySlice_fourier_jet_pow_bound
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (j N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y θ : E,
      ‖θ‖ ^ N * ‖iteratedFDeriv ℝ j (𝓕 (fun η ↦ (mi (y, η) : ℂ))) θ‖ ≤ C := by
  choose B hB hb using exists_uniform_frequencySlice_jet_moment mi hi his
  refine ⟨(2 * Real.pi) ^ j * (2 * j + 2) ^ N *
    ∑ p ∈ Finset.range (j + 1) ×ˢ Finset.range (N + 1), B p.1 p.2,
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun p _ ↦ hB p.1 p.2)), ?_⟩
  intro y θ
  have hs : ContDiff ℝ ∞ (fun η ↦ (mi (y, η) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_const.prodMk contDiff_id))
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (N := ⊤)
    hs (fun k q _ _ ↦ integrable_frequencySlice_jet_moment mi hi his y k q)
    (k := j) (n := N) (by simp) (by simp) θ
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum fun p _ ↦ hb p.1 p.2 y

/-- Uniform rapid decay of every Fourier jet, derived from the fixed compact
symbol jets. Consumed by the rescaled physical kernel jet estimate
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_uniform_frequencySlice_fourier_jet_decay
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (j N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y θ : E,
      (1 + ‖θ‖) ^ N *
        ‖iteratedFDeriv ℝ j (𝓕 (fun η ↦ (mi (y, η) : ℂ))) θ‖ ≤ C := by
  obtain ⟨B₀, hB₀, hb₀⟩ := exists_uniform_frequencySlice_fourier_jet_pow_bound mi hi his j 0
  obtain ⟨B, hB, hb⟩ := exists_uniform_frequencySlice_fourier_jet_pow_bound mi hi his j N
  refine ⟨2 ^ (N - 1) * (B₀ + B), by positivity, ?_⟩
  intro y θ
  have hzero := hb₀ y θ
  simp only [pow_zero, one_mul] at hzero
  calc
    _ ≤ (2 ^ (N - 1) * (1 + ‖θ‖ ^ N)) *
        ‖iteratedFDeriv ℝ j (𝓕 (fun η ↦ (mi (y, η) : ℂ))) θ‖ := by
      gcongr
      simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg θ) N
    _ = 2 ^ (N - 1) *
        (‖iteratedFDeriv ℝ j (𝓕 (fun η ↦ (mi (y, η) : ℂ))) θ‖ +
          ‖θ‖ ^ N * ‖iteratedFDeriv ℝ j (𝓕 (fun η ↦ (mi (y, η) : ℂ))) θ‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hzero (hb y θ)) (by positivity)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailJets
