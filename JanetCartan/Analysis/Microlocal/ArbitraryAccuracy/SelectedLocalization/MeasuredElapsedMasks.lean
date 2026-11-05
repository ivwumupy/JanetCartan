module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredAmplitudeProfiles

/-!
# Primitive elapsed grades for the original measurement masks

Fixed measurement cutoffs contribute a uniform Leibniz profile before charts,
coefficients and scales. The original primitive offsets and carriers remain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Retarded.KernelDecay EvolutionLocalization.PrimitiveGrades
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => ℝ × JointVariables E

/-- A fixed physical measurement cutoff has uniform grades under the actual
elapsed coordinate contractions (`app:ch_regular:eq:high-amplitude`). -/
private theorem exists_measurement_elapsed_contraction_profile
    (μ : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (l : V →L[ℝ] E), ‖l‖ ≤ 1 → ∀ k v,
        ‖iteratedFDeriv ℝ k (fun w : V ↦ (μ (l w) : ℂ)) v‖ ≤ C k := by
  have hm : ContDiff ℝ ∞ (fun y ↦ (μ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hμ
  have hmc : HasCompactSupport (fun y ↦ (μ y : ℂ)) :=
    hμc.comp_left Complex.ofReal_zero
  choose C hC hbound using fun k ↦ hmc.exists_bound_iteratedFDeriv hm k
  refine ⟨C, hC, ?_⟩
  intro l hl k v
  have h := norm_iteratedFDeriv_affine_contraction_le l hl 0
    isOpen_univ hm.contDiffOn (mem_univ (l v+0)) k
  simp only [add_zero] at h
  exact h.trans (hbound k k le_rfl (l v))

/-- The two original measurement masks give the primitive elapsed input/output
mask profiles, with the original offsets and carrier unchanged. Constants are
chosen before the chart, elapsed carrier, coefficients and slow scale. Consumer:
`hprimitiveMasks` of the supported integral leakage estimate
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular_base:eq:measured-adjoint`). -/
theorem exists_measured_elapsed_mask_profiles
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (Qt Qs : ℕ → ℝ) (hQt : ∀ k, 0 ≤ Qt k) (hQs : ∀ k, 0 ≤ Qs k) :
    ∃ Qtm Qsm : ℕ → ℝ, (∀ k, 0 ≤ Qtm k) ∧ (∀ k, 0 ≤ Qsm k) ∧
      ∀ (e : E ≃ₗᵢ[ℝ] E) (L : ℝ), 1 ≤ L →
      ∀ (χout χsource : E → ℂ), ContDiff ℝ ∞ χout → ContDiff ℝ ∞ χsource →
      ∀ (bt bs : ℕ) (K : Set V),
      (∀ v ∈ K, ∀ k, ‖iteratedFDeriv ℝ k (fun w : V ↦ χout w.2.1.1) v‖ ≤
        Qt k * L ^ (k+bt)) →
      (∀ v ∈ K, ∀ k, ‖iteratedFDeriv ℝ k (fun w : V ↦ χsource w.2.1.2) v‖ ≤
        Qs k * L ^ (k+bs)) →
      ∀ v ∈ K, ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : V ↦ (μ (e w.2.1.1) : ℂ)*χout w.2.1.1) v‖ ≤
          Qtm k * L ^ (k+bt) ∧
        ‖iteratedFDeriv ℝ k (fun w : V ↦ (ν (e w.2.1.2) : ℂ)*χsource w.2.1.2) v‖ ≤
          Qsm k * L ^ (k+bs) := by
  obtain ⟨Ct, hCt, hCtbound⟩ := exists_measurement_elapsed_contraction_profile μ hμ hμc
  obtain ⟨Cs, hCs, hCsbound⟩ := exists_measurement_elapsed_contraction_profile ν hν hνc
  refine ⟨derivativeConvolution Ct Qt, derivativeConvolution Cs Qs,
    derivativeConvolution_nonneg hCt hQt, derivativeConvolution_nonneg hCs hQs, ?_⟩
  intro e L hL χout χsource ht hs bt bs K htb hsb v hv k
  let ec := e.toContinuousLinearEquiv.toContinuousLinearMap
  let pt : V →L[ℝ] E := ec.comp ((ContinuousLinearMap.fst ℝ E E).comp
    ((ContinuousLinearMap.fst ℝ (E × E) _).comp (ContinuousLinearMap.snd ℝ ℝ _)))
  let ps : V →L[ℝ] E := ec.comp ((ContinuousLinearMap.snd ℝ E E).comp
    ((ContinuousLinearMap.fst ℝ (E × E) _).comp (ContinuousLinearMap.snd ℝ ℝ _)))
  have hpt : ‖pt‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    change ‖e w.2.1.1‖ ≤ 1 * ‖w‖
    rw [e.norm_map, one_mul]
    exact (norm_fst_le w.2.1).trans ((norm_fst_le w.2).trans (norm_snd_le w))
  have hps : ‖ps‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    change ‖e w.2.1.2‖ ≤ 1 * ‖w‖
    rw [e.norm_map, one_mul]
    exact (norm_snd_le w.2.1).trans ((norm_fst_le w.2).trans (norm_snd_le w))
  have hmt : ContDiff ℝ ∞ (fun w : V ↦ (μ (e w.2.1.1) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hμ).comp pt.contDiff
  have hms : ContDiff ℝ ∞ (fun w : V ↦ (ν (e w.2.1.2) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hν).comp ps.contDiff
  have htm j : ‖iteratedFDeriv ℝ j (fun w : V ↦ (μ (e w.2.1.1) : ℂ)) v‖ ≤ Ct j * L ^ (j+0) :=
    (hCtbound pt hpt j v).trans (le_mul_of_one_le_right (hCt j) (one_le_pow₀ hL))
  have hsm j : ‖iteratedFDeriv ℝ j (fun w : V ↦ (ν (e w.2.1.2) : ℂ)) v‖ ≤ Cs j * L ^ (j+0) :=
    (hCsbound ps hps j v).trans (le_mul_of_one_le_right (hCs j) (one_le_pow₀ hL))
  constructor
  · have h := norm_iteratedFDeriv_smul_le_amplitude_grades hmt
      (ht.comp contDiff_snd.fst.fst) hCt (S := 1) (zero_le_one.trans hL) 0 bt v htm
      (fun j ↦ by simpa only [one_mul, Function.comp_def] using htb v hv j) k
    simpa only [smul_eq_mul, one_mul, zero_add, Function.comp_def] using h
  · have h := norm_iteratedFDeriv_smul_le_amplitude_grades hms
      (hs.comp contDiff_snd.fst.snd) hCs (S := 1) (zero_le_one.trans hL) 0 bs v hsm
      (fun j ↦ by simpa only [one_mul, Function.comp_def] using hsb v hv j) k
    simpa only [smul_eq_mul, one_mul, zero_add, Function.comp_def] using h

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
