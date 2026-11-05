module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerJets.Frequency

/-!
# Identity-leakage Fourier jets uniform over the selected masks

A common compact frequency carrier and the published common joint derivative
profiles determine the constants before the masks or coefficient fields vary.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Set
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph KernelEstimates
open FiniteChain.Retarded.KernelDecay
variable {n : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The literal differentiated identity amplitude has one Fourier-decay constant
for every mask pair with the SAME carrier and joint profiles. These inputs are
supplied by the canonical support and derivative clauses of
`SelectedSectorEvenNestedMaskConclusion`; neither a kernel estimate nor an
operator estimate is assumed. Consumer: uniform identity leakage in the
complete residual (`app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageJetAmplitude_fourier_decay_of_uniform_profiles
    (R : ℝ) (I O : ℕ → ℝ) (hI : ∀ k, 0 ≤ I k) (hO : ∀ k, 0 ≤ O k)
    (j N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → Prod.snd '' tsupport mi ⊆ Metric.closedBall (0 : E) R →
      (∀ k z, ‖iteratedFDeriv ℝ k mi z‖ ≤ I k) →
      (∀ k z, ‖iteratedFDeriv ℝ k mo z‖ ≤ O k) →
      ∀ (ρ : ℝ), 1 ≤ ρ → ∀ x y : E,
      ∀ v : Fin j → E, (∀ i, ‖v i‖ ≤ 1) → ∀ θ : E,
      (1 + ‖θ‖) ^ N * ‖𝓕 (identityLeakageJetAmplitude ρ mi mo x y j v) θ‖ ≤ C := by
  obtain ⟨W, hW, hw⟩ := KernelEstimates.exists_outputJointWave_profile
    (isCompact_closedBall (0 : E) R)
  let P := fun k ↦ derivativeConvolution W (fun l ↦ 1 + O l) (j + k)
  have hP k : 0 ≤ P k := derivativeConvolution_nonneg hW (fun l ↦ by linarith [hO l]) _
  let D := derivativeConvolution P I
  have hD k : 0 ≤ D k := derivativeConvolution_nonneg hP hI k
  let V := volume.real (Metric.closedBall (0 : E) R)
  refine ⟨(2 ^ (N - 1) * (1 + 2 ^ N)) *
    (∑ k ∈ Finset.range (N + 1), V * D k),
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun k _ ↦ mul_nonneg (by dsimp [V]; positivity) (hD k))), ?_⟩
  intro mi mo hi his ho hR hiBound hoBound ρ hρ x y v hv θ
  let f := identityLeakageJetAmplitude ρ mi mo x y j v
  obtain ⟨hf, hs⟩ := identityLeakageJetAmplitude_smooth_support ρ mi mo hi his ho x y j v
  have hc : HasCompactSupport f :=
    (his.image continuous_snd).of_isClosed_subset (isClosed_tsupport _) hs
  have hsR : tsupport f ⊆ Metric.closedBall (0 : E) R := hs.trans hR
  have hj k η (hη : η ∈ Metric.closedBall (0 : E) R) :
      ‖iteratedFDeriv ℝ k f η‖ ≤ D k := by
    have hoGrade l : ‖iteratedFDeriv ℝ l (graphOutputSymbolJet ρ mo x j v) η‖ ≤ P l := by
      simpa only [one_pow, mul_one] using
        norm_iteratedFDeriv_graphOutputSymbolJet_le ρ ho x hW hO
          (L := 1) le_rfl 0 j l v hv η (fun t ↦ hw t η hη)
          (fun t ↦ by
            simpa only [one_pow, mul_one] using
              (norm_iteratedFDeriv_rescaled_graphMask_le ho hρ x t (0, η)).trans
                (hoBound t _))
    have hiSmooth : ContDiff ℝ ∞ (fun η : E ↦ (mi (y, η) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_const.prodMk contDiff_id))
    have hiGrade l : ‖iteratedFDeriv ℝ l (fun η ↦ (mi (y, η) : ℂ)) η‖ ≤ I l := by
      change ‖iteratedFDeriv ℝ l (Complex.ofRealLI ∘ fun η ↦ mi (y, η)) η‖ ≤ I l
      have hsReal : ContDiff ℝ ∞ (fun η : E ↦ mi (y, η)) :=
        hi.comp (contDiff_const.prodMk contDiff_id)
      rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hsReal.contDiffAt (by simp)]
      exact (norm_iteratedFDeriv_symbol_slice_le hi l y η).trans (hiBound l _)
    change ‖iteratedFDeriv ℝ k
      (fun η ↦ graphOutputSymbolJet ρ mo x j v η * (mi (y, η) : ℂ)) η‖ ≤
        derivativeConvolution P I k
    simpa only [one_pow, mul_one, one_mul] using
      norm_iteratedFDeriv_mul_le_grades
        (contDiff_graphOutputSymbolJet ρ ho x j v)
        hiSmooth
        hP hI (S := 1) (T := 1) (L := 1) zero_le_one zero_le_one zero_le_one
        0 0 η (fun l ↦ by simpa using hoGrade l) (fun l ↦ by simpa using hiGrade l) k
  have hint k : Integrable (iteratedFDeriv ℝ k f) :=
    (hf.continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport (hc.iteratedFDeriv k)
  have hmass : Pseudodifferential.sourceDerivativeMass f N ≤
      ∑ k ∈ Finset.range (N + 1), V * D k := by
    apply Finset.sum_le_sum
    intro k _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Metric.closedBall (0 : E) R) (fun η hη ↦ by
        rw [image_eq_zero_of_notMem_tsupport
          (fun hh ↦ hη (hsR (tsupport_iteratedFDeriv_subset k hh))), norm_zero])]
    calc
      _ ≤ ‖∫ η in Metric.closedBall (0 : E) R, ‖iteratedFDeriv ℝ k f η‖‖ := le_abs_self _
      _ ≤ D k * V := by
        apply norm_setIntegral_le_of_norm_le_const
          (isCompact_closedBall (0 : E) R).measure_lt_top
        intro η hη
        simpa only [norm_norm] using hj k η hη
      _ = V * D k := mul_comm _ _
  exact (Pseudodifferential.one_add_norm_pow_mul_norm_fourier_le_sourceDerivativeMass
    f N (hf.of_le (by simp)) (fun k _ ↦ hint k) θ).trans
      (mul_le_mul_of_nonneg_left hmass (by positivity))


end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
