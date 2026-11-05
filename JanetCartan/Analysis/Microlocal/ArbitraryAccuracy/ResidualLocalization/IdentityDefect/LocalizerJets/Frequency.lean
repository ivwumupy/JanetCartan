module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerDecay
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.OutputGrades

/-!
# Frequency grades of the differentiated identity leakage

The same right input mask multiplies the existing exact graph output-symbol
jet. Fixed compact mask derivatives produce its Fourier decay, uniformly in
the physical scale and unit output directions. Consumer: the differentiated
identity kernel in `app:ch_regular:eq:chain-tail`.
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
set_option maxHeartbeats 1000000

/-- The exact normalized output jet retains both the complementary output
symbol and the original right input symbol (`app:ch_regular:eq:chain-tail`). -/
def identityLeakageJetAmplitude (ρ : ℝ) (mi mo : LocalizerSymbol n)
    (x y : E) (j : ℕ) (v : Fin j → E) (η : E) : ℂ :=
  graphOutputSymbolJet ρ mo x j v η * (mi (y, η) : ℂ)

/-- Compact support and smoothness of the differentiated amplitude come from
its original input mask; no estimated kernel is an input
(`app:ch_regular:eq:chain-tail`). -/
theorem identityLeakageJetAmplitude_smooth_support (ρ : ℝ)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (x y : E) (j : ℕ) (v : Fin j → E) :
    ContDiff ℝ ∞ (identityLeakageJetAmplitude ρ mi mo x y j v) ∧
      tsupport (identityLeakageJetAmplitude ρ mi mo x y j v) ⊆ Prod.snd '' tsupport mi := by
  refine ⟨(contDiff_graphOutputSymbolJet ρ ho x j v).mul
    (Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_const.prodMk contDiff_id))), ?_⟩
  apply closure_minimal _ (his.image continuous_snd).isClosed
  intro η hη
  refine ⟨(y, η), subset_tsupport mi ?_, rfl⟩
  intro hz
  exact hη (by simp [identityLeakageJetAmplitude, hz])

/-- Arbitrary Fourier decay of the actual normalized differentiated amplitude.
The constant precedes the physical scale, external bases and unit directions;
all analytic inputs are fixed smooth compact mask jets. This is consumed by
`exists_identityLeakageScalarKernel_jet_decay`
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_identityLeakageJetAmplitude_fourier_decay
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo) (j N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 1 ≤ ρ → ∀ x y : E,
      ∀ v : Fin j → E, (∀ i, ‖v i‖ ≤ 1) → ∀ θ : E,
      (1 + ‖θ‖) ^ N * ‖𝓕 (identityLeakageJetAmplitude ρ mi mo x y j v) θ‖ ≤ C := by
  choose I hI hiBound using fun k ↦ his.exists_bound_iteratedFDeriv hi k
  choose O hO hoBound using fun k ↦ hos.exists_bound_iteratedFDeriv ho k
  obtain ⟨R, _, hR⟩ := (his.image continuous_snd).isBounded.subset_closedBall_lt 0 (0 : E)
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
  intro ρ hρ x y v hv θ
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
                (hoBound t t le_rfl _))
    have hiSmooth : ContDiff ℝ ∞ (fun η : E ↦ (mi (y, η) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_const.prodMk contDiff_id))
    have hiGrade l : ‖iteratedFDeriv ℝ l (fun η ↦ (mi (y, η) : ℂ)) η‖ ≤ I l := by
      change ‖iteratedFDeriv ℝ l (Complex.ofRealLI ∘ fun η ↦ mi (y, η)) η‖ ≤ I l
      have hsReal : ContDiff ℝ ∞ (fun η : E ↦ mi (y, η)) :=
        hi.comp (contDiff_const.prodMk contDiff_id)
      rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hsReal.contDiffAt (by simp)]
      exact (norm_iteratedFDeriv_symbol_slice_le hi l y η).trans (hiBound l l le_rfl _)
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
