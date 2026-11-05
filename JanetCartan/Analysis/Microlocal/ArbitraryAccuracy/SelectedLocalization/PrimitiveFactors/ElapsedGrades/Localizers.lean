module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Masks
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.CutoffBudgets
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.OutputGrades

/-!
# Joint elapsed profiles of the common proof localizers

The actual buffered input and output localizers supply all three mask grades
in `CompleteFactor`: joint input, joint output, and physical output derivatives.
The Fourier character has a uniform profile on the compact elapsed carrier.
All offsets are zero, and all profiles precede the slow scale and accuracy.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open EvolutionLocalization EvolutionIntegratedLocalization FourierIntegral
open FiniteChain.Graph FiniteChain.Graph.KernelEstimates
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => ℝ × JointVariables E

/-- Supply `Qi`, `O`, `Ophysical`, and `W` for the elapsed part of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
The buffered localizers are the exact outputs of
`ProtectedMasks.exists_uniform_conic_nested_localization_data`; the compact
carriers are supplied by `exists_selected_direct_residual_carriers`.
The same output profile works jointly and on physical slices. The input
symbol retains the source base, and no source/output exchange is made for
the adjoint (`app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_elapsed_localizer_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (J : f.centers → Set V) (hJ : ∀ p, IsCompact (J p))
    (mi mo : f.centers → LocalizerSymbol (d+1))
    (Ki Ii Ko Oo : f.centers → Set (E × E))
    (hi : ∀ p, IsBufferedLocalizer (mi p) (Ki p) (Ii p))
    (ho : ∀ p, IsBufferedLocalizer (mo p) (Ko p) (Oo p)) :
    ∃ Qi O W : ℕ → ℝ,
      (∀ j, 0 ≤ Qi j) ∧ (∀ j, 0 ≤ O j) ∧ (∀ j, 0 ≤ W j) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ p y (v : V) j,
        ‖iteratedFDeriv ℝ j (fun w : V ↦ (mi p (y, w.2.2.2.1) : ℂ)) v‖ ≤
          Qi j * L ^ j) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ p u ζ j,
        ‖iteratedFDeriv ℝ j (mo p) (u, ζ)‖ ≤ O j * L ^ j) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ p u ζ j,
        ‖iteratedFDeriv ℝ j (fun t ↦ mo p (t, ζ)) u‖ ≤ O j * L ^ j) ∧
      ∀ p, ∀ v ∈ J p, ∀ j,
        ‖iteratedFDeriv ℝ j outputJointWave (0, v.2.2.2.2)‖ ≤ W j := by
  classical
  choose Di Do hDi hDo hinput houtput using
    fun p ↦ exists_elapsed_localizer_grades (hi p) (ho p)
  choose Oj hOj hOjBound using
    fun p j ↦ (ho p).compactSupport.exists_bound_iteratedFDeriv (ho p).smooth j
  have hW p := KernelEstimates.exists_outputJointWave_profile
    ((hJ p).image (show Continuous (fun v : V ↦ v.2.2.2.2) by fun_prop))
  choose W hW hWBound using hW
  let O := fun p j ↦ Oj p j + Do p j
  have hO p j : 0 ≤ O p j := add_nonneg (hOj p j) (hDo p j)
  have hsum (H : f.centers → ℕ → ℝ) (hH : ∀ p j, 0 ≤ H p j) p j :
      H p j ≤ ∑ a, H a j :=
    Finset.single_le_sum (fun a _ ↦ hH a j) (Finset.mem_univ p)
  refine ⟨fun j ↦ ∑ p, Di p j, fun j ↦ ∑ p, O p j, fun j ↦ ∑ p, W p j,
    fun j ↦ Finset.sum_nonneg (fun p _ ↦ hDi p j),
    fun j ↦ Finset.sum_nonneg (fun p _ ↦ hO p j),
    fun j ↦ Finset.sum_nonneg (fun p _ ↦ hW p j), ?_, ?_, ?_, ?_⟩
  · intro L hL p y v j
    let g : JointVariables E → ℂ := fun w ↦ (mi p (y, w.2.2.1) : ℂ)
    have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp
      ((hi p).smooth.comp (contDiff_const.prodMk contDiff_snd.snd.fst))
    let π : V →L[ℝ] JointVariables E := ContinuousLinearMap.snd ℝ _ _
    have hb := RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.norm_iteratedFDeriv_preAffine_le
      π 0 isOpen_univ hg.contDiffOn (mem_univ _) j (x := v)
    simp only [add_zero] at hb
    have hb' := hb.trans ((mul_le_mul_of_nonneg_right (hinput p L hL y j v.2)
      (pow_nonneg (norm_nonneg π) j)).trans
      (mul_le_of_le_one_right (mul_nonneg (hDi p j) (pow_nonneg (zero_le_one.trans hL) j))
        (pow_le_one₀ (norm_nonneg π) (ContinuousLinearMap.norm_snd_le ℝ _ _))))
    exact hb'.trans (mul_le_mul_of_nonneg_right (hsum Di hDi p j)
      (pow_nonneg (zero_le_one.trans hL) j))
  · intro L hL p u ζ j
    apply (hOjBound p j j le_rfl (u, ζ)).trans
    apply (le_add_of_nonneg_right (hDo p j)).trans
    exact (hsum O hO p j).trans (le_mul_of_one_le_right
      (Finset.sum_nonneg (fun a _ ↦ hO a j)) (one_le_pow₀ hL))
  · intro L hL p u ζ j
    apply (houtput p L hL u ζ j).trans
    exact mul_le_mul_of_nonneg_right
      ((le_add_of_nonneg_left (hOj p j)).trans (hsum O hO p j))
      (pow_nonneg (zero_le_one.trans hL) j)
  · intro p v hv j
    exact (hWBound p j v.2.2.2.2 (mem_image_of_mem _ hv)).trans (hsum W hW p j)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
