module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.EvenConclusion
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.CutoffBudgets

/-!
# Uniform analytic grades of the actual selected even proof masks

The common joint profile from the protected construction controls the precise
input and output slices in both the elapsed and PDO estimates. No new bound
is selected after the varying coefficient field or the mask witnesses.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open SymbolBudgets FiniteChain.Graph FourierIntegral
open ProtectedMasks SelectedEvenProofMasks
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Affine slices preserve the SAME joint profile. This is the zero-offset
input/output mask calculation for `app:ch_regular:eq:chain-tail`. -/
theorem selected_localizer_slices_le_joint_profile
    (m : LocalizerSymbol (d + 1)) (hm : ContDiff ℝ ∞ m)
    (H : ℕ → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hjet : ∀ j z, ‖iteratedFDeriv ℝ j m z‖ ≤ H j)
    {L : ℝ} (hL : 1 ≤ L) :
    (∀ j y (v : JointVariables E),
      ‖iteratedFDeriv ℝ j (fun w : JointVariables E ↦ (m (y, w.2.2.1) : ℂ)) v‖ ≤ H j * L ^ j) ∧
    (∀ j y (v : V),
      ‖iteratedFDeriv ℝ j (fun w : V ↦ (m (y, w.2.2.2.1) : ℂ)) v‖ ≤ H j * L ^ j) ∧
    (∀ j u ζ, ‖iteratedFDeriv ℝ j m (u, ζ)‖ ≤ H j * L ^ j) ∧
    (∀ j u ζ, ‖iteratedFDeriv ℝ j (fun t ↦ m (t, ζ)) u‖ ≤ H j * L ^ j) := by
  have hic : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ m) := Complex.ofRealCLM.contDiff.comp hm
  have hc j z : ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ m) z‖ ≤ H j := by
    change ‖iteratedFDeriv ℝ j (Complex.ofRealLI ∘ m) z‖ ≤ H j
    rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hm.contDiffAt (by simp)]
    exact hjet j z
  have hscale j : H j ≤ H j * L ^ j := le_mul_of_one_le_right (hH j) (one_le_pow₀ hL)
  have hinput j y (v : JointVariables E) :
      ‖iteratedFDeriv ℝ j (fun w : JointVariables E ↦ (m (y, w.2.2.1) : ℂ)) v‖ ≤ H j * L ^ j := by
    let π : JointVariables E →L[ℝ] E × E :=
      (0 : JointVariables E →L[ℝ] E).prod
        ((ContinuousLinearMap.fst ℝ _ _).comp
          ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
    have hπ : ‖π‖ ≤ 1 := π.opNorm_le_bound zero_le_one (by
      intro w
      change ‖((0 : E), w.2.2.1)‖ ≤ 1 * ‖w‖
      simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), one_mul] using
        ((norm_fst_le w.2.2).trans (norm_snd_le w.2)).trans (norm_snd_le w))
    have hb := norm_iteratedFDeriv_preAffine_le π (y, 0) isOpen_univ
      hic.contDiffOn (mem_univ _) j (x := v)
    have hb' := hb.trans ((mul_le_mul_of_nonneg_right (hc j _)
      (pow_nonneg (norm_nonneg _) _)).trans
      (mul_le_of_le_one_right (hH j) (pow_le_one₀ (norm_nonneg _) hπ)))
    simpa only [π, ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.mk_add_mk, zero_add, add_zero,
      Function.comp_apply, Complex.ofRealCLM_apply] using hb'.trans (hscale j)
  refine ⟨hinput, ?_, fun j u ζ ↦ (hjet j (u, ζ)).trans (hscale j), ?_⟩
  · intro j y v
    let g : JointVariables E → ℂ := fun w ↦ (m (y, w.2.2.1) : ℂ)
    have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp
      (hm.comp (contDiff_const.prodMk contDiff_snd.snd.fst))
    let π : V →L[ℝ] JointVariables E := ContinuousLinearMap.snd ℝ _ _
    have hb := norm_iteratedFDeriv_preAffine_le π 0 isOpen_univ hg.contDiffOn (mem_univ _) j (x := v)
    simp only [add_zero] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_right (hinput j y v.2)
      (pow_nonneg (norm_nonneg π) j)).trans
      (mul_le_of_le_one_right (mul_nonneg (hH j) (pow_nonneg (zero_le_one.trans hL) j))
        (pow_le_one₀ (norm_nonneg π) (ContinuousLinearMap.norm_snd_le ℝ _ _))))
  · intro j u ζ
    let π := ContinuousLinearMap.inl ℝ E E
    have hπ : ‖π‖ ≤ 1 := π.opNorm_le_bound zero_le_one (by
      intro v
      simp [π, Prod.norm_def])
    have hb := norm_iteratedFDeriv_preAffine_le π (0, ζ) isOpen_univ
      hm.contDiffOn (mem_univ _) j (x := u)
    have hb' := hb.trans ((mul_le_mul_of_nonneg_right (hjet j _)
      (pow_nonneg (norm_nonneg _) _)).trans
      (mul_le_of_le_one_right (hH j) (pow_le_one₀ (norm_nonneg _) hπ)))
    simpa only [π, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add]
      using hb'.trans (hscale j)

/-- Apply the published canonical joint derivative bound to each member of the
SAME selected even family. The literal `H` supplied before the coefficients
serves as `Qi`, `O`, and `Ophysical`, with zero offsets, for both the elapsed
and PDO primitive estimates. This avoids choosing a fresh derivative profile
from each history-dependent mask. Consumers: the primitive inputs of
`exists_selectedCompletePhysicalError_restriction_bound_of_supported_collars`
and `finiteChain_observation_rapidDecayAt.hleak`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem selected_even_uniform_localizer_grades
    {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables E)) (eI : Module.Basis κ ℝ V)
    (χ₂ : E → ℝ) (Ksource : Set E) (Vsource : Set (E × E)) (Γ : Set E)
    (output : E → ℝ) (N : ℕ) (aPhase bPhase : f.centers → ℝ)
    (n : f.centers → ℕ) (cRad : (p : f.centers) → Fin (n p) → ℝ)
    (hcRad : ∀ p k, 0 < cRad p k) (Urad : (p : f.centers) → Fin (n p) → Set (RootState (Euclidean d)))
    (buffer a b Rbase εcollar δT δI : ℝ) (H : ℕ → ℝ)
    (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (Φ : f.centers → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (Cphase : f.centers → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hEven : SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource Vsource Γ output
      N aPhase bPhase n cRad hcRad Urad buffer a b Rbase εcollar δT δI H Q Φ Cphase) :
    let masks := hEven.choose_spec.choose
    ∀ (k : Fin (N + 1)) (p : f.centers) (L : ℝ), 1 ≤ L →
    let m := canonicalProofLocalizer (coordinateSplit (f.chart p).index) (masks k)
    (∀ j y (v : JointVariables E),
      ‖iteratedFDeriv ℝ j (fun w : JointVariables E ↦ (m (y, w.2.2.1) : ℂ)) v‖ ≤ H j * L ^ j) ∧
    (∀ j y (v : V),
      ‖iteratedFDeriv ℝ j (fun w : V ↦ (m (y, w.2.2.2.1) : ℂ)) v‖ ≤ H j * L ^ j) ∧
    (∀ j u ζ, ‖iteratedFDeriv ℝ j m (u, ζ)‖ ≤ H j * L ^ j) ∧
    (∀ j u ζ, ‖iteratedFDeriv ℝ j (fun t ↦ m (t, ζ)) u‖ ≤ H j * L ^ j) := by
  intro masks k p L hL m
  obtain ⟨_, _, _, _, _, _, _, _, _, hcan, _, hjets, _⟩ := hEven.choose_spec.choose_spec
  exact selected_localizer_slices_le_joint_profile m (hcan k p).smooth H
    (fun j ↦ (norm_nonneg _).trans (hjets k p j 0)) (hjets k p) hL

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
