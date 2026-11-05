module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhysicalResidual
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation.Coordinates
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Basic

/-!
# Fixed mask profiles for the physical residual

The output mask and the radial collar have globally bounded joint jets.
These fixed constants precede the coefficients and scales in the transfer
of the retained residual seminorm (`app:ch_regular:eq:high-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization.PhysicalAmplitude
open RegularSector RegularSector.Characteristic
open EvolutionIntegral EvolutionIntegral.SymbolBudgets EvolutionIntegral.KernelIdentification
open FourierIntegral.LowBounds.FrequencyCutoff
variable {d : ℕ}
local notation "J" => SymbolBudgets.TwoTimePoint d
local notation "E" => Euclidean (d+1)

/-- The original output mask times the radial collar; the angular factor
remains in the recovered symbol (`app:ch_regular:eq:high-amplitude`). -/
def residualMask (χ : E → ℂ) (w : J) : ℂ :=
  χ (timeSpacePoint w.1.1 w.1.2.2) * (1 - physicalCutoff 0 w.2)

/-- Smoothness of the exact fixed mask used to recover the physical residual
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem contDiff_residualMask {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (residualMask χ) :=
  (hχ.comp (contDiff_timeSpacePoint.comp (contDiff_fst.fst.prodMk contDiff_fst.snd.snd))).mul
    (contDiff_const.sub ((complexPhysicalCutoff_contDiff 0).comp contDiff_snd))

private theorem compact_jet_profile {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {χ : X → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ H : ℕ → ℝ, (∀ j, 0 ≤ H j) ∧ ∀ j x, ‖iteratedFDeriv ℝ j χ x‖ ≤ H j := by
  have hb j := (hc.iteratedFDeriv (𝕜 := ℝ) j).exists_bound_of_continuous
    ((hχ.iteratedFDeriv_right (m := ∞) (i := j) (by simp)).continuous)
  choose H hH using hb
  exact ⟨fun j ↦ max 0 (H j), fun j ↦ le_max_left _ _,
    fun j x ↦ (hH j x).trans (le_max_right _ _)⟩

/-- Every joint derivative of the literal mask has a fixed bound, derived
from compact smooth cutoffs. Consumer: the physical residual Leibniz bound;
no scale-dependent offset is introduced (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_residualMask_profile {χ : E → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ H : ℕ → ℝ, (∀ j, 0 ≤ H j) ∧
      ∀ j w, ‖iteratedFDeriv ℝ j (residualMask χ) w‖ ≤ H j := by
  obtain ⟨A, hA, hAb⟩ := compact_jet_profile hχ hc
  obtain ⟨B, hB, hBb⟩ := compact_jet_profile
    (complexPhysicalCutoff_contDiff (n := d) 0) (complexPhysicalCutoff_hasCompactSupport 0)
  let P : J →L[ℝ] E := timeSpacePointCLM.comp
    (((ContinuousLinearMap.fst ℝ ℝ (ℝ × Euclidean d)).comp
      (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.snd ℝ ℝ (Euclidean d)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × Euclidean d)).comp
          (ContinuousLinearMap.fst ℝ _ _))))
  let S : J →L[ℝ] Euclidean d := ContinuousLinearMap.snd ℝ _ _
  let f := χ ∘ P
  let g := fun w : J ↦ (1 : ℂ) - complexPhysicalCutoff 0 (S w)
  have hf : ContDiff ℝ ∞ f := hχ.comp P.contDiff
  have hg : ContDiff ℝ ∞ g := contDiff_const.sub ((complexPhysicalCutoff_contDiff 0).comp S.contDiff)
  have hfB j w : ‖iteratedFDeriv ℝ j f w‖ ≤ A j * ‖P‖ ^ j := by
    have h := norm_iteratedFDeriv_preAffine_le (x := w) P 0 isOpen_univ hχ.contDiffOn (mem_univ _) j
    simp only [add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hAb j (P w)) (by positivity))
  have hgB j w : ‖iteratedFDeriv ℝ j g w‖ ≤ 1 + B j * ‖S‖ ^ j := by
    have hb := norm_iteratedFDeriv_preAffine_le (x := w) S 0 isOpen_univ
      (complexPhysicalCutoff_contDiff 0).contDiffOn (mem_univ _) j
    simp only [add_zero] at hb
    have hh := hb.trans (mul_le_mul_of_nonneg_right (hBb j (S w)) (by positivity))
    rw [show g = (fun _ : J ↦ (1 : ℂ)) - (complexPhysicalCutoff 0 ∘ S) by rfl,
      iteratedFDeriv_sub_apply (contDiffAt_const : ContDiffAt ℝ j (fun _ : J ↦ (1 : ℂ)) w)
        (((complexPhysicalCutoff_contDiff 0).comp S.contDiff).contDiffAt.of_le (by simp))]
    apply (norm_sub_le _ _).trans
    apply add_le_add _ hh
    cases j with
    | zero => simp
    | succ j => simp [iteratedFDeriv_succ_const]
  refine ⟨fun j ↦ ∑ i ∈ Finset.range (j+1),
    (j.choose i : ℝ) * (A i * ‖P‖ ^ i) * (1 + B (j-i) * ‖S‖ ^ (j-i)),
    fun j ↦ Finset.sum_nonneg (fun i _ ↦ mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) (by positivity)))
      (by have := hB (j-i); positivity)), ?_⟩
  intro j w
  change ‖iteratedFDeriv ℝ j (fun w ↦ f w * g w) w‖ ≤ _
  apply (norm_iteratedFDeriv_mul_le hf hg w (n := j) (by simp)).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hfB i w) (by positivity)) (hgB (j-i) w)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) (by positivity)))

end JanetCartan.ArbitraryAccuracy.SelectedLocalization.PhysicalAmplitude
