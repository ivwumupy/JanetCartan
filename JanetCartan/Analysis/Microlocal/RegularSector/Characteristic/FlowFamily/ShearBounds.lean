module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.FieldJets

/-!
# Uniform bounds for the diagonal two-time shear

The inverse of the diagonal projection differential is explicit. Its norm is
controlled by the primitive scalar-root budget, independently of a local IFT
choice. This is the normalization for the common projection chart in
`app:ch_regular_base:lem:characteristic-kernel`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance twoTimeShearBoundsNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- The diagonal projection shear has a quantitative bound in the actual
product norm (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem norm_twoTimeProjectionLinear_le (v : E) :
    ‖twoTimeProjectionLinear v‖ ≤ 1 + 2 * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro w
  have ht := norm_fst_le w
  have hs := (norm_fst_le w.2).trans (norm_snd_le w)
  have hy := (norm_fst_le w.2.2).trans ((norm_snd_le w.2).trans (norm_snd_le w))
  have hp := (norm_snd_le w.2.2).trans ((norm_snd_le w.2).trans (norm_snd_le w))
  have hts : ‖w.1 - w.2.1‖ ≤ 2 * ‖w‖ := (norm_sub_le _ _).trans (by linarith)
  have hv : ‖w.2.2.1 + (w.1 - w.2.1) • v‖ ≤ (1 + 2 * ‖v‖) * ‖w‖ := by
    have hb := norm_add_le w.2.2.1 ((w.1 - w.2.1) • v)
    rw [norm_smul] at hb
    nlinarith [mul_le_mul_of_nonneg_right hts (norm_nonneg v)]
  change max ‖w.1‖ (max ‖w.2.1‖ (max ‖w.2.2.1 + (w.1 - w.2.1) • v‖ ‖w.2.2.2‖)) ≤ _
  have hw : ‖w‖ ≤ (1 + 2 * ‖v‖) * ‖w‖ := by
    nlinarith [norm_nonneg w, norm_nonneg v]
  exact max_le (ht.trans hw) (max_le (hs.trans hw) (max_le hv (hp.trans hw)))

/-- Both directions of the explicit shear have the same primitive bound
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem norm_twoTimeProjectionEquiv_and_symm_le (v : E) :
    ‖(twoTimeProjectionEquiv v).toContinuousLinearMap‖ ≤ 1 + 2 * ‖v‖ ∧
      ‖(twoTimeProjectionEquiv v).symm.toContinuousLinearMap‖ ≤ 1 + 2 * ‖v‖ := by
  constructor
  · exact norm_twoTimeProjectionLinear_le v
  · change ‖twoTimeProjectionLinear (-v)‖ ≤ _
    simpa only [norm_neg] using norm_twoTimeProjectionLinear_le (-v)

variable [CompleteSpace E]

/-- The actual momentum gradient is bounded by the scalar differential,
without a separate gradient hypothesis
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem norm_rootMomentumGradient_le (h : RootState E → ℝ) (z : RootState E) :
    ‖rootMomentumGradient h z‖ ≤ ‖fderiv ℝ h z‖ := by
  unfold rootMomentumGradient
  rw [LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro v
  simpa using (fderiv ℝ h z).le_opNorm (0, (0, v))

variable [FiniteDimensional ℝ E]

/-- The one scalar `C³` budget controls the diagonal shear and its inverse.
These constants are fixed before choosing the root, as required for common
target balls (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootProjectionShear_bounds_of_cNorm_three
    {D : Set (RootState E)} (hD : IsOpen D) {z : RootState E} {R M : ℝ}
    (hR : 0 ≤ R) (hRD : closedBall z R ⊆ D)
    {h : RootState E → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hlow : cNorm (closedBall z R) 3 h ≤ M) :
    ‖(twoTimeProjectionEquiv (-rootMomentumGradient h z)).toContinuousLinearMap‖ ≤ 1 + 2 * M ∧
      ‖(twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap‖ ≤
        1 + 2 * M := by
  have hd : ‖fderiv ℝ h z‖ ≤ cNorm (closedBall z R) 3 h := by
    simpa only [norm_iteratedFDeriv_one] using norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_closedBall z R)
      (fun w hw ↦ (hh.contDiffAt (hD.mem_nhds (hRD hw))).of_le (by simp))
      (mem_closedBall_self hR) (show 1 ≤ 3 by omega)
  have hp := (norm_rootMomentumGradient_le h z).trans (hd.trans hlow)
  obtain ⟨ha, hb⟩ := norm_twoTimeProjectionEquiv_and_symm_le (-rootMomentumGradient h z)
  simp only [norm_neg] at ha hb
  constructor <;> linarith

end JanetCartan.RegularSector.Characteristic
