module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.CollaredBounds

/-!
# Recovering the retained angular amplitude at high radius

For `app:ch_regular:eq:high-amplitude`, recover the angular factor together
with the homogeneous matrix from the original collared symbol. No angular
cutoff is divided out. The physical residual profile consumes this identity
to transfer the original retained seminorms to physical joint derivatives.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization.PhysicalAmplitude
open RegularSector RegularSector.Characteristic RegularSector.FiniteMasks
open ConicAmplitude AmplitudeBounds EvolutionIntegral EvolutionIntegral.SymbolBudgets
open FourierIntegral.PrimitiveProfiles FourierIntegral.LowBounds.FrequencyCutoff
open CompatibleResponse
variable {d q : ℕ}
local notation "J" => SymbolBudgets.TwoTimePoint d
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- Radial dilation of the covector alone, preserving both times and position
in the physical residual (`app:ch_regular_base:eq:energy-complete-residual`). -/
def covectorDilation (t : ℝ) : J →L[ℝ] J :=
  (ContinuousLinearMap.fst ℝ _ _).prod (t • ContinuousLinearMap.snd ℝ _ _)

/-- A fixed bound for the linear substitution, including all covector jets
(`app:ch_regular:eq:high-amplitude`). -/
theorem norm_covectorDilation_le {t H : ℝ} (ht : 0 ≤ t) (hH : 1 ≤ H) (htH : t ≤ H) :
    ‖covectorDilation (d := d) t‖ ≤ H := by
  rw [covectorDilation, ContinuousLinearMap.opNorm_prod, Prod.norm_def, max_le_iff]
  refine ⟨(ContinuousLinearMap.norm_fst_le ℝ _ _).trans hH, ?_⟩
  change ‖t • ContinuousLinearMap.snd ℝ (ℝ × ℝ × Euclidean d) (Euclidean d)‖ ≤ H
  apply (norm_smul_le t (ContinuousLinearMap.snd ℝ (ℝ × ℝ × Euclidean d) (Euclidean d))).trans
  rw [Real.norm_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ _ _) ht).trans
    (by simpa only [mul_one] using htH)

/-- At high radius the original normalized symbol recovers the angular
amplitude, including angular shoulders. The subsequent multiplication by
the radial collar is exact (`app:ch_regular:eq:high-amplitude`). -/
theorem collared_eq_radial_mul_recovered
    (ℓ : Euclidean d →L[ℝ] ℝ) (angular : Euclidean d → ℝ) (F : T → Mat)
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (w : J)
    (hh : 2 ≤ ‖R • (t • w.2)‖) :
    jointAmplitude (curryCharacteristicMatrix (collared ℓ 1 angular F)) w =
      (1 - physicalCutoff 0 w.2 : ℂ) •
        (t • twoTimeOrderField 1 R (curryCharacteristicMatrix (collared ℓ 1 angular F))
          (covectorDilation t w)) := by
  rw [twoTimeOrderField_curry_collared ℓ 1 angular F hR.ne']
  change (conicMask angular w.2 : ℂ) • extend ℓ 1 F _ =
    (1 - physicalCutoff 0 w.2 : ℂ) •
      (t • ((conicMask angular (R • (t • w.2)) : ℂ) •
        extend ℓ 1 F (w.1.1, (w.1.2.1, (w.1.2.2, t • w.2)))))
  rw [conicMask_eq_radial hh, radialSourceCutoff_smul angular _ hR,
    radialSourceCutoff_smul angular _ ht,
    extend_smul ℓ 1 F (w.1.1, (w.1.2.1, (w.1.2.2, w.2))) ht.ne', pow_one,
    smul_comm t, smul_inv_smul₀ ht.ne']
  simp only [conicMask, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    mul_smul]

/-- A single sufficiently large shell recovers the germ at a physical point.
Differentiating this equality transfers joint derivatives without assuming a
new seminorm or a local amplitude budget (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_collared_recovery_germ
    (ℓ : Euclidean d →L[ℝ] ℝ) (angular : Euclidean d → ℝ) (F : T → Mat)
    {t : ℝ} (ht : 0 < t) {w : J} (hw : w.2 ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧
      jointAmplitude (curryCharacteristicMatrix (collared ℓ 1 angular F)) =ᶠ[𝓝 w]
        (fun v ↦ (1 - physicalCutoff 0 v.2 : ℂ) •
          (t • twoTimeOrderField 1 R (curryCharacteristicMatrix (collared ℓ 1 angular F))
            (covectorDilation t v))) := by
  let R := max 1 (3 / ‖t • w.2‖)
  have hn : 0 < ‖t • w.2‖ := norm_pos_iff.mpr (smul_ne_zero ht.ne' hw)
  have hR : 1 ≤ R := le_max_left _ _
  have hh : 2 < ‖R • (t • w.2)‖ := by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hR)]
    have h := mul_le_mul_of_nonneg_right (le_max_right 1 (3 / ‖t • w.2‖)) hn.le
    rw [div_mul_cancel₀ _ hn.ne'] at h
    linarith
  refine ⟨R, hR, ?_⟩
  filter_upwards [((continuous_snd.const_smul t).const_smul R).norm.continuousAt.eventually
    (lt_mem_nhds hh)] with v hv
  exact collared_eq_radial_mul_recovered ℓ angular F (zero_lt_one.trans_le hR) ht v hv.le

end JanetCartan.ArbitraryAccuracy.SelectedLocalization.PhysicalAmplitude
