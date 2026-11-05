module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Amplitudes
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.CollaredBounds

/-!
# Recovering residual jets from the original collared symbol seminorm

The retained construction bounds the conic amplitude, rather than its local
buffered matrix. A high shell recovers the angular amplitude without dividing
by the angular mask. A positive spatial dilation then transfers its jets from
the original band, retaining both times, position, and the low-frequency collar.
Consumer: the normalized residual profile in `CompleteFactor.hprimitiveMasks`
and `exists_selected_elapsed_comparable_profiles.hbudget`.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector
open RegularSector.Characteristic RegularSector.Characteristic.AmplitudeBounds
open RegularSector.Characteristic.ConicAmplitude
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open RegularSector.FiniteMasks CompatibleResponse
open FourierIntegral.PrimitiveProfiles
open EvolutionIntegratedLocalization FiniteChain.Graph
variable {d q : ℕ}
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "P" => SymbolBudgets.TwoTimePoint d
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "V" => ℝ × JointVariables (Euclidean (d+1))

/-- On a sufficiently high shell the original collared residual recovers
its angular amplitude. This identity keeps the original low-frequency cutoff
at the requested frequency, and never divides by an angular mask. The fixed
dilation preserves both times and position (`app:ch_regular:eq:high-amplitude`). -/
theorem normalized_collared_orderOne_eventuallyEq_dilated_shell
    (ℓ : Euclidean d →L[ℝ] ℝ) (a : Euclidean d → ℝ) (F : T → Mat)
    {ρ t S : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (hS : 0 < S)
    {w : P} (hw : 2 < ‖S • (t • w.2)‖) :
    let W := curryCharacteristicMatrix (collared ℓ 1 a F)
    normalizedField ρ (SymbolBudgets.jointAmplitude W) =ᶠ[𝓝 w]
      (fun v ↦ (ρ⁻¹ * t) • ((conicMask (fun _ ↦ 1) (ρ • v.2) : ℂ) •
        twoTimeOrderField 1 S W (v.1, t • v.2))) := by
  intro W
  filter_upwards [((continuous_snd.const_smul t).const_smul S).norm.continuousAt.eventually
    (lt_mem_nhds hw)] with v hv
  change 2 < ‖S • (t • v.2)‖ at hv
  rw [twoTimeOrderField_curry_collared ℓ 1 a F hS.ne']
  simp only [normalizedField, SymbolBudgets.jointAmplitude, W, curryCharacteristicMatrix,
    collared]
  rw [conicMask_eq_radial hv.le,
    radialSourceCutoff_smul a (t • v.2) hS, radialSourceCutoff_smul a v.2 ht]
  rw [extend_smul ℓ 1 F (v.1.1, (v.1.2.1, (v.1.2.2, v.2))) hρ.ne',
    extend_smul ℓ 1 F (v.1.1, (v.1.2.1, (v.1.2.2, v.2))) ht.ne']
  simp only [pow_one, conicMask, radialSourceCutoff, mul_one, Complex.ofReal_mul]
  rw [show a (NormedSpace.normalize (ρ • v.2)) = a (NormedSpace.normalize v.2) from
    radialSourceCutoff_smul a v.2 hρ]
  rw [smul_comm (ρ⁻¹ * t), smul_comm (ρ⁻¹ * t), smul_smul (ρ⁻¹ * t) (t⁻¹),
    mul_assoc, mul_inv_cancel₀ ht.ne', mul_one, mul_smul]

private theorem residual_product_jet_le
    {f : V → ℂ} {g : V → Mat} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) {m : ℕ} {v : V}
    (hfa : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f v‖ ≤ A)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g v‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun w ↦ f w • g w) v‖ ≤ 2 ^ m * A * B := by
  apply (norm_iteratedFDeriv_smul_le hf hg v (by simp : (m : ℕ∞ω) ≤ ∞)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hfa i (by simpa using Finset.mem_range.mp hi)) (Nat.cast_nonneg _))
        (hgb (m-i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

/-- Fixed cost of the chart plateau, the radial collar, and a bounded
positive dilation, chosen before the residual and its source frequency.
Only the original retained amplitude seminorm is multiplied by this cost
(`app:ch_regular:eq:initial-coefficient-profile`, `app:ch_regular:eq:high-amplitude`). -/
def normalizedResidualTransferConstant (K : Set V) (χ : V → ℂ) (thi : ℝ) (m : ℕ) : ℝ :=
  thi * (2 ^ m) ^ 2 * cNorm K m χ *
    normalizedSeminorm (elapsedJointCoordinates '' K) m
      (fun w : P ↦ (conicMask (fun _ ↦ 1) w.2 : ℂ)) *
    (max 1 ‖elapsedJointCoordinates (d := d)‖) ^ m *
    (max 1 (max 1 thi * ‖elapsedJointCoordinates (d := d)‖)) ^ m

/-- The transfer cost is nonnegative, independently of the residual.
Consumer: the common profile `Qb` (`app:ch_regular:eq:high-amplitude`). -/
theorem normalizedResidualTransferConstant_nonneg (K : Set V) (χ : V → ℂ)
    {thi : ℝ} (hthi : 0 ≤ thi) (m : ℕ) :
    0 ≤ normalizedResidualTransferConstant K χ thi m := by
  unfold normalizedResidualTransferConstant
  have := cNorm_nonneg K m χ
  have := normalizedSeminorm_nonneg (elapsedJointCoordinates '' K) m
    (fun w : P ↦ (conicMask (fun _ ↦ 1) w.2 : ℂ))
  positivity

/-- Transfer the original order-minus-one seminorm to a joint elapsed jet
through the actual positive radial dilation. The local buffered amplitude
needs no quantitative bound. Its collared amplitude supplies the original
seminorm, and all collar and plateau jets are constructed from fixed smooth
functions. Both time variables and the physical position remain unchanged.
Consumer: `Qb` in `CompleteFactor.hprimitiveMasks`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_normalizedResidual_le_retained_seminorm
    (ℓ : Euclidean d →L[ℝ] ℝ) (a : Euclidean d → ℝ) (F : T → Mat)
    {K : Set V} (hK : IsCompact K)
    (hzero : ∀ v ∈ K, (elapsedJointCoordinates v).2 ≠ 0)
    (χ : V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    {J : Set P} (hJ : IsCompact J)
    (hW : ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude
      (curryCharacteristicMatrix (collared ℓ 1 a F))))
    {m : ℕ} (hfinite : BoundedTwoTimeOrderSeminorm 1 J m
      (curryCharacteristicMatrix (collared ℓ 1 a F)))
    {ρ t thi : ℝ} (hρ : 1 ≤ ρ) (ht : 0 < t) (htop : t ≤ thi)
    {v : V} (hv : v ∈ K)
    (hmap : ((elapsedJointCoordinates v).1, t • (elapsedJointCoordinates v).2) ∈ J) :
    ‖iteratedFDeriv ℝ m (fun w ↦ χ w •
      normalizedElapsedSymbol ρ (curryCharacteristicMatrix (collared ℓ 1 a F)) w) v‖ ≤
      ρ⁻¹ * normalizedResidualTransferConstant K χ thi m *
        twoTimeOrderSeminorm 1 J m (curryCharacteristicMatrix (collared ℓ 1 a F)) := by
  let e := elapsedJointCoordinates (d := d)
  let W := curryCharacteristicMatrix (collared ℓ 1 a F)
  let Tt : P →L[ℝ] P := (ContinuousLinearMap.fst ℝ _ _).prod
    (t • ContinuousLinearMap.snd ℝ _ _)
  let H := max 1 (max 1 thi * ‖e‖)
  let E := max 1 ‖e‖
  let B := twoTimeOrderSeminorm 1 J m W
  let A := cNorm K m χ
  let C := normalizedSeminorm (e '' K) m
    (fun w : P ↦ (conicMask (fun _ ↦ 1) w.2 : ℂ))
  have hA : 0 ≤ A := cNorm_nonneg _ _ _
  have hB : 0 ≤ B := twoTimeOrderSeminorm_nonneg _ _ _ _
  have hC : 0 ≤ C := normalizedSeminorm_nonneg _ _ _
  have hH : 1 ≤ H := le_max_left _ _
  have hE : 1 ≤ E := le_max_left _ _
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have htn : 0 < ‖t • (e v).2‖ := norm_pos_iff.mpr
    (smul_ne_zero ht.ne' (hzero v hv))
  let S := max 1 (3 / ‖t • (e v).2‖)
  have hS : 1 ≤ S := le_max_left _ _
  have hhigh : 2 < ‖S • (t • (e v).2)‖ := by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hS)]
    have hh := mul_le_mul_of_nonneg_right (le_max_right 1 (3 / ‖t • (e v).2‖)) htn.le
    rw [div_mul_cancel₀ _ htn.ne'] at hh
    linarith
  let g : V → ℂ := fun w ↦ conicMask (fun _ ↦ 1) (ρ • (e w).2)
  let f : P → Mat := twoTimeOrderField 1 S W
  let b : V → Mat := f ∘ (Tt.comp e)
  have hf : ContDiff ℝ ∞ f :=
    (hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul S))).const_smul (S^1)
  have hb : ContDiff ℝ ∞ b := hf.comp (Tt.comp e).contDiff
  have hg0 : ContDiff ℝ ∞ (fun w : P ↦ (conicMask (fun _ ↦ 1) (ρ • w.2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_conicMask contDiff_const).comp
      (contDiff_snd.const_smul ρ))
  have hg : ContDiff ℝ ∞ g := hg0.comp e.contDiff
  have hTt : ‖Tt‖ ≤ max 1 thi := by
    apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_left _ _))
    intro w
    change ‖(w.1, t • w.2)‖ ≤ _
    rw [Prod.norm_def, norm_smul, Real.norm_of_nonneg ht.le]
    apply max_le
    · exact (norm_fst_le w).trans (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
    · exact mul_le_mul (htop.trans (le_max_right _ _)) (norm_snd_le w)
        (norm_nonneg _) (zero_le_one.trans (le_max_left _ _))
  have hTe : ‖Tt.comp e‖ ≤ H := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hTt (norm_nonneg _)).trans (le_max_right _ _))
  have hbb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i b v‖ ≤ B * H ^ m := by
    intro i hi
    have hh := norm_iteratedFDeriv_preAffine_le (Tt.comp e) 0 isOpen_univ
      hf.contDiffOn (mem_univ _) i (x := v)
    simp only [add_zero] at hh
    apply hh.trans
    apply mul_le_mul
    · exact (norm_iteratedFDeriv_le_cNorm hJ (hf.of_le (by simp)) hmap hi).trans
        (cNorm_twoTimeOrderField_le hfinite hS)
    · exact (pow_le_pow_left₀ (norm_nonneg _) hTe i).trans (pow_le_pow_right₀ hH hi)
    · positivity
    · exact hB
  have hgg : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g v‖ ≤ C * E ^ m := by
    intro i hi
    have hh := norm_iteratedFDeriv_preAffine_le e 0 isOpen_univ
      hg0.contDiffOn (mem_univ _) i (x := v)
    simp only [add_zero] at hh
    apply hh.trans
    apply mul_le_mul
    · exact (norm_iteratedFDeriv_le_cNorm (hK.image e.continuous)
        (hg0.of_le (by simp)) (mem_image_of_mem e hv) hi).trans
        (cNorm_normalizedField_le
          (boundedNormalizedSeminorm_conicMask contDiff_const (hK.image e.continuous)
            (by rintro _ ⟨w, hw, rfl⟩; exact hzero w hw) m) hρ)
    · exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i).trans
        (pow_le_pow_right₀ hE hi)
    · positivity
    · exact hC
  have hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (fun w ↦ g w • b w) v‖ ≤
      2 ^ m * (C * E ^ m) * (B * H ^ m) := by
    intro i hi
    apply (residual_product_jet_le hg hb (by positivity) (by positivity)
      (fun j hj ↦ hgg j (hj.trans hi)) (fun j hj ↦ hbb j (hj.trans hi))).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi)
        (by positivity)) (by positivity)
  have hprod := residual_product_jet_le hχ (hg.smul hb) hA (by positivity)
    (fun i hi ↦ norm_iteratedFDeriv_le_cNorm hK (hχ.of_le (by simp)) hv hi) hgb
  have he := (normalized_collared_orderOne_eventuallyEq_dilated_shell ℓ a F hρpos ht
    (zero_lt_one.trans_le hS) hhigh).comp_tendsto e.continuous.continuousAt
  have he' : (fun w ↦ χ w • normalizedElapsedSymbol ρ W w) =ᶠ[𝓝 v]
      (fun w ↦ (ρ⁻¹*t) • (χ w • (g w • b w))) := by
    filter_upwards [he] with w hw
    change normalizedField ρ (SymbolBudgets.jointAmplitude W) (e w) =
      (ρ⁻¹*t) • (g w • b w) at hw
    have hn : normalizedElapsedSymbol ρ W w = normalizedField ρ
        (SymbolBudgets.jointAmplitude W) (e w) := by
      simp [normalizedElapsedSymbol, normalizedField, SymbolBudgets.jointAmplitude,
        e, elapsedJointCoordinates, spatialPart_smul]
    rw [hn, hw]
    exact smul_comm _ _ _
  have hc : iteratedFDeriv ℝ m (fun w ↦ (ρ⁻¹*t) • (χ w • (g w • b w))) v =
      (ρ⁻¹*t) • iteratedFDeriv ℝ m (fun w ↦ χ w • (g w • b w)) v :=
    iteratedFDeriv_const_smul_apply' ((hχ.smul (hg.smul hb)).contDiffAt.of_le (by simp))
  rw [(he'.iteratedFDeriv ℝ m).eq_of_nhds, hc,
    norm_smul, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hρpos.le) ht.le)]
  calc
    _ ≤ (ρ⁻¹*t) * (2 ^ m * A * (2 ^ m * (C * E ^ m) * (B * H ^ m))) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ (ρ⁻¹*thi) * (2 ^ m * A * (2 ^ m * (C * E ^ m) * (B * H ^ m))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htop (by positivity))
        (by positivity)
    _ = _ := by unfold normalizedResidualTransferConstant; dsimp [A, B, C, E, H, e]; ring

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
