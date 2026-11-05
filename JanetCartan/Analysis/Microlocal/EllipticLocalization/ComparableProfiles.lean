module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.CoefficientProfiles
public import JanetCartan.Analysis.Microlocal.EllipticLocalization.SourceProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.LocalCalculus

/-!
# Actual comparable elliptic symbol grades

The full pencil inverse and its physical action are evaluated on the original
coefficient profiles. The actual collared source multiplier remains inside
the differentiated amplitude. Both literal orientations retain degree minus
one, including the entire fixed low collar (`app:ch_regular:eq:high-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open ActualCarriers FiniteMasks FiniteMasks.ActualFamily EllipticComplement
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.PrimitiveProfiles
open FiniteChain.Graph KernelEstimates PhysicalShells PhysicalShells.Comparable
open KernelEstimates.NoncomparableGeometry FiniteChain.Retarded.KernelDecay
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- Mixed normalized grades on the exact comparable carrier for the actual
inverse and full residual. The output may be the original mask or the supplied
common output, inside the original doubled ball; the source mask and symbols
remain unchanged. Every analytic input is produced from the original
coefficient profiles, with degree minus one and zero offset, in both literal
orientations (`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_elliptic_masked_comparable_profile
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (threshold : ℝ) (ht : 1 ≤ threshold) {a b : ℝ} (ha : 0 < a)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    let Kb := tsupport χout ×ˢ tsupport (χs)
    let J := frequencyAnnulus (n := d+1) (a / (16*annulusFactor 1 1))
      (4 * max 1 (4*annulusFactor 1 1*b))
    let Kpdo := comparableJointCarrier 1 1 a b ((Prod.fst '' Kb) ×ˢ J) Kb (frequencyAnnulus a b)
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ (residual backward : Bool) (k : ℕ) v, v ∈ Kpdo →
        ‖iteratedFDeriv ℝ k (fun w : V ↦ orientedMaskedPDOAmplitude backward χout (χs)
          (if residual then ellipticResidualSymbol f hK threshold Q B
            else ellipticInverseSymbol f hK threshold Q) w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
              ρ ^ (-1 : ℝ) * C k * L ^ k := by
  intro Kb J Kpdo
  have hJ : IsCompact J := isCompact_frequencyAnnulus _ _
  have hzero : (0 : E) ∉ J := by
    intro hz
    have hf := two_le_annulusFactor 1 1
    have hp : 0 < a / (16*annulusFactor 1 1) := div_pos ha (by linarith)
    exact (not_le.mpr hp) (by simpa only [norm_zero] using hz.1)
  have hKb : IsCompact Kb := hoc.prod (f.inputMask_compact.comp_left Complex.ofReal_zero)
  have hKpdo : IsCompact Kpdo := isCompact_comparableJointCarrier 1 1 a b
    ((hKb.image continuous_fst).prod hJ) hKb (isCompact_frequencyAnnulus _ _)
  have hcarrier v (hv : v ∈ Kpdo) :
      v.1.1 ∈ interior {y | f.inputMask y = 1} ∧ v.1.1 ∈ closedBall x RQ ∧ v.2.1 ∈ J := by
    have hy := hos hv.1.1.1
    exact ⟨f.inputMask_plateau hy, f.physicalBall_coefficientDomain
      (closedBall_subset_closedBall (by linarith [f.physicalRadius_pos]) hy), hv.1.2.1⟩
  obtain ⟨D, hD, hcore⟩ := exists_coefficientElliptic_joint_profiles f hK hΩ hball J hJ hzero
    AQ AB hAQ hAB
  let π : V →L[ℝ] E × E :=
    ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.fst ℝ E _).comp (ContinuousLinearMap.snd ℝ _ _))
  let πβ : V →L[ℝ] ℝ × E := (0 : V →L[ℝ] ℝ).prod
    ((ContinuousLinearMap.fst ℝ E _).comp (ContinuousLinearMap.snd ℝ _ _))
  have hπ : ‖π‖ ≤ 1 := by
    apply π.opNorm_le_bound zero_le_one
    intro v
    change max ‖v.1.1‖ ‖v.2.1‖ ≤ 1 * ‖v‖
    rw [one_mul]
    exact max_le ((norm_fst_le v.1).trans (norm_fst_le v))
      ((norm_fst_le v.2).trans (norm_snd_le v))
  have hπβ : ‖πβ‖ ≤ 1 := by
    apply πβ.opNorm_le_bound zero_le_one
    intro v
    change max ‖(0 : ℝ)‖ ‖v.2.1‖ ≤ 1 * ‖v‖
    simp only [norm_zero, max_eq_right (norm_nonneg _), one_mul]
    exact (norm_fst_le v.2).trans (norm_snd_le v)
  let m : V → ℂ := fun v ↦ χout v.1.1 * (f.inputMask v.1.2 : ℂ)
  have hm : ContDiff ℝ ∞ m := (ho.comp contDiff_fst.fst).mul
    ((Complex.ofRealCLM.contDiff.comp f.inputMask_smooth).comp contDiff_fst.snd)
  let β : E → ℂ := fun ξ ↦ (ellipticSourceMask f hK threshold ξ : ℂ)
  have hβ : ContDiff ℝ ∞ β := Complex.ofRealCLM.contDiff.comp
    (ellipticSourceMask_properties f hK threshold).1
  let Jβ := πβ '' Kpdo
  have hJβ : IsCompact Jβ := hKpdo.image πβ.continuous
  have hβnorm k : BoundedNormalizedSeminorm Jβ k (fun w : ℝ × E ↦ β w.2) :=
    boundedNormalizedSeminorm_dilatedConicMask (ellipticAngularMask_spec f hK).1
      (show 1 ≤ 2*threshold by linarith) hJβ (by
        rintro _ ⟨v, hv, rfl⟩
        exact fun he ↦ hzero (he ▸ (hcarrier v hv).2.2)) k
  let T k := cNorm Kpdo k m
  let G k := normalizedSeminorm Jβ k (fun w : ℝ × E ↦ β w.2)
  have hT k : 0 ≤ T k := cNorm_nonneg _ _ _
  have hG k : 0 ≤ G k := normalizedSeminorm_nonneg _ _ _
  let C := derivativeConvolution T (derivativeConvolution G D)
  have hC k : 0 ≤ C k := derivativeConvolution_nonneg hT (derivativeConvolution_nonneg hG hD) k
  refine ⟨C, hC, ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hmap hQp hBp residual backward k v hv
  have hρp : 0 < ρ := zero_lt_one.trans_le hρ
  have htp : 0 < threshold := zero_lt_one.trans_le ht
  have hvphys := hcarrier v hv
  let s := if residual then ellipticResidualSymbol f hK threshold Q B
    else ellipticInverseSymbol f hK threshold Q
  have hforward : ‖iteratedFDeriv ℝ k (fun w : V ↦ m w • s w.1.1 (ρ • w.2.1)) v‖ ≤
      ρ ^ (-1 : ℝ) * C k * L ^ k := by
    by_cases hsupport : v.2.1 ∈ tsupport (fun ξ ↦ β (ρ • ξ))
    · have hgap := determinant_gap_on_normalized_elliptic_support f hK htp hρp
        (hmap (hball hvphys.2.1)) hsupport
      have hdet : determinant (Q v.1.1) v.2.1 ≠ 0 := abs_pos.mp
        ((mul_nonneg (half_pos f.determinantGap_pos).le (pow_nonneg (norm_nonneg _) _)).trans_lt hgap)
      have hGs := contDiffAt_coefficientEllipticInverse (p := (Q v.1.1, v.2.1)) hdet
      have hq := hQ.contDiffAt (hΩ.mem_nhds (hball hvphys.2.1))
      have hb := hB.contDiffAt (hΩ.mem_nhds (hball hvphys.2.1))
      let F : E × E → CMat := fun w ↦ if residual then
        coefficientEllipticPhysicalAction ((Q w.1, (fderiv ℝ Q w.1, B w.1)), w.2)
        else coefficientEllipticInverse (Q w.1, w.2)
      have hF : ContDiffAt ℝ ∞ F (π v) := by
        cases residual
        · exact hGs.comp (π v) ((hq.comp (π v) contDiffAt_fst).prodMk contDiffAt_snd)
        · exact (contDiffAt_coefficientEllipticPhysicalAction hdet).comp (π v)
            (((hq.comp (π v) contDiffAt_fst).prodMk
              (((hq.fderiv_right (m := ∞) (by simp)).comp (π v) contDiffAt_fst).prodMk
                (hb.comp (π v) contDiffAt_fst))).prodMk contDiffAt_snd)
      have hFp := hF.comp v π.contDiff.contDiffAt
      have hFjet j : ‖iteratedFDeriv ℝ j (F ∘ π) v‖ ≤ D j * L ^ j := by
        apply (algebraic_norm_iteratedFDeriv_comp_linear_at_le π hF j).trans
        apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg π) hπ)).trans
        exact hcore Rstar hR L hL Q B hQ hB hmap hQp hBp threshold ρ htp hρp
          (π v) hvphys.2.1 hvphys.2.2 hsupport residual j
      have hbs : ContDiff ℝ ∞ (fun w : V ↦ β (ρ • w.2.1)) :=
        hβ.comp (contDiff_snd.fst.const_smul ρ)
      have hbj j : ‖iteratedFDeriv ℝ j (fun w : V ↦ β (ρ • w.2.1)) v‖ ≤ G j * L ^ j := by
        let g : ℝ × E → ℂ := normalizedField ρ (fun w : ℝ × E ↦ β w.2)
        have hg : ContDiff ℝ ∞ g := hβ.comp (contDiff_snd.const_smul ρ)
        change ‖iteratedFDeriv ℝ j (g ∘ πβ) v‖ ≤ _
        apply (algebraic_norm_iteratedFDeriv_comp_linear_at_le πβ hg.contDiffAt j).trans
        apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg πβ) hπβ)).trans
        exact ((norm_iteratedFDeriv_le_cNorm hJβ (hg.of_le (by simp))
          (mem_image_of_mem πβ hv) le_rfl).trans (cNorm_normalizedField_le (hβnorm j) hρ)).trans
            (le_mul_of_one_le_right (hG j) (one_le_pow₀ hL))
      have hmj j : ‖iteratedFDeriv ℝ j m v‖ ≤ T j * L ^ j :=
        (norm_iteratedFDeriv_le_cNorm hKpdo (hm.of_le (by simp)) hv le_rfl).trans
          (le_mul_of_one_le_right (hT j) (one_le_pow₀ hL))
      have hprod j := algebraic_norm_iteratedFDeriv_smul_grades hbs.contDiffAt hFp hG
        (zero_le_one.trans hL) hbj (S := 1) (by simpa only [one_mul] using hFjet) j
      have hfull := algebraic_norm_iteratedFDeriv_smul_grades hm.contDiffAt
        (hbs.contDiffAt.smul hFp) hT (zero_le_one.trans hL) hmj hprod k
      have he := (ellipticSymbols_normalized_eventuallyEq f hK threshold hρp Q B (π v)
        hvphys.1 hq hGs residual).comp_tendsto π.continuous.continuousAt
      have hefull : (fun w : V ↦ m w • s w.1.1 (ρ • w.2.1)) =ᶠ[𝓝 v]
          fun w : V ↦ ρ⁻¹ • (m w • (β (ρ • w.2.1) • F (π w))) := by
        filter_upwards [he] with w hw
        change s w.1.1 (ρ • w.2.1) = ρ⁻¹ • (β (ρ • w.2.1) • F (π w)) at hw
        rw [hw, smul_comm]
      have hsfull : ContDiffAt ℝ ∞ (fun w : V ↦ m w • (β (ρ • w.2.1) • F (π w))) v :=
        hm.contDiffAt.smul (hbs.contDiffAt.smul hFp)
      rw [(hefull.iteratedFDeriv ℝ k).eq_of_nhds]
      change ‖iteratedFDeriv ℝ k (ρ⁻¹ • (fun w : V ↦ m w • (β (ρ • w.2.1) • F (π w)))) v‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply (hsfull.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)),
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρp), Real.rpow_neg_one]
      have hfbound : ‖iteratedFDeriv ℝ k (fun w : V ↦ m w • (β (ρ • w.2.1) • F (π w))) v‖ ≤
          C k * L ^ k := by simpa only [one_mul, Pi.smul_apply', Function.comp_def] using hfull
      exact (mul_le_mul_of_nonneg_left hfbound (inv_nonneg.mpr hρp.le)).trans_eq (by ring)
    · have he : (fun w : V ↦ m w • s w.1.1 (ρ • w.2.1)) =ᶠ[𝓝 v] fun _ ↦ 0 := by
        have hz := (notMem_tsupport_iff_eventuallyEq.mp hsupport).comp_tendsto
          (continuous_snd.fst.continuousAt : ContinuousAt (fun w : V ↦ w.2.1) v)
        filter_upwards [hz] with w hw
        have hreal : ellipticSourceMask f hK threshold (ρ • w.2.1) = 0 :=
          Complex.ofReal_eq_zero.mp hw
        have hs : s ∈ ({ellipticInverseSymbol f hK threshold Q,
            ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
            Set (E → E → CMat)) := by cases residual <;> simp [s]
        rw [ellipticSymbols_zero_of_sourceMask_zero f hK threshold Q B hreal s hs, smul_zero]
      rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
      change ‖iteratedFDeriv ℝ k (0 : V → CMat) v‖ ≤ _
      rw [show iteratedFDeriv ℝ k (0 : V → CMat) v = 0 from congrFun iteratedFDeriv_zero v, norm_zero]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hρp.le _) (hC k))
        (pow_nonneg (zero_le_one.trans hL) _)
  cases backward
  · exact hforward
  · simpa only [orientedMaskedPDOAmplitude, ↓reduceIte,
      norm_iteratedFDeriv_transport_conjTranspose] using hforward

end JanetCartan.RegularSector.EllipticLocalization
