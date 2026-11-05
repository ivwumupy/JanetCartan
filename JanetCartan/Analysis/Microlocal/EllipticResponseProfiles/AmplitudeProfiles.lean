module

public import JanetCartan.Analysis.Microlocal.EllipticResponseProfiles.CoefficientProfiles
public import JanetCartan.Analysis.Microlocal.EllipticLocalization.ComparableProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets

/-!
# Reserve profiles of the actual normalized elliptic amplitudes

The fixed physical and collared angular/radial masks retain bounds independent
of the history scale. The full inverse and physical residual keep their exact
normalized identities throughout the radial transition. Consumers:
`NearCarrier.ParameterEnvelope` and `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticResponseProfiles
open ActualCarriers FiniteMasks FiniteMasks.ActualFamily EllipticComplement EllipticLocalization
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.PrimitiveProfiles ResponseTransfer
open FiniteChain.Retarded.KernelDecay
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat

/-- Fixed masks preserve the first-jet reserve in the normalized elliptic
product (`app:ch_response:eq:direct-envelope-profile`). -/
private theorem norm_jet_fixed_smul_reserve_le
    {a : V → ℂ} {g : V → CMat} {v : V}
    (ha : ContDiffAt ℝ ∞ a v) (hg : ContDiffAt ℝ ∞ g v)
    {C D : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    {L : ℝ} (hL : 1 ≤ L) (R : ℕ)
    (haj : ∀ j, ‖iteratedFDeriv ℝ j a v‖ ≤ C j)
    (hgj : ∀ j, ‖iteratedFDeriv ℝ j g v‖ ≤ D j * L ^ (j-R)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w ↦ a w • g w) v‖ ≤
      derivativeConvolution C D k * L ^ (k-R) := by
  obtain ⟨U, hU, hau⟩ := ha.contDiffOn (m := (k : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨W, hW, hgu⟩ := hg.contDiffOn (m := (k : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨O, hOsub, hO, hv⟩ := _root_.mem_nhds_iff.mp (inter_mem hU hW)
  have h := norm_iteratedFDerivWithin_smul_le
    (hau.mono (hOsub.trans inter_subset_left)) (hgu.mono (hOsub.trans inter_subset_right))
    hO.uniqueDiffOn hv (n := k) le_rfl
  simp only [iteratedFDerivWithin_of_isOpen _ hO hv] at h
  apply h.trans
  simp only [derivativeConvolution, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ (k.choose j : ℝ) * C j * (D (k-j) * L ^ (k-j-R)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (haj j) (Nat.cast_nonneg _)) (hgj _)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC _))
    _ = ((k.choose j : ℝ) * C j * D (k-j)) * L ^ (k-j-R) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : k-j-R ≤ k-R))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC _)) (hD _))

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- Both literal orientations of the actual normalized full elliptic
inverse and residual have reserve `Rstar - 1`, uniformly on any fixed compact
full-frequency set away from zero and at every physical position. All masks,
the full `B`, and the final doubled radial collar remain literal. Constants
precede the fields, history and radial scales
(`app:ch_response:eq:direct-envelope-profile`, `app:ch_regular:eq:high-amplitude`). -/
theorem exists_normalized_elliptic_amplitude_reserve_profiles
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (threshold : ℝ) (ht : 1 ≤ threshold)
    (J : Set E) (hJ : IsCompact J) (hzero : (0 : E) ∉ J)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ (residual backward : Bool) (k : ℕ) (v : V), v.2.2 ∈ J →
        ‖iteratedFDeriv ℝ k (normalizedFullAmplitude
          (orientedMaskedPDOAmplitude backward χout (χs)
            (if residual then ellipticResidualSymbol f hK threshold Q B
              else ellipticInverseSymbol f hK threshold Q)) ρ) v‖ ≤
                ρ ^ (-1 : ℝ) * C k * L ^ (k-(Rstar-1)) := by
  let Kfull := tsupport χout ×ˢ tsupport (χs) ×ˢ J
  have hKfull : IsCompact Kfull := hoc.prod
    ((f.inputMask_compact.comp_left Complex.ofReal_zero).prod hJ)
  have hcarrier v (hv : v ∈ Kfull) :
      v.1 ∈ interior {y | f.inputMask y = 1} ∧ v.1 ∈ closedBall x RQ ∧ v.2.2 ∈ J := by
    have hy := hos hv.1
    exact ⟨f.inputMask_plateau hy, f.physicalBall_coefficientDomain
      (closedBall_subset_closedBall (by linarith [f.physicalRadius_pos]) hy), hv.2.2⟩
  obtain ⟨D, hD, hcore⟩ := exists_coefficientElliptic_joint_reserve_profiles f hK hΩ hball J hJ hzero
    AQ AB hAQ hAB
  let π : V →L[ℝ] E × E := (ContinuousLinearMap.fst ℝ E (E × E)).prod
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E)))
  let πβ : V →L[ℝ] ℝ × E := (0 : V →L[ℝ] ℝ).prod
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E)))
  have hπ : ‖π‖ ≤ 1 := by
    apply π.opNorm_le_bound zero_le_one
    intro v
    change max ‖v.1‖ ‖v.2.2‖ ≤ 1 * ‖v‖
    rw [one_mul]
    exact max_le (norm_fst_le v) ((norm_snd_le v.2).trans (norm_snd_le v))
  have hπβ : ‖πβ‖ ≤ 1 := by
    apply πβ.opNorm_le_bound zero_le_one
    intro v
    change max ‖(0 : ℝ)‖ ‖v.2.2‖ ≤ 1 * ‖v‖
    simp only [norm_zero, max_eq_right (norm_nonneg _), one_mul]
    exact (norm_snd_le v.2).trans (norm_snd_le v)
  let m : V → ℂ := fun v ↦ χout v.1 * (f.inputMask v.2.1 : ℂ)
  have hm : ContDiff ℝ ∞ m := (ho.comp contDiff_fst).mul
    ((Complex.ofRealCLM.contDiff.comp f.inputMask_smooth).comp contDiff_snd.fst)
  let β : E → ℂ := fun ξ ↦ (ellipticSourceMask f hK threshold ξ : ℂ)
  have hβ : ContDiff ℝ ∞ β := Complex.ofRealCLM.contDiff.comp
    (ellipticSourceMask_properties f hK threshold).1
  let Jβ := πβ '' Kfull
  have hJβ : IsCompact Jβ := hKfull.image πβ.continuous
  have hβnorm k : BoundedNormalizedSeminorm Jβ k (fun w : ℝ × E ↦ β w.2) :=
    boundedNormalizedSeminorm_dilatedConicMask (ellipticAngularMask_spec f hK).1
      (show 1 ≤ 2*threshold by linarith) hJβ (by
        rintro _ ⟨v, hv, rfl⟩
        exact fun he ↦ hzero (he ▸ (hcarrier v hv).2.2)) k
  let T k := cNorm Kfull k m
  let G k := normalizedSeminorm Jβ k (fun w : ℝ × E ↦ β w.2)
  have hT k : 0 ≤ T k := cNorm_nonneg _ _ _
  have hG k : 0 ≤ G k := normalizedSeminorm_nonneg _ _ _
  let C := derivativeConvolution T (derivativeConvolution G D)
  have hC k : 0 ≤ C k := derivativeConvolution_nonneg hT (derivativeConvolution_nonneg hG hD) k
  refine ⟨C, hC, ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hmap hQp hBp residual backward k v hfreq
  have hρp : 0 < ρ := zero_lt_one.trans_le hρ
  have htp : 0 < threshold := zero_lt_one.trans_le ht
  let s := if residual then ellipticResidualSymbol f hK threshold Q B
    else ellipticInverseSymbol f hK threshold Q
  have hnonneg : 0 ≤ ρ ^ (-1 : ℝ) * C k * L ^ (k-(Rstar-1)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hρp.le _) (hC k))
      (pow_nonneg (zero_le_one.trans hL) _)
  by_cases hv : v ∈ Kfull
  · have hvphys := hcarrier v hv
    have hforward : ‖iteratedFDeriv ℝ k (fun w : V ↦ m w • s w.1 (ρ • w.2.2)) v‖ ≤
        ρ ^ (-1 : ℝ) * C k * L ^ (k-(Rstar-1)) := by
      by_cases hsupport : v.2.2 ∈ tsupport (fun ξ ↦ β (ρ • ξ))
      · have hgap := determinant_gap_on_normalized_elliptic_support f hK htp hρp
          (hmap (hball hvphys.2.1)) hsupport
        have hdet : determinant (Q v.1) v.2.2 ≠ 0 := abs_pos.mp
          ((mul_nonneg (half_pos f.determinantGap_pos).le (pow_nonneg (norm_nonneg _) _)).trans_lt hgap)
        have hGs := contDiffAt_coefficientEllipticInverse (p := (Q v.1, v.2.2)) hdet
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
        have hFjet j : ‖iteratedFDeriv ℝ j (F ∘ π) v‖ ≤ D j * L ^ (j-(Rstar-1)) := by
          apply (algebraic_norm_iteratedFDeriv_comp_linear_at_le π hF j).trans
          apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg π) hπ)).trans
          exact hcore Rstar hR L hL Q B hQ hB hmap hQp hBp threshold ρ htp hρp
            (π v) hvphys.2.1 hvphys.2.2 hsupport residual j
        have hbs : ContDiff ℝ ∞ (fun w : V ↦ β (ρ • w.2.2)) :=
          hβ.comp (contDiff_snd.snd.const_smul ρ)
        have hbj j : ‖iteratedFDeriv ℝ j (fun w : V ↦ β (ρ • w.2.2)) v‖ ≤ G j := by
          let g : ℝ × E → ℂ := normalizedField ρ (fun w : ℝ × E ↦ β w.2)
          have hg : ContDiff ℝ ∞ g := hβ.comp (contDiff_snd.const_smul ρ)
          change ‖iteratedFDeriv ℝ j (g ∘ πβ) v‖ ≤ _
          apply (algebraic_norm_iteratedFDeriv_comp_linear_at_le πβ hg.contDiffAt j).trans
          apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg πβ) hπβ)).trans
          exact (norm_iteratedFDeriv_le_cNorm hJβ (hg.of_le (by simp))
            (mem_image_of_mem πβ hv) le_rfl).trans (cNorm_normalizedField_le (hβnorm j) hρ)
        have hmj j : ‖iteratedFDeriv ℝ j m v‖ ≤ T j :=
          norm_iteratedFDeriv_le_cNorm hKfull (hm.of_le (by simp)) hv le_rfl
        have hprod j := norm_jet_fixed_smul_reserve_le hbs.contDiffAt hFp hG hD hL
          (Rstar-1) hbj hFjet j
        have hfull := norm_jet_fixed_smul_reserve_le hm.contDiffAt
          (hbs.contDiffAt.smul hFp) hT (derivativeConvolution_nonneg hG hD) hL
          (Rstar-1) hmj hprod k
        have he := (ellipticSymbols_normalized_eventuallyEq f hK threshold hρp Q B (π v)
          hvphys.1 hq hGs residual).comp_tendsto π.continuous.continuousAt
        have hefull : (fun w : V ↦ m w • s w.1 (ρ • w.2.2)) =ᶠ[𝓝 v]
            fun w : V ↦ ρ⁻¹ • (m w • (β (ρ • w.2.2) • F (π w))) := by
          filter_upwards [he] with w hw
          change s w.1 (ρ • w.2.2) = ρ⁻¹ • (β (ρ • w.2.2) • F (π w)) at hw
          rw [hw, smul_comm]
        have hsfull : ContDiffAt ℝ ∞ (fun w : V ↦ m w • (β (ρ • w.2.2) • F (π w))) v :=
          hm.contDiffAt.smul (hbs.contDiffAt.smul hFp)
        rw [(hefull.iteratedFDeriv ℝ k).eq_of_nhds]
        change ‖iteratedFDeriv ℝ k (ρ⁻¹ • (fun w : V ↦ m w • (β (ρ • w.2.2) • F (π w)))) v‖ ≤ _
        rw [iteratedFDeriv_const_smul_apply (hsfull.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)),
          norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρp), Real.rpow_neg_one]
        have hfbound : ‖iteratedFDeriv ℝ k (fun w : V ↦ m w • (β (ρ • w.2.2) • F (π w))) v‖ ≤
            C k * L ^ (k-(Rstar-1)) := by simpa only [one_mul, Pi.smul_apply', Function.comp_def] using hfull
        exact (mul_le_mul_of_nonneg_left hfbound (inv_nonneg.mpr hρp.le)).trans_eq (by ring)
      · have he : (fun w : V ↦ m w • s w.1 (ρ • w.2.2)) =ᶠ[𝓝 v] fun _ ↦ 0 := by
          have hz := (notMem_tsupport_iff_eventuallyEq.mp hsupport).comp_tendsto
            (continuous_snd.snd.continuousAt : ContinuousAt (fun w : V ↦ w.2.2) v)
          filter_upwards [hz] with w hw
          have hreal : ellipticSourceMask f hK threshold (ρ • w.2.2) = 0 :=
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
    · change ‖iteratedFDeriv ℝ k
        (fun w : V ↦ (m w • s w.1 (ρ • w.2.2)).conjTranspose) v‖ ≤ _
      rw [norm_iteratedFDeriv_transport_conjTranspose]
      exact hforward
  · have hzero : m =ᶠ[𝓝 v] fun _ ↦ 0 := by
      by_cases hout : v.1 ∈ tsupport χout
      · have hin : v.2.1 ∉ tsupport (χs) := fun hin ↦ hv ⟨hout, hin, hfreq⟩
        have he := (notMem_tsupport_iff_eventuallyEq.mp hin).comp_tendsto
          (continuous_snd.fst.continuousAt (x := v))
        filter_upwards [he] with w hw
        exact mul_eq_zero_of_right (χout w.1) hw
      · have he := (notMem_tsupport_iff_eventuallyEq.mp hout).comp_tendsto
          (continuous_fst.continuousAt (x := v))
        filter_upwards [he] with w hw
        exact mul_eq_zero_of_left hw (f.inputMask w.2.1 : ℂ)
    have he : normalizedFullAmplitude (orientedMaskedPDOAmplitude backward χout (χs) s) ρ
        =ᶠ[𝓝 v] fun _ ↦ 0 := by
      filter_upwards [hzero] with w hw
      change χout w.1 * (f.inputMask w.2.1 : ℂ) = 0 at hw
      simp only [normalizedFullAmplitude, orientedMaskedPDOAmplitude, hw, zero_smul,
        Matrix.conjTranspose_zero, ite_self]
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
    change ‖iteratedFDeriv ℝ k (0 : V → CMat) v‖ ≤ _
    rw [show iteratedFDeriv ℝ k (0 : V → CMat) v = 0 from congrFun iteratedFDeriv_zero v, norm_zero]
    exact hnonneg

/-- Global smoothness of the same full normalized amplitudes, including
both literal orientations and the radial collar. This supplies smoothness on
the response owner's open determinant-gap domains without an additional
analytic premise (`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_normalized_elliptic_amplitude
    (hΩ : IsOpen Ω) (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout)
    {threshold : ℝ} (ht : 0 < threshold) (ρ : ℝ)
    (Q : E → Coeff) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius)) (residual backward : Bool) :
    ContDiff ℝ ∞ (normalizedFullAmplitude
      (orientedMaskedPDOAmplitude backward χout (χs)
        (if residual then ellipticResidualSymbol f hK threshold Q B
          else ellipticInverseSymbol f hK threshold Q)) ρ) := by
  let s := if residual then ellipticResidualSymbol f hK threshold Q B
    else ellipticInverseSymbol f hK threshold Q
  have hs : ContDiff ℝ ∞ (Function.uncurry s) := by
    cases residual
    · exact contDiff_ellipticInverseSymbol f hK hΩ ht Q hQ hmap
    · exact contDiff_ellipticResidualSymbol f hK hΩ ht Q B hQ hB hmap
  have hm : ContDiff ℝ ∞ (fun w : V ↦ χout w.1 * (f.inputMask w.2.1 : ℂ)) :=
    (ho.comp contDiff_fst).mul
      ((Complex.ofRealCLM.contDiff.comp f.inputMask_smooth).comp contDiff_snd.fst)
  have hforward : ContDiff ℝ ∞ (fun w : V ↦
      (χout w.1 * (f.inputMask w.2.1 : ℂ)) • s w.1 (ρ • w.2.2)) :=
    hm.smul (hs.comp (contDiff_fst.prodMk (contDiff_snd.snd.const_smul ρ)))
  cases backward
  · exact hforward
  · exact (Matrix.conjTransposeLinearEquiv (Fin (d+1)) (Fin (d+1)) ℝ ℂ).toContinuousLinearEquiv.contDiff.comp hforward

end JanetCartan.RegularSector.EllipticResponseProfiles
