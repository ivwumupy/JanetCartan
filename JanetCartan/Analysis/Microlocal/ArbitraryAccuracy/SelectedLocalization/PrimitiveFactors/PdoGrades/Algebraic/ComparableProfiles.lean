module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.ComparableCarrier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.SelectedPhysicalProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.NormalizedGerms
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.LocalCalculus
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff.Multiplier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal

/-!
# Comparable joint grades of the entire selected algebraic residual

The fixed doubled cutoff, both physical masks, complete source product and
full zeroth-order coefficient are retained. The actual `Kpdo` is the one in
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
The original coefficient reserve absorbs the first jet; the offset is zero.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open RegularSector.FiniteEvolution.PhysicalCutoff
open CharacteristicTransport.CompleteResidual ResidualLocalization FourierIntegral
open FourierIntegral.PrimitiveProfiles FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Comparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry FiniteChain.Retarded.KernelDecay
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- Quantitative comparable grades for the SAME selected algebraic symbol
in the finite direct operator ledger. The literal `Kpdo`, both masks and both
orientations are included. The inverse domain input is the retained producer's
constant-field certificate at `2*f.radialThreshold`; no symbol estimate is an
input. The order-minus-one factor is retained before common-order domination.
The original coefficient profiles and reserve are preserved, with offset ZERO.
Consumer: branch three of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_algebraic_comparable_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall A₀ f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (a b : ℝ) (ha : 0 < a) (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    let J := frequencyAnnulus (n := d+1) (a / (16*annulusFactor 1 1))
      (4 * max 1 (4*annulusFactor 1 1*b))
    let Z := fun p ↦ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p)
    let Kpdo := fun p ↦ comparableJointCarrier 1 1 a b ((Prod.fst '' Z p) ×ˢ J)
      (Z p) (frequencyAnnulus a b)
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ A k * L ^ (k - Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ A k * L ^ (k - Rstar)) →
      ∀ (p : f.centers) (backward : Bool) k v, v ∈ Kpdo p →
        ‖iteratedFDeriv ℝ k (fun w : V ↦ orientedMaskedPDOAmplitude backward
          (endpointOutputMask f p output) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) Q B 1) w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
            ρ ^ (-1 : ℝ) * C k * L ^ k := by
  classical
  intro J Z Kpdo
  have hth : 1 ≤ threshold := f.radialThreshold_ge_one.trans ht
  have htpos : 0 < threshold := zero_lt_one.trans_le hth
  have hJ : IsCompact J := isCompact_frequencyAnnulus _ _
  have hJzero : (0 : E) ∉ J := by
    intro hz
    have hp : 0 < a / (16*annulusFactor 1 1) := by
      have := two_le_annulusFactor 1 1
      positivity
    exact (not_le.mpr hp) (by simpa only [norm_zero] using hz.1)
  have hK p : IsCompact (Kpdo p) := by
    have hz : IsCompact (Z p) := (endpointOutputMask_properties f p ho hoc hos).2.1.prod
      (chartPhysicalMasks_properties f p).2.2.2.1
    exact isCompact_comparableJointCarrier 1 1 a b
      ((hz.image continuous_fst).prod hJ) hz (isCompact_frequencyAnnulus _ _)
  have hcarrier p v (hv : v ∈ Kpdo p) :=
    (selected_algebraic_comparable_carrier_inputs f p output hos a b ha).2.2 v hv
  obtain ⟨D, hD, hcore⟩ := exists_selected_coefficientPhysicalAction_joint_profile
    f hΩ hRQ hKΩ hc hdom J hJ hJzero A hA
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
  let m : f.centers → V → ℂ := fun p v ↦
    endpointOutputMask f p output v.1.1 * chartInputMask f p v.1.2
  have hm p : ContDiff ℝ ∞ (m p) :=
    ((endpointOutputMask_properties f p ho hoc hos).1.comp contDiff_fst.fst).mul
      ((chartPhysicalMasks_properties f p).2.1.comp contDiff_fst.snd)
  let β := fun p ↦ selectedEndpointMultiplier f p threshold
  let Jβ := fun p ↦ πβ '' Kpdo p
  have hJβ p : IsCompact (Jβ p) := (hK p).image πβ.continuous
  have hβnorm p k : BoundedNormalizedSeminorm (Jβ p) k (fun w : ℝ × E ↦ β p w.2) :=
    boundedNormalizedSeminorm_physical_dilatedConicMask (f.angularMask_smooth p)
      (f.chart p).index hth (hJβ p) (by
        rintro w ⟨v, hv, rfl⟩
        exact fun he ↦ hJzero (he ▸ (hcarrier p v hv).2.2)) k
  let T := fun k ↦ ∑ p, cNorm (Kpdo p) k (m p)
  let G := fun k ↦ ∑ p, normalizedSeminorm (Jβ p) k (fun w : ℝ × E ↦ β p w.2)
  have hT k : 0 ≤ T k := Finset.sum_nonneg (fun _ _ ↦ cNorm_nonneg _ _ _)
  have hG k : 0 ≤ G k := Finset.sum_nonneg (fun _ _ ↦ normalizedSeminorm_nonneg _ _ _)
  let C := derivativeConvolution T (derivativeConvolution G D)
  have hC k : 0 ≤ C k := derivativeConvolution_nonneg hT (derivativeConvolution_nonneg hG hD) k
  refine ⟨C, hC, ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hQr hQp hBp p backward k v hv
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hvphys := hcarrier p v hv
  let bρ : E → ℂ := fun ξ ↦ β p (ρ • ξ)
  have hforward : ‖iteratedFDeriv ℝ k (fun w : V ↦
      m p w • selectedAlgebraicSymbol f p (2*threshold) Q B 1 w.1.1 (ρ • w.2.1)) v‖ ≤
        ρ ^ (-1 : ℝ) * C k * L ^ k := by
    by_cases hsupport : v.2.1 ∈ tsupport bρ
    · have hGs := contDiffAt_selected_coefficientConicBminus_of_retained_domain
        f p hRQ hKΩ (hc p) (Q (physicalCoordinates (f.chart p).index v.1.1))
        (hQr (hKΩ hvphys.2.1)) (hdom p _ (hQr (hKΩ hvphys.2.1))) v.2.1
        (fun he ↦ hJzero (he ▸ hvphys.2.2))
        (tsupport_selectedEndpointMultiplier_normalized_subset f p htpos hρpos hsupport)
      have hq := hQ.contDiffAt (hΩ.mem_nhds (hKΩ hvphys.2.1))
      have hb := hB.contDiffAt (hΩ.mem_nhds (hKΩ hvphys.2.1))
      let F : E × E → CMat := fun w ↦ coefficientConicPhysicalAction
        (f.chart p).radialSection (f.chart p).index (f.chart p).row (f.chart p).col (f.chart p).root
        ((Q (physicalCoordinates (f.chart p).index w.1),
          (fderiv ℝ Q (physicalCoordinates (f.chart p).index w.1),
            B (physicalCoordinates (f.chart p).index w.1))), w.2)
      have hP : ContDiff ℝ ∞ (fun w : E × E ↦ physicalCoordinates (f.chart p).index w.1) :=
        (physicalCoordinates (f.chart p).index).contDiff.comp contDiff_fst
      have hF : ContDiffAt ℝ ∞ F (π v) :=
        (contDiffAt_coefficientConicPhysicalAction _ _ _ _ _ _ hGs).comp (π v)
          (((hq.comp (π v) hP.contDiffAt).prodMk
            (((hq.fderiv_right (m := ∞) (by simp)).comp (π v) hP.contDiffAt).prodMk
              (hb.comp (π v) hP.contDiffAt))).prodMk contDiffAt_snd)
      have hFp := hF.comp v π.contDiff.contDiffAt
      have hFjet j : ‖iteratedFDeriv ℝ j (F ∘ π) v‖ ≤ D j * L ^ j := by
        apply (algebraic_norm_iteratedFDeriv_comp_linear_at_le π hF j).trans
        apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg π) hπ)).trans
        exact hcore Rstar hR L hL Q B hQ hB hQr hQp hBp p threshold ρ htpos hρpos
          (π v) hvphys.2.1 hvphys.2.2 hsupport j
      have hbs : ContDiff ℝ ∞ (fun w : V ↦ β p (ρ • w.2.1)) :=
        (selectedEndpointMultiplier_bounds f p threshold).1.comp (contDiff_snd.fst.const_smul ρ)
      have hbj j : ‖iteratedFDeriv ℝ j (fun w : V ↦ β p (ρ • w.2.1)) v‖ ≤ G j * L ^ j := by
        let g : ℝ × E → ℂ := normalizedField ρ (fun w : ℝ × E ↦ β p w.2)
        have hg : ContDiff ℝ ∞ g :=
          (selectedEndpointMultiplier_bounds f p threshold).1.comp (contDiff_snd.const_smul ρ)
        change ‖iteratedFDeriv ℝ j (g ∘ πβ) v‖ ≤ _
        apply (algebraic_norm_iteratedFDeriv_comp_linear_at_le πβ hg.contDiffAt j).trans
        apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg πβ) hπβ)).trans
        apply ((norm_iteratedFDeriv_le_cNorm (hJβ p) (hg.of_le (by simp))
          (mem_image_of_mem πβ hv) le_rfl).trans (cNorm_normalizedField_le (hβnorm p j) hρ)).trans
        exact (Finset.single_le_sum (fun p _ ↦ normalizedSeminorm_nonneg (Jβ p) j
          (fun w : ℝ × E ↦ β p w.2)) (Finset.mem_univ p)).trans
          (le_mul_of_one_le_right (hG j) (one_le_pow₀ hL))
      have hmj j : ‖iteratedFDeriv ℝ j (m p) v‖ ≤ T j * L ^ j :=
        (norm_iteratedFDeriv_le_cNorm (hK p) ((hm p).of_le (by simp)) hv le_rfl).trans
          ((Finset.single_le_sum (fun p _ ↦ cNorm_nonneg (Kpdo p) j (m p)) (Finset.mem_univ p)).trans
            (le_mul_of_one_le_right (hT j) (one_le_pow₀ hL)))
      have hprod j := algebraic_norm_iteratedFDeriv_smul_grades hbs.contDiffAt hFp hG
        (zero_le_one.trans hL) hbj (S := 1) (by simpa only [one_mul] using hFjet) j
      have hfull := algebraic_norm_iteratedFDeriv_smul_grades (hm p).contDiffAt
        (hbs.contDiffAt.smul hFp) hT (zero_le_one.trans hL) hmj hprod k
      have he := (selected_algebraic_normalized_eventuallyEq_coefficient_action
        f p ht hρpos Q B (π v) hvphys.1 hq hGs).comp_tendsto π.continuous.continuousAt
      have hefull : (fun w : V ↦ m p w • selectedAlgebraicSymbol f p (2*threshold) Q B 1
          w.1.1 (ρ • w.2.1)) =ᶠ[𝓝 v]
          fun w : V ↦ ρ⁻¹ • (m p w • (β p (ρ • w.2.1) • F (π w))) := by
        filter_upwards [he] with w hw
        change selectedAlgebraicSymbol f p (2*threshold) Q B 1 w.1.1 (ρ • w.2.1) = _ at hw
        rw [hw]
        exact smul_comm _ _ _
      have hsfull : ContDiffAt ℝ ∞ (fun w : V ↦ m p w • (β p (ρ • w.2.1) • F (π w))) v :=
        (hm p).contDiffAt.smul (hbs.contDiffAt.smul hFp)
      rw [(hefull.iteratedFDeriv ℝ k).eq_of_nhds]
      change ‖iteratedFDeriv ℝ k (ρ⁻¹ • (fun w : V ↦ m p w • (β p (ρ • w.2.1) • F (π w)))) v‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply (hsfull.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)),
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρpos), Real.rpow_neg_one]
      have hfbound : ‖iteratedFDeriv ℝ k (fun w : V ↦ m p w • (β p (ρ • w.2.1) • F (π w))) v‖ ≤
          C k * L ^ k := by
        change ‖iteratedFDeriv ℝ k (fun w : V ↦ m p w • (β p (ρ • w.2.1) • F (π w))) v‖ ≤
          1 * C k * L ^ k at hfull
        simpa only [one_mul] using hfull
      exact (mul_le_mul_of_nonneg_left hfbound (inv_nonneg.mpr hρpos.le)).trans_eq (by ring)
    · have he : (fun w : V ↦ m p w • selectedAlgebraicSymbol f p (2*threshold) Q B 1
          w.1.1 (ρ • w.2.1)) =ᶠ[𝓝 v] (fun _ ↦ 0) := by
        have hzero := (notMem_tsupport_iff_eventuallyEq.mp hsupport).comp_tendsto
          (continuous_snd.fst.continuousAt : ContinuousAt (fun w : V ↦ w.2.1) v)
        filter_upwards [hzero] with w hw
        rw [selected_algebraic_symbol_zero_of_multiplier_zero f p threshold Q B w.1.1 (ρ • w.2.1) hw,
          smul_zero]
      rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
      change ‖iteratedFDeriv ℝ k (0 : V → CMat) v‖ ≤ _
      have hd0 : iteratedFDeriv ℝ k (0 : V → CMat) v = 0 :=
        congrFun (show iteratedFDeriv ℝ k (0 : V → CMat) = 0 from iteratedFDeriv_zero) v
      rw [hd0, norm_zero]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hρpos.le _) (hC k))
        (pow_nonneg (zero_le_one.trans hL) k)
  cases backward
  · exact hforward
  · simpa only [orientedMaskedPDOAmplitude, ↓reduceIte,
      norm_iteratedFDeriv_transport_conjTranspose] using hforward

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
