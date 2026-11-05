module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.CoveredAmplitudeProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.PhysicalAnnularJets

/-!
# Annular jets from the original selected frequency coverage

The existing physical retarded construction normalizes every supported
frequency into its own amplitude band with a dilation at least one. On the
stationary annulus the spatial frequency gap bounds the ratio of that dilation
to the envelope frequency. This proves the normalized jets on the original
band, including both physical masks and the literal doubled physical collar.
No enlarged amplitude budget or alternate family is required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral SymbolBudgets
open RegularSector.FinitePdo.RetainedConstruction
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "JPoint" => SymbolBudgets.TwoTimePoint d

open FourierIntegral PrimitiveProfiles FullAmplitudePrimitiveBudget.Local

/-- The differentiated multiplier restricts every symbol jet to its original
closed support; outside it all multiplier jets vanish. This is the localized
Leibniz step for `app:ch_response:eq:direct-envelope-profile`. -/
private theorem cNorm_masked_symbol_le_of_supported_jets
    {K : Set (Point (d+1))} (hK : IsCompact K)
    (f : Point (d+1) → ℂ) (g : Point (d+1) → Matrix (Fin q) (Fin q) ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : ℕ)
    {A : ℝ} (hA : 0 ≤ A)
    (hjets : ∀ k ≤ j, ∀ x ∈ K, x ∈ tsupport f → ‖iteratedFDeriv ℝ k g x‖ ≤ A) :
    cNorm K j (fun x ↦ f x • g x) ≤ (j+1 : ℝ) * 2^j * cNorm K j f * A := by
  have hb : ∀ k ≤ j, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (fun x ↦ f x • g x) x‖ ≤ 2^j * cNorm K j f * A := by
    intro k hk x hx
    apply (norm_iteratedFDeriv_smul_on_open_le isOpen_univ hf.contDiffOn hg.contDiffOn
      (mem_univ x) k).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * cNorm K j f * A := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        by_cases hsupport : x ∈ tsupport f
        · exact mul_le_mul (mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_le_cNorm hK (hf.of_le (by simp)) hx (hi'.trans hk))
              (Nat.cast_nonneg _))
            (hjets (k-i) ((Nat.sub_le k i).trans hk) x hx hsupport)
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg ..))
        · have he : iteratedFDeriv ℝ i f x = 0 := by
            by_contra hn
            exact hsupport (support_iteratedFDeriv_subset i hn)
          rw [he,norm_zero,mul_zero,zero_mul]
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (cNorm_nonneg ..)) hA
      _ = 2^k * cNorm K j f * A := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        norm_cast
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
          (cNorm_nonneg ..)) hA
  have h := cNorm_le_sum_of_bounds
    (fun k (_ : k ≤ j) ↦ mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)^j)
      (cNorm_nonneg ..)) hA) hb
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,
    Nat.cast_one,mul_assoc] using h

/-- Normalize a supported annular jet using the SAME original radial-band
coverage. The positive spatial frequency gap bounds the ratio of dilations;
thus both orders retain their exact lambda normalization. Consumer: annular
jets for `app:ch_response:eq:direct-envelope-profile`. -/
theorem retained_annular_symbol_jet_le_of_diagonal_coverage
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε ra rb δ : ℝ} (hδ : 0 < δ)
    {β : E → ℂ} (hcoverage : DiagonalFrequencyCoverage ℓ z.2.2 ε ra rb β)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (o j : ℕ) (hbudget : BoundedTwoTimeOrderSeminorm o
      (bufferedJetSet ℓ z ε ra rb) j W)
    {lam : ℝ} (hlam : 1 ≤ lam)
    {base : ℝ × (ℝ × Euclidean d)}
    (hbase : base ∈ closedBall z.1 (2*ε) ×ˢ
      (closedBall z.1 (2*ε) ×ˢ closedBall z.2.1 (2*ε)))
    {ξ : E} (hξ : lam • ξ ∈ tsupport β) (hgap : δ ≤ ‖spatialPart ξ‖) :
    ‖iteratedFDeriv ℝ j (twoTimeOrderField o lam W) (base,spatialPart ξ)‖ ≤
      (max 1 δ⁻¹) ^ (j+o) * twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W := by
  obtain ⟨R,hR,η,hη,he,hnorm⟩ := hcoverage (lam • ξ) hξ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hlampos : 0 < lam := zero_lt_one.trans_le hlam
  have htpos : 0 < lam/R := div_pos hlampos hRpos
  have hratio : lam/R ≤ δ⁻¹ := by
    rw [spatialPart_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hlampos] at hnorm
    apply (div_le_iff₀ hRpos).mpr
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hδ).mpr
    exact (mul_le_mul_of_nonneg_left hgap hlampos.le).trans hnorm
  let c : ℝ := max 1 δ⁻¹
  have hc : 1 ≤ c := le_max_left _ _
  have hratioC : lam/R ≤ c := hratio.trans (le_max_right _ _)
  let N : JPoint →L[ℝ] JPoint :=
    (ContinuousLinearMap.fst ℝ _ _).prod ((lam/R) • ContinuousLinearMap.snd ℝ _ _)
  have hN : ‖N‖ ≤ c := by
    apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hc)
    intro v
    change max ‖v.1‖ ‖(lam/R) • v.2‖ ≤ c * ‖v‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos htpos]
    exact max_le ((norm_fst_le v).trans (le_mul_of_one_le_left (norm_nonneg v) hc))
      (mul_le_mul hratioC (norm_snd_le v) (norm_nonneg _) (zero_le_one.trans hc))
  have hRs : ContDiff ℝ ∞ (twoTimeOrderField o R W) :=
    (hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))).const_smul (R^o)
  have hcomp : twoTimeOrderField o lam W = (lam/R)^o • (twoTimeOrderField o R W ∘ N) := by
    funext v
    change lam^o • jointAmplitude W (v.1,lam • v.2) =
      (lam/R)^o • (R^o • jointAmplitude W (v.1,R • ((lam/R) • v.2)))
    rw [smul_smul,smul_smul,← mul_pow]
    have heq : R * (lam/R) = lam := by field_simp
    have heq' : lam/R * R = lam := by field_simp
    rw [heq,heq']
  have hNpoint : N (base,spatialPart ξ) = (base,η) := by
    change (base,(lam/R) • spatialPart ξ) = (base,η)
    congr 1
    rw [div_eq_inv_mul,mul_smul,← spatialPart_smul,he,inv_smul_smul₀ hRpos.ne']
  rw [hcomp,iteratedFDeriv_const_smul_apply ((hRs.comp N.contDiff).contDiffAt.of_le (by simp)),
    norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos htpos o)]
  have hb := Pseudodifferential.norm_iteratedFDeriv_comp_linear_le N
    (twoTimeOrderField o R W) hRs j (base,spatialPart ξ)
  rw [hNpoint] at hb
  have hj := (norm_iteratedFDeriv_le_cNorm
    (isCompact_bufferedJetSet ℓ z ε ra rb)
    (hRs.of_le (by simp : (j : ℕ∞ω) ≤ ∞)) (show (base,η) ∈ _ from ⟨hbase,hη⟩)
    le_rfl).trans (cNorm_twoTimeOrderField_le hbudget hR)
  have hnj : ‖N‖^j ≤ c^j := pow_le_pow_left₀ (norm_nonneg N) hN j
  calc
    _ ≤ c^o * (twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W * c^j) :=
      mul_le_mul (pow_le_pow_left₀ htpos.le hratioC o)
        (hb.trans (mul_le_mul hj hnj (pow_nonneg (norm_nonneg N) j)
          (twoTimeOrderSeminorm_nonneg ..))) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hc) o)
    _ = _ := by rw [pow_add]; ring

/-- Both physical masks and the literal multiplier preserve the normalized
annular symbol bound from the original coverage. Outside the multiplier's
closed support all of its jets vanish. Inside it, only the original band is
used. Consumer: the annular input of
`app:ch_response:eq:direct-envelope-profile`. -/
theorem retained_elapsed_order_cNorm_le_of_diagonal_coverage
    {K : Set (Point (d+1))} (hK : IsCompact K)
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε ra rb δ : ℝ} (hδ : 0 < δ) {β : E → ℂ}
    (hcoverage : DiagonalFrequencyCoverage ℓ z.2.2 ε ra rb β)
    (hgap : ∀ p ∈ K, δ ≤ ‖spatialPart p.2‖)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (o j : ℕ)
    (hβbound : BoundedNormalizedSeminorm K j (jointMultiplier β))
    (hbudget : BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W)
    {t lam : ℝ} (hlam : 1 ≤ lam)
    (hbase : ∀ p ∈ K, (elapsedPoint t p).1 ∈ closedBall z.1 (2*ε) ×ˢ
      (closedBall z.1 (2*ε) ×ˢ closedBall z.2.1 (2*ε))) :
    cNorm K j (lam^o • normalizedField lam (uncurry (elapsedAmplitude W χout χsource β t))) ≤
      amplitudeMaskConstant K j χout χsource β * (max 1 δ⁻¹)^(j+o) *
        twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W := by
  let c := max 1 δ⁻¹
  have hc : 1 ≤ c := le_max_left _ _
  let A := c^(j+o) * twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg (zero_le_one.trans hc) _) (twoTimeOrderSeminorm_nonneg ..)
  let f := normalizedField lam (jointMultiplier β)
  let g := twoTimeOrderField o lam W ∘ elapsedPoint t
  have hf : ContDiff ℝ ∞ f := hβ.comp (contDiff_snd.const_smul lam)
  have hfield : ContDiff ℝ ∞ (twoTimeOrderField o lam W) :=
    (hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul lam))).const_smul (lam^o)
  have hg : ContDiff ℝ ∞ g := hfield.comp (elapsedLinear.contDiff.add contDiff_const)
  have hjets : ∀ k ≤ j, ∀ p ∈ K, p ∈ tsupport f → ‖iteratedFDeriv ℝ k g p‖ ≤ A := by
    intro k hk p hp hsupport
    have hsupp : lam • p.2 ∈ tsupport β :=
      tsupport_comp_subset_preimage β (continuous_snd.const_smul lam) hsupport
    have hn := norm_iteratedFDeriv_preAffine_le elapsedLinear (elapsedTranslation t)
      isOpen_univ hfield.contDiffOn (x := p) (mem_univ _) k
    have hn' : ‖iteratedFDeriv ℝ k g p‖ ≤
        ‖iteratedFDeriv ℝ k (twoTimeOrderField o lam W) (elapsedPoint t p)‖ :=
      hn.trans (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) norm_elapsedLinear_le))
    have hbudgetk : BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) k W := by
      refine ⟨twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W, ?_⟩
      rintro _ ⟨R,rfl⟩
      exact (cNorm_mono_order hk).trans (cNorm_twoTimeOrderField_le hbudget R.2)
    have hsem : twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) k W ≤
        twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W := by
      apply Real.sSup_le _ (twoTimeOrderSeminorm_nonneg ..)
      rintro _ ⟨R,rfl⟩
      exact (cNorm_mono_order hk).trans (cNorm_twoTimeOrderField_le hbudget R.2)
    have hb := retained_annular_symbol_jet_le_of_diagonal_coverage ℓ z hδ hcoverage
      W hW o k hbudgetk hlam (hbase p hp) hsupp (hgap p hp)
    have hpoint : ((elapsedPoint t p).1,spatialPart p.2) = elapsedPoint t p := by
      rw [elapsedPoint_eq]
    rw [hpoint] at hb
    exact hn'.trans (hb.trans (mul_le_mul (pow_le_pow_right₀ hc (by omega)) hsem
      (twoTimeOrderSeminorm_nonneg ..) (pow_nonneg (zero_le_one.trans hc) _)))
  have hinner := cNorm_masked_symbol_le_of_supported_jets hK f g hf hg j hA hjets
  have hM : ContDiff ℝ ∞ (physicalMasks χout χsource) :=
    (ho.comp contDiff_fst.fst).mul (hs.comp contDiff_fst.snd)
  rw [elapsedOrderField_eq]
  apply (cNorm_smul_on_open_le hK isOpen_univ (subset_univ K) hM.contDiffOn
    (hf.smul hg).contDiffOn j).trans
  have hinner' := hinner.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (cNorm_normalizedField_le hβbound hlam)
      (by positivity : 0 ≤ (j+1 : ℝ)*2^j)) hA)
  apply (mul_le_mul_of_nonneg_left hinner'
    (mul_nonneg (by positivity) (cNorm_nonneg ..))).trans_eq
  dsimp only [amplitudeMaskConstant,A,c]
  ring


open RegularSector.Characteristic.ResidualCoordinates RegularSector.FiniteMasks
open DirectEvolution AnnularSobolev RetainedFactors
variable {p : ℕ}
local notation "Par" => Euclidean p
local notation "Joint" => (E × Par) × CarrierVariables (d+1)

/-- The literal physical annular amplitude uses its original band's diagonal
coverage and the stationary frequency gap, without a larger amplitude band.
Both shoulders and the `2*threshold` cutoff remain inside the differentiated
product. Consumer: selected full-source annular history profiles
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_physical_annular_cNorm_le_of_diagonal_coverage
    {K : Set Joint} (hK : IsCompact K)
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε ra rb δgap : ℝ} (hε : 0 < ε) (hδgap : 0 < δgap)
    (hchart : ∀ v ∈ K, annularCarrierCoordinates v ∈ retainedGraphDomain ℓ z ε)
    (hgap : ∀ v ∈ K, δgap ≤ ‖spatialPart v.2.snd‖)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask) (index : Fin (d+1))
    {threshold : ℝ} (hthreshold : 1 ≤ threshold)
    (hcoverage : DiagonalFrequencyCoverage ℓ z.2.2 ε ra rb
      (fun ξ ↦ (dilatedConicMask mask (2*threshold) (physicalCoordinates index ξ) : ℂ)))
    (π : E → ℂ) (hπ : ContDiff ℝ ∞ π)
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1)) (D : ℕ → ℝ) (o j : ℕ)
    (hfinite : BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W)
    (hbudget : twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W ≤
      D j * (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B))
    {t lam : ℝ} (ht : t ∈ Icc 0 ε) (hlam : 1 ≤ lam) :
    cNorm K j (Function.uncurry (normalizedAnnularElapsedAmplitude (P := Par) W
      χout χsource (fun ξ ↦ (dilatedConicMask mask (2*threshold) (physicalCoordinates index ξ) : ℂ)) π t lam (-(o : ℤ)))) ≤
      physicalAnnularMaskConstant K j χout χsource mask index threshold π *
        (max 1 δgap⁻¹)^(j+o) * D j *
        (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B) := by
  let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask (2*threshold) (physicalCoordinates index ξ) : ℂ)
  let K' := annularCarrierCoordinates '' K
  let F := lam ^ o • normalizedField lam (uncurry (elapsedAmplitude W χout χsource β t))
  have hK' : IsCompact K' := hK.image annularCarrierCoordinates.continuous
  have hβ : ContDiff ℝ ∞ β :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_dilatedConicMask hm (2*threshold)).comp
      (physicalCoordinates index).contDiff)
  have hzero : ∀ v ∈ K', v.2 ≠ 0 := by
    rintro v ⟨w, hw, rfl⟩ he
    have hp := (hchart w hw).2.1
    change 0 < ℓ (spatialPart (annularCarrierCoordinates w).2) at hp
    have hz : spatialPart (annularCarrierCoordinates w).2 = 0 := by rw [he]; rfl
    rw [hz, map_zero] at hp
    exact lt_irrefl _ hp
  have hβbound : BoundedNormalizedSeminorm K' j (jointMultiplier β) :=
    RegularSector.FiniteEvolution.PhysicalCutoff.boundedNormalizedSeminorm_physical_dilatedConicMask
      hm index hthreshold hK' hzero j
  have hbase : ∀ v ∈ K', (elapsedPoint t v).1 ∈ closedBall z.1 (2*ε) ×ˢ
      (closedBall z.1 (2*ε) ×ˢ closedBall z.2.1 (2*ε)) := by
    rintro v ⟨w,hw,rfl⟩
    have hx := (hchart w hw).1
    have hx' : (annularCarrierCoordinates w).1.1 ∈ elapsedPhysicalBox z ε :=
      ⟨ball_subset_ball (by linarith) hx.1,ball_subset_ball (by linarith) hx.2⟩
    have hb := elapsed_mem_bufferedBase hε ht hx'
    rw [elapsedPoint_eq]
    simpa only [mem_prod,mem_closedBall,Prod.dist_eq,max_le_iff] using ball_subset_closedBall hb
  have hgap' : ∀ v ∈ K', δgap ≤ ‖spatialPart v.2‖ := by
    rintro v ⟨w,hw,rfl⟩
    exact hgap w hw
  have hF : ContDiff ℝ ∞ F :=
    ((contDiff_uncurry_elapsedAmplitude W χout χsource β hW ho hs hβ t).comp
      (contDiff_fst.prodMk (contDiff_snd.const_smul lam))).const_smul (lam ^ o)
  have hπ' : ContDiff ℝ ∞ (fun v : Joint ↦ π v.2.snd) :=
    hπ.comp ((WithLp.sndL 2 ℝ E E).contDiff.comp contDiff_snd)
  have hprod := cNorm_smul_on_open_le hK isOpen_univ (subset_univ K)
    hπ'.contDiffOn (hF.comp annularCarrierCoordinates.contDiff).contDiffOn j
  have hpre := cNorm_preAffine_contraction_le (K := K) annularCarrierCoordinates
    norm_annularCarrierCoordinates_le 0 hK' isOpen_univ (subset_univ K')
    hF.contDiffOn (fun v hv ↦ by simpa only [add_zero] using
      (show annularCarrierCoordinates v ∈ K' from ⟨v, hv, rfl⟩)) j
  simp only [add_zero] at hpre
  have helapsed := retained_elapsed_order_cNorm_le_of_diagonal_coverage hK' ℓ z hδgap
    hcoverage hgap' W hW χout χsource ho hs hβ o j hβbound hfinite hlam hbase
  have hsymbol := mul_le_mul_of_nonneg_left hbudget
    (mul_nonneg (amplitudeMaskConstant_nonneg K' j χout χsource β) (by positivity : 0 ≤ (max 1 δgap⁻¹)^(j+o)))
  rw [normalizedAnnularElapsedAmplitude_eq_orderField W χout χsource β π t
    (zero_lt_one.trans_le hlam).ne' o]
  refine hprod.trans ((mul_le_mul_of_nonneg_left
    (hpre.trans (helapsed.trans hsymbol))
      (mul_nonneg (by positivity) (cNorm_nonneg _ _ _))).trans_eq ?_)
  change _ = ((_ * _) * _) * _ * _
  ring

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
