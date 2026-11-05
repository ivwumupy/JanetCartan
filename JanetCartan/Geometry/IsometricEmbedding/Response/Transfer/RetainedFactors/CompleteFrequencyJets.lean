module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CappedKernels
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryProfiles
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.AmplitudeBudgets

/-!
# Full-frequency jets on the capped retained support

The complementary part of the integrated envelope needs the original joint
symbol jets on the entire multiplier support. Normalize by `1 + ‖ξ‖`, placing
every supported covector, including the high-pass shoulder, in one fixed
compact band. Contraction in the frequency variable then converts the original
normalized symbol budgets without losing a derivative or a scale power.
Consumers: `hbb`, `hΨb` and `hsourceΨ` in both integrated envelope endpoints,
for `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase UniformEvolution EvolutionIntegral
open SymbolBudgets FourierIntegral WholeImageGeometry
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "JPoint" => SymbolBudgets.TwoTimePoint d

/-- Every frequency of the original collared multiplier has a normalized
representative in a single fixed annulus. There is no frequency truncation
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_frequency_normalized_mem_sourceBand
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : RootState (Euclidean d)}
    {ε aperture : ℝ} (hε : 0 < ε) (haperture : 0 ≤ aperture)
    {ξ : E} (hξ : ξ ∈ retainedFrequencyDomain ℓ z ε aperture (1 / 2)) :
    (1 + ‖ξ‖)⁻¹ • ξ ∈ normalizedSourceBand
      (fullAngularCone ℓ z.2.2 ε aperture) (1 + ‖ξ‖) (1 / 3) 1 := by
  have hR : 0 < 1 + ‖ξ‖ := by positivity
  have hnorm : (1 / 2 : ℝ) < ‖ξ‖ := retainedFrequencyDomain_norm_lt ℓ hξ
  refine ⟨?_, ?_, ?_⟩
  · change (1 + ‖ξ‖) • ((1 + ‖ξ‖)⁻¹ • ξ) ∈ fullAngularCone ℓ z.2.2 ε aperture
    rw [smul_inv_smul₀ hR.ne']
    exact retainedFrequencyDomain_subset_fullAngularCone ℓ hε haperture hξ
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, ← div_eq_inv_mul]
    apply (lt_div_iff₀ hR).mpr
    linarith
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, ← div_eq_inv_mul]
    exact (div_lt_one hR).mpr (by linarith)

/-- The complete capped interval maps to the original compact amplitude
band, after the SAME normalization. This applies to either physical mask,
including every source point needed for the literal adjoint tail
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem capped_normalized_elapsedPoint_mem_bufferedJetSet
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : RootState (Euclidean d)}
    {ε src aperture : ℝ} (hε : 0 < ε) (hsrc : src ≤ ε)
    (haperture : 0 ≤ aperture) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) {x ξ : E}
    (hx : x ∈ elapsedPhysicalBox z (ε / 2))
    (hξ : ξ ∈ retainedFrequencyDomain ℓ z ε aperture (1 / 2)) :
    elapsedPoint t ((x, 0), (1 + ‖ξ‖)⁻¹ • ξ) ∈ bufferedJetSet ℓ z ε
      ((1 / 3) / (1 + aperture + ‖z.2.2‖ + ε)) (1 + ‖ℓ‖) := by
  have htε : t ∈ Icc (0 : ℝ) ε := ⟨ht.1, by linarith only [ht.2, hsrc, hε]⟩
  have hxε : x ∈ elapsedPhysicalBox z ε :=
    ⟨ball_subset_ball (by linarith) hx.1, ball_subset_ball (by linarith) hx.2⟩
  have hmem := normalizedSourceBand_mem_elapsedJetSet ℓ hε.le haperture
    (by norm_num : (0 : ℝ) < 1 / 3) (by positivity : 0 < 1 + ‖ξ‖)
    (p := (x, (1 + ‖ξ‖)⁻¹ • ξ))
    ⟨hxε, retained_frequency_normalized_mem_sourceBand ℓ hε haperture hξ⟩
  have hm := elapsedJetSet_mapsTo ℓ htε hmem
  change elapsedPoint t ((x, 0), (1 + ‖ξ‖)⁻¹ • ξ) ∈
    bufferedJetSet ℓ z ε _ ((1 + ‖ℓ‖) * 1) at hm
  simpa only [mul_one] using hm

private theorem norm_iteratedFDeriv_le_frequency_normalization
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set JPoint} (hU : IsOpen U) {f : JPoint → F}
    (hf : ContDiffOn ℝ ∞ f U) {R : ℝ} (hR : 1 ≤ R)
    {p : JPoint} (hp : p ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j f p‖ ≤
      ‖iteratedFDeriv ℝ j (fun v : JPoint ↦ f (v.1, R • v.2))
        (p.1, R⁻¹ • p.2)‖ := by
  let N : JPoint →L[ℝ] JPoint :=
    (ContinuousLinearMap.fst ℝ _ _).prod (R⁻¹ • ContinuousLinearMap.snd ℝ _ _)
  let D : JPoint →L[ℝ] JPoint :=
    (ContinuousLinearMap.fst ℝ _ _).prod (R • ContinuousLinearMap.snd ℝ _ _)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hN : ‖N‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change max ‖v.1‖ ‖R⁻¹ • v.2‖ ≤ 1 * ‖v‖
    rw [one_mul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRpos]
    exact max_le (norm_fst_le v) ((mul_le_of_le_one_left (norm_nonneg _)
      (inv_le_one_of_one_le₀ hR)).trans (norm_snd_le v))
  have hDN : D ∘ N = id := by
    funext v
    change (v.1, R • (R⁻¹ • v.2)) = v
    simp only [smul_inv_smul₀ hRpos.ne']
  have hO : IsOpen (D ⁻¹' U) := hU.preimage D.continuous
  have hNp : N p ∈ D ⁻¹' U := by
    change (D ∘ N) p ∈ U
    rwa [hDN]
  have hs : ContDiffOn ℝ ∞ (f ∘ D) (D ⁻¹' U) :=
    hf.comp D.contDiff.contDiffOn (fun _ hv ↦ hv)
  have he := N.iteratedFDerivWithin_comp_right hs hO.uniqueDiffOn
    (hO.preimage N.continuous).uniqueDiffOn hNp (i := j) (by simp)
  rw [iteratedFDerivWithin_of_isOpen j (hO.preimage N.continuous) hNp,
    iteratedFDerivWithin_of_isOpen j hO hNp] at he
  have heq : (f ∘ D) ∘ N = f := by rw [Function.comp_assoc, hDN, Function.comp_id]
  rw [heq] at he
  rw [he]
  apply ((iteratedFDeriv ℝ j (f ∘ D) (N p)).norm_compContinuousLinearMap_le
    (fun _ ↦ N)).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    pow_le_one₀ (norm_nonneg N) hN (n := j)

/-- Original joint amplitude derivatives on the FULL supported cone follow
from the retained order-zero seminorm on the fixed band. The correction and
full residual use `correction_order_zero_bound` before this lemma; their
order-minus-one gain remains in the separate annular estimate
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_complete_amplitude_jet_le
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : RootState (Euclidean d)}
    {ε src aperture : ℝ} (hε : 0 < ε) (hsrc : src ≤ ε)
    (haperture : 0 ≤ aperture)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (j : ℕ)
    (hbudget : BoundedTwoTimeOrderSeminorm 0
      (bufferedJetSet ℓ z ε ((1 / 3) / (1 + aperture + ‖z.2.2‖ + ε))
        (1 + ‖ℓ‖)) j W)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) {x ξ : E}
    (hx : x ∈ elapsedPhysicalBox z (ε / 2))
    (hξ : ξ ∈ retainedFrequencyDomain ℓ z ε aperture (1 / 2)) :
    ‖iteratedFDeriv ℝ j (jointAmplitude W) (elapsedPoint t ((x, 0), ξ))‖ ≤
      twoTimeOrderSeminorm 0
        (bufferedJetSet ℓ z ε ((1 / 3) / (1 + aperture + ‖z.2.2‖ + ε))
          (1 + ‖ℓ‖)) j W := by
  let R := 1 + ‖ξ‖
  have hR : 1 ≤ R := le_add_of_nonneg_right (norm_nonneg ξ)
  have hn := norm_iteratedFDeriv_le_frequency_normalization isOpen_univ
    hW.contDiffOn hR (mem_univ (elapsedPoint t ((x, 0), ξ))) j
  have hm := capped_normalized_elapsedPoint_mem_bufferedJetSet ℓ hε hsrc haperture ht hx hξ
  have hs : ContDiff ℝ ∞ (twoTimeOrderField 0 R W) := by
    simp only [twoTimeOrderField, pow_zero, one_smul]
    change ContDiff ℝ ∞ (fun v : JPoint ↦ jointAmplitude W (v.1, R • v.2))
    exact hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))
  have hc := norm_iteratedFDeriv_le_cNorm
    (isCompact_bufferedJetSet ℓ z ε ((1 / 3) / (1 + aperture + ‖z.2.2‖ + ε))
      (1 + ‖ℓ‖)) (hs.of_le (by simp : (j : ℕ∞ω) ≤ ∞)) hm le_rfl
  apply hn.trans
  apply le_trans _ (cNorm_twoTimeOrderField_le hbudget hR)
  simp only [twoTimeOrderField, pow_zero, one_smul] at hc ⊢
  change ‖iteratedFDeriv ℝ j (fun v : JPoint ↦ jointAmplitude W (v.1, R • v.2))
    (elapsedPoint t ((x, 0), (1 + ‖ξ‖)⁻¹ • ξ))‖ ≤ _ at hc
  simpa only [elapsedPoint_eq, spatialPart_smul, R] using hc

/-- The original retained conic phase has at most linear frequency growth
at every joint derivative order, on the COMPLETE capped interval and full
multiplier support. Its only analytic cost is the original phase producer's
coefficient shift one (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_complete_phase_jet_le
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : RootState (Euclidean d)}
    {ε src aperture b : ℝ} (hε : 0 < ε) (hsrc : src ≤ ε)
    (haperture : 0 ≤ aperture) (hεb : 4 * ε ≤ b)
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (phaseCost : ℕ → ℝ)
    (hphase : ∀ j, cNorm (closedBall (z.1, z) b) j (twoTimePhase C) ≤
      phaseCost j * (1 + cNorm KQ (j + 1) Q))
    (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) {x ξ : E}
    (hx : x ∈ elapsedPhysicalBox z (ε / 2))
    (hξ : ξ ∈ retainedFrequencyDomain ℓ z ε aperture (1 / 2)) :
    ‖iteratedFDeriv ℝ j (jointPhase (curriedPhase ℓ C)) (elapsedPoint t ((x, 0), ξ))‖ ≤
      (1 + ‖ξ‖) * retainedPhaseCost ℓ z ε
        ((1 / 3) / (1 + aperture + ‖z.2.2‖ + ε)) (1 + ‖ℓ‖) phaseCost j *
          (1 + cNorm KQ (j + 1) Q) := by
  let R := 1 + ‖ξ‖
  let ra := (1 / 3) / (1 + aperture + ‖z.2.2‖ + ε)
  let J := bufferedJetSet ℓ z ε ra (1 + ‖ℓ‖)
  let U := budgetCoordinates ⁻¹' domain ℓ C.target
  have hR : 1 ≤ R := le_add_of_nonneg_right (norm_nonneg ξ)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hra : 0 < ra := by dsimp [ra]; positivity
  have hU : IsOpen U := (isOpen_domain ℓ C.open_target).preimage budgetCoordinates.continuous
  have hs : ContDiffOn ℝ ∞ (jointPhase (curriedPhase ℓ C)) U :=
    contDiffOn_jointPhase_curriedExtend ℓ C.open_target hC
  have hp : elapsedPoint t ((x, 0), ξ) ∈ U := by
    have h := capped_elapsedPoint_mem_phase_plateau ℓ z hε hsrc ht hx hξ
    change budgetCoordinates (elapsedPoint t ((x, 0), ξ)) ∈ domain ℓ C.target
    rw [elapsedPoint_eq]
    change (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) ∈ domain ℓ C.target
    exact ⟨h.1, hbuffer (closedBall_subset_closedBall hεb h.2)⟩
  have hnorm := norm_iteratedFDeriv_le_frequency_normalization hU hs hR hp j
  have he : (fun v : JPoint ↦ jointPhase (curriedPhase ℓ C) (v.1, R • v.2)) =
      R • jointPhase (curriedPhase ℓ C) := by
    funext v
    exact extend_smul ℓ (twoTimePhase C) (budgetCoordinates v) hRpos
  have hJU : J ⊆ U := by
    intro p hp
    have hn := bufferedJetSet_normalizes ℓ (z := z) (b := 1 + ‖ℓ‖) hε.le hra
    exact ⟨hn.1 p hp, hbuffer (closedBall_subset_closedBall (by linarith) (hn.2 hp))⟩
  have hm : elapsedPoint t ((x, 0), R⁻¹ • ξ) ∈ J :=
    capped_normalized_elapsedPoint_mem_bufferedJetSet ℓ hε hsrc haperture ht hx hξ
  have hm' : ((elapsedPoint t ((x, 0), ξ)).1,
      R⁻¹ • (elapsedPoint t ((x, 0), ξ)).2) = elapsedPoint t ((x, 0), R⁻¹ • ξ) := by
    simp only [elapsedPoint_eq, spatialPart_smul]
  rw [he, hm', iteratedFDeriv_const_smul_apply
    ((hs.contDiffAt (hU.mem_nhds (hJU hm))).of_le (by simp)), norm_smul,
      Real.norm_eq_abs, abs_of_pos hRpos] at hnorm
  have hc := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
    (isCompact_bufferedJetSet ℓ z ε ra (1 + ‖ℓ‖))
    (fun p hp ↦ (hs.contDiffAt (hU.mem_nhds (hJU hp))).of_le (by simp : (j : ℕ∞ω) ≤ ∞))
    hm le_rfl
  have hb := retained_phase_coefficient_bound ℓ hε.le hra (by linarith : 2 * ε ≤ b)
    hbuffer hC KQ Q phaseCost hphase (rb := 1 + ‖ℓ‖) j
  exact hnorm.trans ((mul_le_mul_of_nonneg_left (hc.trans hb) hRpos.le).trans_eq (by ring))

/-- The SAME smooth representative inherits the full-frequency joint jets,
including all time derivatives and the high-pass shoulder. The fixed cutoff
is identically one as a germ on the actual capped support, so no new phase
budget or chart is assumed (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retained_complete_representative_jet_le
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : RootState (Euclidean d)}
    {ε src aperture b : ℝ} (hε : 0 < ε) (hsrc : src ≤ ε)
    (haperture : 0 ≤ aperture) (hεb : 4 * ε ≤ b)
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hbuffer : closedBall (z.1, z) b ⊆ C.target)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {χ : TwoTimePoint (Euclidean d) → ℝ}
    (hχ : ∀ p ∈ closedBall (z.1, z) (4 * ε), χ =ᶠ[𝓝 p] (fun _ ↦ 1))
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (phaseCost : ℕ → ℝ)
    (hphase : ∀ j, cNorm (closedBall (z.1, z) b) j (twoTimePhase C) ≤
      phaseCost j * (1 + cNorm KQ (j + 1) Q))
    (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (3 * src / 4)) {x ξ : E}
    (hx : x ∈ elapsedPhysicalBox z (ε / 2))
    (hξ : ξ ∈ retainedFrequencyDomain ℓ z ε aperture (1 / 2)) :
    ‖iteratedFDeriv ℝ j
        (jointPhase (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase C)))
        (elapsedPoint t ((x, 0), ξ))‖ ≤
      (1 + ‖ξ‖) * retainedPhaseCost ℓ z ε
        ((1 / 3) / (1 + aperture + ‖z.2.2‖ + ε)) (1 + ‖ℓ‖) phaseCost j *
          (1 + cNorm KQ (j + 1) Q) := by
  have hcoordinates : budgetCoordinates (elapsedPoint t ((x, 0), ξ)) =
      (x 0, (x 0 - t, (spatialPart x, spatialPart ξ))) := by
    rw [elapsedPoint_eq]
    rfl
  have he := (SmoothRepresentative.representative_eventuallyEq_phase ℓ C hδ hχ
    (capped_elapsedPoint_mem_phase_plateau ℓ z hε hsrc ht hx hξ)
    (hδhalf.trans hξ.2.le)).comp_tendsto
      (by simpa only [hcoordinates] using
        budgetCoordinates.continuous.tendsto (elapsedPoint t ((x, 0), ξ)))
  change jointPhase (SmoothRepresentative.curriedRepresentative ℓ δ hδ χ (twoTimePhase C))
    =ᶠ[𝓝 (elapsedPoint t ((x, 0), ξ))] jointPhase (curriedPhase ℓ C) at he
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact retained_complete_phase_jet_le ℓ hε hsrc haperture hεb hbuffer hC
    KQ Q phaseCost hphase j ht hx hξ

end JanetCartan.ResponseTransfer.RetainedFactors
