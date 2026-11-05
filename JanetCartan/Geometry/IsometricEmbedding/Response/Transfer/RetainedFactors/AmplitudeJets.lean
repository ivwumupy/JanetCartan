module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.FiniteCover
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.AmplitudeBudgets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Support
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Basic

/-!
# Original coefficient budgets for the retained normalized annular amplitude

The consumer is the `hαjet` premise of
`IntegratedEnvelope.Assembly.fullElapsedEnvelope_hasEnvelopeProfile_of_primitive_jets`
in `app:ch_response:eq:direct-envelope-profile`. The full two-position amplitude,
both physical masks, original dilated multiplier and order factor are retained.
Only the original `twoTimeOrderSeminorm` bound from `UniformAmplitudes` is used;
no bound for a transferred amplitude or operator is assumed.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors
open FourierIntegral PrimitiveProfiles FullAmplitudePrimitiveBudget.Local
open RegularSector.Characteristic RegularSector.Characteristic.UniformEvolution
open RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open RegularSector.FiniteMasks ConicPhase DirectEvolution AnnularSobolev

variable {d q p : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean p
local notation "Joint" => (E × Par) × CarrierVariables (d + 1)

/-- Forget only the external carrier parameter, retaining output, source and
normalized covector. This is the literal amplitude substitution in
`app:ch_response:eq:direct-envelope-profile`. -/
def annularCarrierCoordinates : Joint →L[ℝ] Point (d + 1) :=
  (((ContinuousLinearMap.fst ℝ E Par).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((WithLp.fstL 2 ℝ E E).comp (ContinuousLinearMap.snd ℝ _ _))).prod
      ((WithLp.sndL 2 ℝ E E).comp (ContinuousLinearMap.snd ℝ _ _))

/-- The amplitude coordinate substitution has no norm or derivative loss
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_annularCarrierCoordinates_le :
    ‖annularCarrierCoordinates (d := d) (p := p)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change max (max ‖v.1.1‖ ‖v.2.fst‖) ‖v.2.snd‖ ≤ 1 * ‖v‖
  rw [one_mul]
  exact max_le (max_le ((norm_fst_le v.1).trans (norm_fst_le v))
    ((WithLp.norm_fst_le E v.2).trans (norm_snd_le v)))
      ((WithLp.norm_snd_le E v.2).trans (norm_snd_le v))

/-- Exact conversion of the direct-envelope normalization to the original
retained order-`-o` symbol. The scalar `lam^o` cancels precisely the order
factor; there is no extra power of the envelope scale
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalizedAnnularElapsedAmplitude_eq_orderField
    (W : TwoTimeAmplitude d q) (χout χsource β π : E → ℂ)
    (t : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (o : ℕ) :
    Function.uncurry (normalizedAnnularElapsedAmplitude (P := Par)
      W χout χsource β π t lam (-(o : ℤ))) =
    fun v : Joint ↦ π v.2.snd •
      (lam ^ o • normalizedField lam (uncurry (elapsedAmplitude W χout χsource β t)))
        (annularCarrierCoordinates v) := by
  funext v
  simp only [Function.uncurry, normalizedAnnularElapsedAmplitude,
    annularElapsedAmplitude, frequencyCutFullAmplitude,
    smul_smul, inv_mul_cancel₀ hlam, one_smul, zpow_neg, zpow_natCast, inv_inv]
  exact smul_comm (lam ^ o) (π v.2.snd) _

/-- Joint smoothness of the SAME annular amplitude includes both physical
positions and every carrier parameter, with the operator fixed
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem contDiff_normalizedAnnularElapsedAmplitude
    (W : TwoTimeAmplitude d q) (χout χsource β π : E → ℂ)
    (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (hπ : ContDiff ℝ ∞ π)
    (t : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (o : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (normalizedAnnularElapsedAmplitude (P := Par)
      W χout χsource β π t lam (-(o : ℤ)))) := by
  rw [normalizedAnnularElapsedAmplitude_eq_orderField W χout χsource β π t hlam o]
  have hA := contDiff_uncurry_elapsedAmplitude W χout χsource β hW ho hs hβ t
  have hn : ContDiff ℝ ∞
      (lam ^ o • normalizedField lam (uncurry (elapsedAmplitude W χout χsource β t))) :=
    (hA.comp (contDiff_fst.prodMk (contDiff_snd.const_smul lam))).const_smul (lam ^ o)
  exact (hπ.comp ((WithLp.sndL 2 ℝ E E).contDiff.comp contDiff_snd)).smul
    (hn.comp annularCarrierCoordinates.contDiff)

/-- The fixed mask cost precedes the original coefficients, frequency and
elapsed time. It uses precisely the retained dilated conic multiplier
(`app:ch_response:eq:direct-envelope-profile`). -/
def annularMaskConstant (K : Set Joint) (j : ℕ)
    (χout χsource : E → ℂ) (mask : E → ℝ) (threshold : ℝ) (π : E → ℂ) : ℝ :=
  ((j + 1 : ℝ) * 2 ^ j * cNorm K j (fun v : Joint ↦ π v.2.snd)) *
    amplitudeMaskConstant (annularCarrierCoordinates '' K) j χout χsource
      (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ))

/-- The CLOSED annular carrier retains both physical masks, the full original
multiplier at `lam*θ`, and the fixed annular selector. Thus derivatives cannot
lose a cutoff shoulder when applying the direct-envelope endpoint
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem tsupport_normalizedAnnularElapsedAmplitude_subset
    (W : TwoTimeAmplitude d q) (χout χsource β π : E → ℂ)
    (t : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (order : ℤ) :
    tsupport (Function.uncurry (normalizedAnnularElapsedAmplitude (P := Par)
      W χout χsource β π t lam order)) ⊆
      {v : Joint | v.1.1 ∈ tsupport χout ∧ v.2.fst ∈ tsupport χsource ∧
        lam • v.2.snd ∈ tsupport β ∧ v.2.snd ∈ tsupport π} := by
  apply closure_minimal
  · intro v hv
    change normalizedAnnularElapsedAmplitude W χout χsource β π t lam order
      v.1 (WithLp.toLp 2 (v.2.fst, v.2.snd)) ≠ 0 at hv
    rw [normalizedAnnularElapsedAmplitude_apply W χout χsource β π t hlam order] at hv
    refine ⟨subset_tsupport χout ?_, subset_tsupport χsource ?_,
      subset_tsupport β ?_, subset_tsupport π ?_⟩ <;>
      intro hz <;> exact hv (by simp [hz])
  · exact ((isClosed_tsupport χout).preimage continuous_fst.fst).inter
      (((isClosed_tsupport χsource).preimage
        ((WithLp.continuous_fst 2 E E).comp continuous_snd)).inter
        (((isClosed_tsupport β).preimage
          (((WithLp.continuous_snd 2 E E).comp continuous_snd).const_smul lam)).inter
          ((isClosed_tsupport π).preimage
            ((WithLp.continuous_snd 2 E E).comp continuous_snd))))

/-- All mask costs are nonnegative; this permits the later original
coefficient-profile substitution (`app:ch_response:eq:direct-envelope-profile`). -/
theorem annularMaskConstant_nonneg (K : Set Joint) (j : ℕ)
    (χout χsource : E → ℂ) (mask : E → ℝ) (threshold : ℝ) (π : E → ℂ) :
    0 ≤ annularMaskConstant K j χout χsource mask threshold π := by
  exact mul_nonneg (mul_nonneg (by positivity) (cNorm_nonneg _ _ _))
    (amplitudeMaskConstant_nonneg _ _ _ _ _)

/-- The original coefficient bound gives the joint normalized annular budget
on a CLOSED retained carrier. The elapsed-image inclusion and the multiplier
budget are proved from the retained chart and angular mask. There is no
frequency factor after normalizing either order zero or order minus one.

`hbudget` is the literal output of `UniformAmplitudes.ConicConstruction`;
for `W₀+W₁` use `UniformEvolution.solver_coefficient_bound` with `2*D`.
For the complete residual use its `j=2` output with `o=1`. The remaining
coefficient-to-`L` conversion and placement of the actual critical carrier
are obligations of the common-family construction
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem retained_normalized_annular_cNorm_le
    {K : Set Joint} (hK : IsCompact K)
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε ra rb : ℝ} (hε : 0 < ε)
    (hchart : ∀ v ∈ K, annularCarrierCoordinates v ∈ retainedGraphDomain ℓ z ε)
    (hband : ∀ v ∈ K, ℓ (spatialPart v.2.snd) ∈ Icc ra rb)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    {threshold : ℝ} (hthreshold : 1 ≤ threshold)
    (π : E → ℂ) (hπ : ContDiff ℝ ∞ π)
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1)) (D : ℕ → ℝ) (o j : ℕ)
    (hfinite : BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W)
    (hbudget : twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W ≤
      D j * (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B))
    {t lam : ℝ} (ht : t ∈ Icc 0 ε) (hlam : 1 ≤ lam) :
    cNorm K j (Function.uncurry (normalizedAnnularElapsedAmplitude (P := Par) W
      χout χsource (fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)) π t lam (-(o : ℤ)))) ≤
      annularMaskConstant K j χout χsource mask threshold π * D j *
        (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B) := by
  let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)
  let K' := annularCarrierCoordinates '' K
  let J := bufferedJetSet ℓ z ε ra rb
  let F := lam ^ o • normalizedField lam (uncurry (elapsedAmplitude W χout χsource β t))
  have hK' : IsCompact K' := hK.image annularCarrierCoordinates.continuous
  have hJ : IsCompact J := isCompact_bufferedJetSet ℓ z ε ra rb
  have hβ : ContDiff ℝ ∞ β :=
    Complex.ofRealCLM.contDiff.comp (contDiff_dilatedConicMask hm threshold)
  have hzero : ∀ v ∈ K', v.2 ≠ 0 := by
    rintro v ⟨w, hw, rfl⟩ he
    have hp := (hchart w hw).2.1
    change 0 < ℓ (spatialPart (annularCarrierCoordinates w).2) at hp
    have hz : spatialPart (annularCarrierCoordinates w).2 = 0 := by rw [he]; rfl
    rw [hz, map_zero] at hp
    exact lt_irrefl _ hp
  have hβbound : BoundedNormalizedSeminorm K' j (jointMultiplier β) :=
    boundedNormalizedSeminorm_dilatedConicMask hm hthreshold hK' hzero j
  have hmap : MapsTo (elapsedPoint t) K' J := by
    rintro v ⟨w, hw, rfl⟩
    exact retainedGraphDomain_elapsed_mem_bufferedJetSet ℓ z hε ht
      (hchart w hw) (hband w hw)
  have hWF : ContDiff ℝ ∞ (twoTimeOrderField o lam W) :=
    (hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul lam))).const_smul (lam ^ o)
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
  have helapsed := cNorm_elapsedOrderField_le hK' hJ isOpen_univ (subset_univ J)
    o j t lam hlam W χout χsource β ho hs hβ hβbound hWF.contDiffOn hmap
  have hsymbol := (cNorm_twoTimeOrderField_le hfinite hlam).trans hbudget
  rw [normalizedAnnularElapsedAmplitude_eq_orderField W χout χsource β π t
    (zero_lt_one.trans_le hlam).ne' o]
  refine hprod.trans ((mul_le_mul_of_nonneg_left
    (hpre.trans (helapsed.trans (mul_le_mul_of_nonneg_left hsymbol
      (amplitudeMaskConstant_nonneg _ _ _ _ _))))
        (mul_nonneg (by positivity) (cNorm_nonneg _ _ _))).trans_eq ?_)
  change _ = (_ * _) * _ * _
  ring

/-- Instantiate the annular jet calculation on the actual two retained
branches: the solver `W₀+W₁` has order zero and the complete residual `W₂=PW₁`
has order minus one. The correction's order-one seminorm is converted before
forming the solver sum, using the existing producer. The constants precede
`Q,B,lam,t`, and no extra derivative of either coefficient is used.

The bounds are on the literal normalized integrands, including all parameter
directions. This closes the amplitude-budget conversion for
`app:ch_response:eq:direct-envelope-profile`; constructing the common critical
carrier and substituting the original history grades remain separate.
-/
theorem retained_solver_residual_annular_jets
    {K : Set Joint} (hK : IsCompact K)
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε ra rb : ℝ} (hε : 0 < ε)
    (hchart : ∀ v ∈ K, annularCarrierCoordinates v ∈ retainedGraphDomain ℓ z ε)
    (hband : ∀ v ∈ K, ℓ (spatialPart v.2.snd) ∈ Icc ra rb)
    (W : Fin 3 → TwoTimeAmplitude d q)
    (hW : ∀ i, ContDiff ℝ ∞ (jointAmplitude (W i)))
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    {threshold : ℝ} (hthreshold : 1 ≤ threshold)
    (π : E → ℂ) (hπ : ContDiff ℝ ∞ π)
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1)) (D : ℕ → ℝ)
    (hbudget : ∀ i : Fin 3, ∀ j,
      BoundedTwoTimeOrderSeminorm (if i = 0 then 0 else 1)
        (bufferedJetSet ℓ z ε ra rb) j (W i) ∧
      twoTimeOrderSeminorm (if i = 0 then 0 else 1)
        (bufferedJetSet ℓ z ε ra rb) j (W i) ≤
          D j * (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B))
    {t lam : ℝ} (ht : t ∈ Icc 0 ε) (hlam : 1 ≤ lam) (j : ℕ) :
    let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)
    let cost := annularMaskConstant K j χout χsource mask threshold π * D j *
      (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B)
    (∀ v ∈ K, ‖iteratedFDeriv ℝ j (Function.uncurry
      (normalizedAnnularElapsedAmplitude (P := Par) (W 0 + W 1)
        χout χsource β π t lam 0)) v‖ ≤ 2 * cost) ∧
    (∀ v ∈ K, ‖iteratedFDeriv ℝ j (Function.uncurry
      (normalizedAnnularElapsedAmplitude (P := Par) (W 2)
        χout χsource β π t lam (-1))) v‖ ≤ cost) := by
  dsimp only
  let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)
  have hβ : ContDiff ℝ ∞ β :=
    Complex.ofRealCLM.contDiff.comp (contDiff_dilatedConicMask hm threshold)
  have hsum := solver_coefficient_bound KQ Q B (isCompact_bufferedJetSet ℓ z ε ra rb)
    (hW 0) (hW 1) D (by simpa using hbudget 0) (by simpa using hbudget 1) j
  have hsmooth : ContDiff ℝ ∞ (jointAmplitude (W 0 + W 1)) := (hW 0).add (hW 1)
  have hsumBound := retained_normalized_annular_cNorm_le hK ℓ z hε hchart hband
    (W 0 + W 1) hsmooth χout χsource ho hs mask hm hthreshold π hπ KQ Q B
    (fun k ↦ 2 * D k) 0 j hsum.1 hsum.2 ht hlam
  have hresidual := hbudget 2 j
  simp only [show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte] at hresidual
  have hresBound := retained_normalized_annular_cNorm_le hK ℓ z hε hchart hband
    (W 2) (hW 2) χout χsource ho hs mask hm hthreshold π hπ KQ Q B
    D 1 j hresidual.1 hresidual.2 ht hlam
  have hLam := (zero_lt_one.trans_le hlam).ne'
  have hsumSmooth := contDiff_normalizedAnnularElapsedAmplitude (p := p)
    (W 0 + W 1) χout χsource β π hsmooth ho hs hβ hπ t hLam 0
  have hresSmooth := contDiff_normalizedAnnularElapsedAmplitude (p := p)
    (W 2) χout χsource β π (hW 2) ho hs hβ hπ t hLam 1
  constructor
  · intro v hv
    exact ((norm_iteratedFDeriv_le_cNorm hK (hsumSmooth.of_le (by simp)) hv le_rfl).trans
      hsumBound).trans_eq (by ring)
  · intro v hv
    exact (norm_iteratedFDeriv_le_cNorm hK (hresSmooth.of_le (by simp)) hv le_rfl).trans hresBound

end JanetCartan.ResponseTransfer.RetainedFactors
