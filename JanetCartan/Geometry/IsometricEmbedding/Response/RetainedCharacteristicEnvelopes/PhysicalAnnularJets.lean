module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AmplitudeJets
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCutoff.Multiplier

/-!
# Annular jets with the original doubled physical multiplier

The selected characteristic operators use the physical cutoff at `2*threshold`
inside the original coordinate permutation. Its bump need not be rotation
invariant. Apply its proved normalized multiplier seminorm directly, keeping
both physical masks and the entire annular selector literal.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open FourierIntegral PrimitiveProfiles FullAmplitudePrimitiveBudget.Local
open RegularSector.Characteristic UniformEvolution ResidualCoordinates
open EvolutionIntegral SymbolBudgets RegularSector.FiniteMasks ConicPhase
open DirectEvolution AnnularSobolev RetainedFactors
variable {d q p : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean p
local notation "Joint" => (E × Par) × CarrierVariables (d+1)

/-- Fixed mask cost for the original doubled physical collar in
`app:ch_response:eq:direct-envelope-profile`. Neither radial shoulder is
replaced by a canonical cutoff. -/
def physicalAnnularMaskConstant (K : Set Joint) (j : ℕ)
    (χout χsource : E → ℂ) (mask : E → ℝ) (index : Fin (d+1))
    (threshold : ℝ) (π : E → ℂ) : ℝ :=
  ((j + 1 : ℝ) * 2 ^ j * cNorm K j (fun v : Joint ↦ π v.2.snd)) *
    amplitudeMaskConstant (annularCarrierCoordinates '' K) j χout χsource
      (fun ξ ↦ (dilatedConicMask mask (2*threshold) (physicalCoordinates index ξ) : ℂ))

/-- Nonnegativity of the literal-mask cost used in the admitted-history
substitution for `app:ch_response:eq:direct-envelope-profile`. -/
theorem physicalAnnularMaskConstant_nonneg (K : Set Joint) (j : ℕ)
    (χout χsource : E → ℂ) (mask : E → ℝ) (index : Fin (d+1))
    (threshold : ℝ) (π : E → ℂ) :
    0 ≤ physicalAnnularMaskConstant K j χout χsource mask index threshold π := by
  exact mul_nonneg (mul_nonneg (by positivity) (cNorm_nonneg _ _ _))
    (amplitudeMaskConstant_nonneg _ _ _ _ _)

/-- The selected original symbol seminorm gives the normalized annular jet
budget with the SAME physical radial cutoff at `2*threshold`. The normalized
multiplier budget is derived by
`PhysicalCutoff.boundedNormalizedSeminorm_physical_dilatedConicMask`; it is
not an assumed envelope field. Consumer: the selected admitted-history
amplitude application in `app:ch_response:eq:direct-envelope-profile`. -/
theorem retained_physical_normalized_annular_cNorm_le
    {K : Set Joint} (hK : IsCompact K)
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε ra rb : ℝ} (hε : 0 < ε)
    (hchart : ∀ v ∈ K, annularCarrierCoordinates v ∈ retainedGraphDomain ℓ z ε)
    (hband : ∀ v ∈ K, ℓ (spatialPart v.2.snd) ∈ Icc ra rb)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask) (index : Fin (d+1))
    {threshold : ℝ} (hthreshold : 1 ≤ threshold)
    (π : E → ℂ) (hπ : ContDiff ℝ ∞ π)
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1)) (D : ℕ → ℝ) (o j : ℕ)
    (hfinite : BoundedTwoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W)
    (hbudget : twoTimeOrderSeminorm o (bufferedJetSet ℓ z ε ra rb) j W ≤
      D j * (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B))
    {t lam : ℝ} (ht : t ∈ Icc 0 ε) (hlam : 1 ≤ lam) :
    cNorm K j (Function.uncurry (normalizedAnnularElapsedAmplitude (P := Par) W
      χout χsource (fun ξ ↦ (dilatedConicMask mask (2*threshold) (physicalCoordinates index ξ) : ℂ)) π t lam (-(o : ℤ)))) ≤
      physicalAnnularMaskConstant K j χout χsource mask index threshold π * D j *
        (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B) := by
  let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask (2*threshold) (physicalCoordinates index ξ) : ℂ)
  let K' := annularCarrierCoordinates '' K
  let J := bufferedJetSet ℓ z ε ra rb
  let F := lam ^ o • normalizedField lam (uncurry (elapsedAmplitude W χout χsource β t))
  have hK' : IsCompact K' := hK.image annularCarrierCoordinates.continuous
  have hJ : IsCompact J := isCompact_bufferedJetSet ℓ z ε ra rb
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


end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
