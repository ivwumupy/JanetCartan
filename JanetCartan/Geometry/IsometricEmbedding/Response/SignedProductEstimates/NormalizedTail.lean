module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedFourier
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedAdjoint
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Multiplier

/-!
# Actual normalized angular discrepancy of each complete signed source

Apply the original protected signed-source estimate to the actual corrected
characteristic-plus-elliptic Fourier complement. Its geometric buffer comes
from the same family's proved plateau, and both original output masks remain
in the resulting discrepancy. No analytic residual estimate is a premise.
Consumer: `app:ch_pairs:eq:pairs-lag-one-error`, source contribution.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open ResponseTransfer ResponseTransfer.Complement.InactiveSource ResponseTransfer.SourceNegative
open Sampling.BackgroundModulation Pseudodifferential
variable {d N : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)

/-- The original complete cutoff source is genuinely integrable and in L².
Only local smoothness on its original support buffer is used
(`app:ch_pairs:prop:pairs-lag-sum`, Step 1). -/
private theorem complete_modulated_source_admission {S U : Set E}
    (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (χ φ : E → ℝ) (a : E → V) (ρ : ℝ)
    (hχ : ContDiffOn ℝ ∞ χ U) (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport χ ⊆ S) :
    Integrable (modulatedSource χ φ a ρ) volume ∧ MemLp (modulatedSource χ φ a ρ) 2 volume := by
  have hsupport : tsupport (fun y ↦ χ y • a y) ⊆ S := (tsupport_smul_subset_left χ a).trans hs
  have hc : HasCompactSupport (fun y ↦ χ y • a y) :=
    hS.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hdiff := contDiff_carrier_source hU ρ φ (fun y ↦ χ y • a y) hφ
    (hχ.smul ha) (hsupport.trans hSU)
  have he : (fun y ↦ carrier ρ φ y • (χ y • a y)) = modulatedSource χ φ a ρ := by
    funext y; exact smul_comm _ _ _
  rw [he] at hdiff
  have hcompact : HasCompactSupport (modulatedSource χ φ a ρ) := by
    exact hS.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_smul_subset_left χ (fun y ↦ carrier ρ φ y • a y)).trans hs)
  exact ⟨hdiff.continuous.integrable_of_hasCompactSupport hcompact,
    hdiff.continuous.memLp_of_hasCompactSupport hcompact⟩

/-- The same physical masks preserve Sobolev bounds of the actual complete
Fourier complement, forward and for the literal adjoint
(`app:ch_regular:eq:resolved-angular-tail`). -/
private theorem exists_normalized_discrepancy_mask_bound
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K)
    (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H,
      (∀ᵐ y ∂volume, u y ≠ 0 → y ∈ closedBall center f.physicalRadius) →
      (∀ᵐ y ∂volume, u y ≠ 0 → output y = 1) →
      MemVectorFourierSobolev (s : ℝ) (complementFourierOperator f hK L₀ u) →
      let v := (pairedSource f hK L₀ output ho.continuous hob - 1) u
      let w := ((pairedSource f hK L₀ output ho.continuous hob).adjoint - 1) u
      (MemVectorFourierSobolev (s : ℝ) v ∧ vectorFourierSobolevNorm (s : ℝ) v ≤
        C * vectorFourierSobolevNorm (s : ℝ) (complementFourierOperator f hK L₀ u)) ∧
      (MemVectorFourierSobolev (s : ℝ) w ∧ vectorFourierSobolevNorm (s : ℝ) w ≤
        C * vectorFourierSobolevNorm (s : ℝ) (complementFourierOperator f hK L₀ u)) := by
  obtain ⟨Co, hCo, hout⟩ := exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) output ho hoc hob s
  obtain ⟨Cf, hCf, hfixed⟩ := exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) f.outputMask f.outputMask_smooth f.outputMask_compact
    (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2) s
  obtain ⟨Ci, hCi, hinput⟩ := exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) f.inputMask f.inputMask_smooth f.inputMask_compact
    (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2) s
  refine ⟨Co*Cf+Ci, by positivity, ?_⟩
  intro u hs hp hc v w
  have hf := pairedSource_sub_identity_eq_complement f hK hL₀ output ho.continuous hob u hs hp
  have ha := normalizedSource_adjoint_sub_identity_eq_complement f hK hL₀ output ho.continuous hob u hs hp
  obtain ⟨hfm, hfn⟩ := hfixed _ hc
  obtain ⟨hom, hon⟩ := hout _ hfm
  obtain ⟨him, hin⟩ := hinput _ hc
  have hfnn := TerminalBounds.neg_bound hom
  have hann := TerminalBounds.neg_bound him
  change MemVectorFourierSobolev (s : ℝ) (-_) ∧ _ at hfnn hann
  rw [← hf] at hfnn
  rw [← ha] at hann
  refine ⟨⟨hfnn.1, ?_⟩, ⟨hann.1, ?_⟩⟩
  · change vectorFourierSobolevNorm (s : ℝ) ((pairedSource f hK L₀ output ho.continuous hob - 1) u) ≤ _
    rw [hfnn.2]
    calc
      _ ≤ Co * (Cf * vectorFourierSobolevNorm (s : ℝ) (complementFourierOperator f hK L₀ u)) :=
        hon.trans (mul_le_mul_of_nonneg_left hfn hCo)
      _ ≤ (Co*Cf+Ci) * vectorFourierSobolevNorm (s : ℝ) (complementFourierOperator f hK L₀ u) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCi) (by unfold vectorFourierSobolevNorm matrixFourierSobolevNorm; positivity)
  · change vectorFourierSobolevNorm (s : ℝ) (((pairedSource f hK L₀ output ho.continuous hob).adjoint - 1) u) ≤ _
    rw [hann.2]
    exact hin.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hCo hCf))
      (by unfold vectorFourierSobolevNorm matrixFourierSobolevNorm; positivity))

/-- The actual normalized angular source discrepancy has arbitrary original
stage decay for BOTH complete reduced tensor amplitudes, forward and for the
literal adjoint, at every positive or negative order below the fixed requested order. Constants precede all phases,
samples, targets and histories; the stage threshold also precedes accuracy.
The terminal inclusion `T ⊆ K` is the original fixed-response-radius producer's
geometric obligation. No plateau, full gap, desired tail or response bound is
assumed (`app:ch_pairs:prop:pairs-lag-sum`, Steps 1–3). -/
theorem exists_normalized_signed_source_discrepancy_constants
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K)
    (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    {T : Set E} (hT : IsCompact T) (hTK : T ⊆ K) (hTneg : ∀ v ∈ T, -v ∈ T)
    {S : Set E} (hS : IsCompact S) (hScore : S ⊆ closedBall center f.physicalRadius)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hop : ∀ y ∈ S, output y = 1)
    {a G cbeat : ℝ} (ha : 0 < a) (hG : 0 < G) (hbeat : 0 < cbeat)
    (Cscale : ℝ) (P X Y CQ C : ℕ → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r) (s : ℕ) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ q : ℕ, ∃ D : ℝ, 0 ≤ D ∧
      ∀ (U : Set E), IsOpen U → S ⊆ U →
      ∀ (χ ψ φ : E → ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1))
        (A B : E → Matrix (Fin N) (Fin (d+1)) ℂ) (R L ρ : ℝ),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ φ U → ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      tsupport χ ⊆ S → 1 ≤ L → Rmin ≤ R →
      cbeat * (R ^ carrierExponent * R ^ (-separationExponent)) ≤ ρ →
      L ≤ Cscale * R ^ (1+meanSlack) →
      (∀ y ∈ U, a ≤ ‖fderiv ℝ φ y‖ ∧ ‖fderiv ℝ φ y‖ ≤ G) →
      (∀ y ∈ U, NormedSpace.normalize (fderiv ℝ φ y) ∈ (InnerProductSpace.toDual ℝ E) '' T) →
      (∀ y ∈ S, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ (r+1) φ y‖ ≤ P r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ y‖ ≤ X r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r ψ y‖ ≤ Y r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q y‖ ≤ CQ r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A y‖ ≤ C r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B y‖ ≤ C r * L^r) →
      let estimate := fun g : E → V ↦ ∃ hg : MemLp g 2 volume, ∀ t : ℝ, t ≤ s →
        let v := (pairedSource f hK L₀ output ho.continuous hob - 1) (hg.toLp g)
        let w := ((pairedSource f hK L₀ output ho.continuous hob).adjoint - 1) (hg.toLp g)
        (MemVectorFourierSobolev t v ∧ vectorFourierSobolevNorm t v ≤
          D * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹) ∧
        (MemVectorFourierSobolev t w ∧ vectorFourierSobolevNorm t w ≤
          D * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹)
      estimate (modulatedSource χ φ (fun y ↦ ψ y • ((1/2 : ℝ) •
        complexStressContraction (Q y) (symmetricBilinearTensor (A y) (B y)))) ρ) ∧
      estimate (modulatedSource χ φ (fun y ↦ ψ y • ((1/2 : ℝ) •
        complexStressContraction (Q y) (symmetricBilinearTensor (A y) ((B y).map conj)))) ρ) := by
  obtain ⟨δ, hδ, hbuffer⟩ := exists_normalizedComplement_angular_buffer f hK hT hTK hTneg
  obtain ⟨Rtail, hRtail, htail⟩ := exists_reduced_signed_protected_source_stage_constants
    (N := N) hS ha hG hδ hbeat 1 Cscale zero_le_one P X Y CQ C hP hX hY hCQ hC
    (Nat.cast_nonneg s)
  obtain ⟨Rrad, _, hrad⟩ := exists_normalizedComplement_radial_threshold hbeat ha L₀
  obtain ⟨Cphys, hCphys, hphysical⟩ := exists_normalized_discrepancy_mask_bound
    f hK L₀ hL₀ output ho hoc hob s
  refine ⟨max Rtail Rrad, hRtail.trans (le_max_left _ _), fun q ↦ ?_⟩
  obtain ⟨D, hD, hsource⟩ := htail q
  refine ⟨Cphys * (d+1 : ℝ) * D, by positivity, ?_⟩
  intro U hU hSU χ ψ φ Q A B R L ρ hχ hψ hQ hφ hA hB hχS hL hR hρ hslow
    hband hprotected hphase hχb hψb hQb hAb hBb
  let mask := normalizedComplementBoundedMask f hK L₀
  have hangular : ∀ η, mask.symbol η ≠ 0 → a*ρ/2 ≤ ‖η‖ → ‖η‖ ≤ 2*G*ρ →
      ∀ v ∈ (InnerProductSpace.toDual ℝ E) '' T,
        δ ≤ dist v (NormedSpace.normalize (InnerProductSpace.toDual ℝ E η)) := by
    intro η hη hlo _ v hv
    obtain ⟨w, hw, rfl⟩ := hv
    have hb := hbuffer L₀ (by linarith [f.radialThreshold_ge_one]) η hη
      ((hrad R ((le_max_right _ _).trans hR) ρ hρ).trans hlo) w hw
    have hn : NormedSpace.normalize (InnerProductSpace.toDual ℝ E η) =
        InnerProductSpace.toDual ℝ E (NormedSpace.normalize η) := by
      simp [NormedSpace.normalize]
    simpa only [hn, LinearIsometryEquiv.dist_map] using hb
  obtain ⟨hp, hm⟩ := hsource U hU hSU ((InnerProductSpace.toDual ℝ E) '' T) χ ψ φ Q A B R L ρ mask
    hχ hψ hQ hφ hA hB hχS hL ((le_max_left _ _).trans hR) le_rfl hρ hslow hband
    hprotected hangular hphase hχb hψb hQb hAb hBb
  obtain ⟨hpa, hma⟩ := contDiffOn_reduced_signed_amplitudes hQ hψ hA hB
  have hfull (b : E → V) (hb : ContDiffOn ℝ ∞ b U)
      (htail :
        let Hf := fun η ↦ mask.symbol η • JanetCartan.Localization.physicalFourierIntegral volume
          (modulatedSource χ φ b ρ) (InnerProductSpace.toDual ℝ E η)
        Integrable (fun η ↦ (1+‖η‖^2)^(s : ℝ)*‖Hf η‖^2) ∧
          JanetCartan.Localization.fourierWeightedL2Norm volume (s : ℝ) Hf ≤
            D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) :
      ∃ hg : MemLp (modulatedSource χ φ b ρ) 2 volume, ∀ t : ℝ, t ≤ s →
        let v := (pairedSource f hK L₀ output ho.continuous hob - 1)
          (hg.toLp (modulatedSource χ φ b ρ))
        let w := ((pairedSource f hK L₀ output ho.continuous hob).adjoint - 1)
          (hg.toLp (modulatedSource χ φ b ρ))
        (MemVectorFourierSobolev t v ∧ vectorFourierSobolevNorm t v ≤
          (Cphys * (d+1 : ℝ) * D) * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) ∧
        (MemVectorFourierSobolev t w ∧ vectorFourierSobolevNorm t w ≤
          (Cphys * (d+1 : ℝ) * D) * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) := by
    obtain ⟨hi, hg⟩ := complete_modulated_source_admission hS hU hSU χ φ b ρ hχ hφ hb hχS
    have hsupp : ∀ᵐ y ∂volume, hg.toLp (modulatedSource χ φ b ρ) y ≠ 0 → y ∈ S := by
      filter_upwards [hg.coeFn_toLp] with y hy hne
      apply hχS (subset_tsupport χ ?_)
      intro hz
      exact hne (by rw [hy]; simp only [modulatedSource, hz, zero_smul])
    obtain ⟨hcm, hcn⟩ := normalizedComplementFourier_sobolev_le_physical_energy f hK L₀ _ hi hg
      (Nat.cast_nonneg s) htail.1
    obtain ⟨hf, ha⟩ := hphysical (hg.toLp _)
      (by filter_upwards [hsupp] with y hy hn; exact hScore (hy hn))
      (by filter_upwards [hsupp] with y hy hn; exact hop y (hy hn)) hcm
    have hbound : Cphys * vectorFourierSobolevNorm (s : ℝ)
        (complementFourierOperator f hK L₀ (hg.toLp _)) ≤
        (Cphys * (d+1 : ℝ) * D) * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹ := by
      exact (mul_le_mul_of_nonneg_left
        (hcn.trans (mul_le_mul_of_nonneg_left htail.2 (by positivity))) hCphys).trans_eq (by ring)
    exact ⟨hg, fun t ht ↦
      ⟨⟨fun i ↦ (hf.1 i).mono ht,
        (ResponseTransfer.Complement.vectorFourierSobolevNorm_mono hf.1 ht).trans (hf.2.trans hbound)⟩,
       ⟨fun i ↦ (ha.1 i).mono ht,
        (ResponseTransfer.Complement.vectorFourierSobolevNorm_mono ha.1 ht).trans (ha.2.trans hbound)⟩⟩⟩
  exact ⟨hfull _ hpa hp, hfull _ hma hm⟩

end JanetCartan.SignedProductEstimates
