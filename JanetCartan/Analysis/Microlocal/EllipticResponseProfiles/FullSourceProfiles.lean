module

public import JanetCartan.Analysis.Microlocal.EllipticResponseProfiles.AmplitudeProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AdjointProfiles

/-!
# Full-source elliptic profiles in the response consumer's normalization

The inverse and residual amplitudes are multiplied by the same radial scale.
Their jets have the exact natural-subtraction reserve used by the near-carrier
full-source envelope producer. Both original physical masks remain in place;
the exchanged literal adjoint is also controlled on the same frequency set.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticResponseProfiles
open FiniteMasks.ActualFamily EllipticComplement
open ArbitraryAccuracy.ResidualLocalization FourierIntegral ResponseTransfer
open ResponseTransfer.NearCarrierAssembly ResponseTransfer.NearCarrierFullLow
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- The exact reserve-two profile consumed by
`hasEnvelopeProfile_fixedSelectorGraph_parameterDerivatives_of_raw_profiles`.
It applies to the actual full inverse and complete residual, and keeps the
same source covector, physical masks and doubled radial collar. The original
history producer may instantiate `Q`, `B`, `L`, `AQ`, and `AB` directly; no
mixed-symbol profile is assumed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_elliptic_full_source_profiles
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (threshold : ℝ) (ht : 1 ≤ threshold)
    (J : Set E) (hJ : IsCompact J) (hzero : (0 : E) ∉ J)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 2 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ (residual backward : Bool),
        let A := ρ • orientedMaskedPDOAmplitude backward χout (χs)
          (if residual then ellipticResidualSymbol f hK threshold Q B
            else ellipticInverseSymbol f hK threshold Q)
        ContDiff ℝ ∞ (normalizedFullAmplitude A ρ) ∧
        (∀ (k : ℕ) (v : V), v.2.2 ∈ J →
          ‖iteratedFDeriv ℝ k (normalizedFullAmplitude A ρ) v‖ ≤
            C k * L ^ (k-(Rstar-2))) ∧
        ContDiff ℝ ∞ (normalizedFullAmplitude (exchangedAdjointAmplitude A) ρ) ∧
        (∀ (k : ℕ) (v : V), v.2.2 ∈ J →
          ‖iteratedFDeriv ℝ k (normalizedFullAmplitude (exchangedAdjointAmplitude A) ρ) v‖ ≤
            C k * L ^ (k-(Rstar-2))) := by
  obtain ⟨C, hC, hprofile⟩ := exists_normalized_elliptic_amplitude_reserve_profiles f hK
    hΩ hball χout ho hoc hos threshold ht J hJ hzero AQ AB hAQ hAB
  refine ⟨C, hC, ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hmap hQp hBp residual backward A
  let a := orientedMaskedPDOAmplitude backward χout (χs)
    (if residual then ellipticResidualSymbol f hK threshold Q B
      else ellipticInverseSymbol f hK threshold Q)
  have hρp : 0 < ρ := zero_lt_one.trans_le hρ
  have ha : ContDiff ℝ ∞ (normalizedFullAmplitude a ρ) :=
    contDiff_normalized_elliptic_amplitude f hK hΩ χout ho
      (zero_lt_one.trans_le ht) ρ Q B hQ hB hmap residual backward
  have hA : ContDiff ℝ ∞ (normalizedFullAmplitude A ρ) := ha.const_smul ρ
  have hb (k : ℕ) (v : V) (hv : v.2.2 ∈ J) :
      ‖iteratedFDeriv ℝ k (normalizedFullAmplitude A ρ) v‖ ≤
        C k * L ^ (k-(Rstar-2)) := by
    have hh := hprofile Rstar (by omega) L ρ hL hρ Q B hQ hB hmap hQp hBp
      residual backward k v hv
    change ‖iteratedFDeriv ℝ k (ρ • normalizedFullAmplitude a ρ) v‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (ha.contDiffAt.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)),
      norm_smul, Real.norm_eq_abs, abs_of_pos hρp]
    calc
      _ ≤ ρ * (ρ ^ (-1 : ℝ) * C k * L ^ (k-(Rstar-1))) :=
        mul_le_mul_of_nonneg_left hh hρp.le
      _ = C k * L ^ (k-(Rstar-1)) := by
        rw [Real.rpow_neg_one]
        field_simp [hρp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by omega : k-(Rstar-1) ≤ k-(Rstar-2))) (hC k)
  refine ⟨hA, hb, ?_, ?_⟩
  · change ContDiff ℝ ∞ (fun v : V ↦
      ((normalizedFullAmplitude A ρ) (fullAmplitudePositionSwap v)).conjTranspose)
    exact (Matrix.conjTransposeLinearEquiv (Fin (d+1)) (Fin (d+1)) ℝ ℂ).toContinuousLinearEquiv.contDiff.comp (hA.comp fullAmplitudePositionSwap.contDiff)
  · intro k v hv
    rw [norm_jet_normalizedFullAmplitude_exchangedAdjoint]
    exact hb k (v.2.1, v.1, v.2.2) hv

end JanetCartan.RegularSector.EllipticResponseProfiles
