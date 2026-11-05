module

public import JanetCartan.Analysis.Microlocal.EllipticResponseProfiles.FirstJet

/-!
# Reserve profiles of the full inverse on the original determinant gap

The compact coefficient first-jet domain is the same as in
`EllipticLocalization.CoefficientProfiles`. Retaining its reserve supplies the
full-source response estimate (`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticResponseProfiles
open ActualCarriers
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "Jet" => Coeff × ((E →L[ℝ] Coeff) × Mat)

open FiniteMasks.ActualFamily EllipticComplement EllipticLocalization
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The actual full inverse and complete physical coefficient action have
joint profiles on the normalized closed source support. Only original
coefficient profiles enter; their reserve absorbs the first derivative.
The bound retains reserve `Rstar - 1`. Constants precede the varying fields, history scale and frequency
(`app:ch_regular:eq:initial-coefficient-profile`, `high-amplitude`). -/
theorem exists_coefficientElliptic_joint_reserve_profiles
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (J : Set E) (hJ : IsCompact J) (hzero : (0 : E) ∉ J)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (_hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ threshold ρ : ℝ, 0 < threshold → 0 < ρ →
      ∀ v : E × E, v.1 ∈ closedBall x RQ → v.2 ∈ J →
        v.2 ∈ tsupport (fun ξ ↦ (ellipticSourceMask f hK threshold (ρ • ξ) : ℂ)) →
      ∀ (residual : Bool) (k : ℕ),
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦
          if residual then coefficientEllipticPhysicalAction
            ((Q w.1, (fderiv ℝ Q w.1, B w.1)), w.2)
          else coefficientEllipticInverse (Q w.1, w.2)) v‖ ≤ C k * L ^ (k-(Rstar-1)) := by
  let A k := max (AQ k) (AB k)
  have hA k : 0 ≤ A k := (hAQ k).trans (le_max_left _ _)
  let S : Set (Jet × E) :=
    ((closedBall A₀ f.coefficientRadius ×ˢ
      (closedBall (0 : E →L[ℝ] Coeff) (A 1) ×ˢ closedBall (0 : Mat) (A 0))) ×ˢ J) ∩
      {v | f.determinantGap / 2 * ‖v.2‖ ^ (d+1) ≤ |determinant v.1.1 v.2|}
  have hS : IsCompact S :=
    (((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
      (isCompact_closedBall _ _))).prod hJ).inter_right
        (isClosed_le (continuous_const.mul (continuous_snd.norm.pow _))
          (contDiff_determinant.continuous.comp (continuous_fst.fst.prodMk continuous_snd)).abs)
  have hgap v (hv : v ∈ S) : determinant v.1.1 v.2 ≠ 0 := by
    apply abs_pos.mp
    apply lt_of_lt_of_le _ hv.2
    exact mul_pos (half_pos f.determinantGap_pos)
      (pow_pos (norm_pos_iff.mpr (fun he ↦ hzero (he ▸ hv.1.2))) _)
  let G : Bool → Jet × E → CMat := fun residual v ↦
    if residual then coefficientEllipticPhysicalAction v else coefficientEllipticInverse (v.1.1, v.2)
  have hs residual v (hv : v ∈ S) : ContDiffAt ℝ ∞ (G residual) v := by
    cases residual
    · exact (contDiffAt_coefficientEllipticInverse (p := (v.1.1, v.2)) (hgap v hv)).comp v
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    · exact contDiffAt_coefficientEllipticPhysicalAction (hgap v hv)
  choose D hD hb using fun residual ↦ exists_coefficientFirstJet_reserve_profile
    (G residual) hS (hs residual) A hA
  refine ⟨fun k ↦ D false k + D true k, fun k ↦ add_nonneg (hD false k) (hD true k), ?_⟩
  intro Rstar hR L hL Q B hQ hB hmap hQp hBp threshold ρ ht hρ v hv hJv hβ residual k
  have hQp' j : cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j-Rstar) :=
    (hQp j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (zero_le_one.trans hL) _))
  have hBp' j : cNorm (closedBall x RQ) j B ≤ A j * L ^ (j-Rstar) :=
    (hBp j).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (pow_nonneg (zero_le_one.trans hL) _))
  have hdf : ‖fderiv ℝ Q v.1‖ ≤ A 1 := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x RQ)
      (fun y hy ↦ (hQ.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
        (show (1 : ℕ∞ω) ≤ ∞ by simp)) hv (le_refl 1)
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans (by simpa only [Nat.sub_eq_zero_of_le hR, pow_zero, mul_one] using hQp' 1)
  have hBv : ‖B v.1‖ ≤ A 0 := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x RQ)
      (fun y hy ↦ (hB.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
        (show (0 : ℕ∞ω) ≤ ∞ by simp)) hv (le_refl 0)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh.trans (by simpa only [Nat.zero_sub, pow_zero, mul_one] using hBp' 0)
  have hmem : ((Q v.1, (fderiv ℝ Q v.1, B v.1)), v.2) ∈ S := by
    refine ⟨⟨⟨hmap (hball hv), ?_, ?_⟩, hJv⟩,
      (determinant_gap_on_normalized_elliptic_support f hK ht hρ (hmap (hball hv)) hβ).le⟩
    · simpa only [mem_closedBall, dist_zero_right] using hdf
    · simpa only [mem_closedBall, dist_zero_right] using hBv
  have hh := hb residual Rstar hR L hL x RQ Ω hΩ hball Q B hQ hB hQp' hBp' v hv hmem k
  have hsum : D residual k ≤ D false k + D true k := by
    cases residual
    · exact le_add_of_nonneg_right (hD true k)
    · exact le_add_of_nonneg_left (hD false k)
  exact (show _ ≤ D residual k * L^(k-(Rstar-1)) by simpa only [G] using hh).trans
    (mul_le_mul_of_nonneg_right hsum (pow_nonneg (zero_le_one.trans hL) _))


end JanetCartan.RegularSector.EllipticResponseProfiles
