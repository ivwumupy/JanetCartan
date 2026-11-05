module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.Elapsed
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Assembly.CompactJets

/-!
# Original-phase bounds for the smooth representative

The constants below contain only fixed cutoffs and the fixed normalization
map. They precede the varying chart phase. Germ agreement also transfers
every supported jet with derivative loss zero. The original phase producer
then incurs precisely its existing one-derivative coefficient reserve.
Consumer: phase profiles in `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
open RegularSector.Characteristic ConicPhase EvolutionIntegral
variable {d : ℕ}
local notation "T" => TwoTimePoint (Euclidean d)

/-- The finite-order multiplication cost contains the fixed localizer, not
the chart phase (`app:ch_response:eq:direct-envelope-profile`). -/
def localizationCost (χ : T → ℝ) (J : Set T) (n : ℕ) : ℝ :=
  1 + (∑ j ∈ Finset.range (n + 1), ‖ContinuousLinearMap.mul ℝ ℝ‖ *
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * cNorm J n χ

/-- Positivity of the explicit localization cost (`app:ch_response:eq:direct-envelope-profile`). -/
theorem localizationCost_pos (χ : T → ℝ) (J : Set T) (n : ℕ) :
    0 < localizationCost χ J n := by
  unfold localizationCost
  have := cNorm_nonneg J n χ
  positivity

/-- Quantitative localization from the original phase jets at the SAME order.
Smoothness is used to justify the derivative formula, not as a substitute for
a uniform bound (`app:ch_response:eq:direct-envelope-profile`). -/
theorem cNorm_localizedPhase_le {χ F : T → ℝ} {J U : Set T}
    (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiffOn ℝ ∞ F U) (n : ℕ) :
    cNorm J n (localizedPhase χ F) ≤ localizationCost χ J n * cNorm J n F := by
  apply (FullPhaseCharts.InverseEstimates.cNorm_bilinear_le_on
    (ContinuousLinearMap.mul ℝ ℝ) hJ hU hJU hχ.contDiffOn hF n).trans
  unfold localizationCost
  nlinarith [cNorm_nonneg J n F]

/-- All jets of the representative on the required conic buffer are literally
the original conic jets (`app:ch_response:eq:direct-envelope-profile`). -/
theorem iteratedFDeriv_representative_eq_phase
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ q ∈ K, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    {p : T} (hp : p ∈ domain ℓ K) (hfreq : δ ≤ ‖p.2.2.2‖) (n : ℕ) :
    iteratedFDeriv ℝ n (representative ℓ δ hδ χ (twoTimePhase C)) p =
      iteratedFDeriv ℝ n (phase ℓ C) p :=
  ((representative_eventuallyEq_phase ℓ C hδ he hp hfreq).iteratedFDeriv ℝ n).eq_of_nhds

/-- A quantitative supported-jet bound using ONLY original chart jets and
fixed normalization geometry, with derivative shift zero. The compact set
`J` includes the full segments needed by the consumer, and its image lies in
the common normalized buffer `K` (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_representative_le
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K J : Set T}
    (he : ∀ q ∈ K, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    (hK : IsCompact K) (hKC : K ⊆ C.target) (hJ : IsCompact J)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hpos : ∀ p ∈ J, 0 < ℓ p.2.2.2) (hmap : MapsTo (normalize ℓ) J K)
    {n k : ℕ} (hk : k ≤ n) {p : T} (hp : p ∈ J) (hfreq : δ ≤ ‖p.2.2.2‖) :
    ‖iteratedFDeriv ℝ k (representative ℓ δ hδ χ (twoTimePhase C)) p‖ ≤
      jetBoundConstant ℓ J n * cNorm K n (twoTimePhase C) := by
  rw [iteratedFDeriv_representative_eq_phase ℓ C hδ he
    ⟨hpos p hp, hmap hp⟩ hfreq k]
  exact norm_iteratedFDeriv_extend_le ℓ hJ hK C.open_target hKC hpos hmap hC hk hp

/-- The full supported seminorm has the same zero-loss bound, with constants
fixed independently of the original phase (`app:ch_response:eq:direct-envelope-profile`). -/
theorem cNorm_representative_le
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K J : Set T}
    (he : ∀ q ∈ K, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    (hK : IsCompact K) (hKC : K ⊆ C.target) (hJ : IsCompact J)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hpos : ∀ p ∈ J, 0 < ℓ p.2.2.2) (hmap : MapsTo (normalize ℓ) J K)
    (hfreq : ∀ p ∈ J, δ ≤ ‖p.2.2.2‖) (n : ℕ) :
    cNorm J n (representative ℓ δ hδ χ (twoTimePhase C)) ≤
      jetBoundConstant ℓ J n * cNorm K n (twoTimePhase C) := by
  have heq : cNorm J n (representative ℓ δ hδ χ (twoTimePhase C)) =
      cNorm J n (phase ℓ C) := by
    unfold cNorm
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    apply Set.image_congr
    intro p hp
    rw [iteratedFDeriv_representative_eq_phase ℓ C hδ he
      ⟨hpos p hp, hmap hp⟩ (hfreq p hp) k]
  rw [heq]
  exact cNorm_extend_le ℓ hJ hK C.open_target hKC hpos hmap hC n

end JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
