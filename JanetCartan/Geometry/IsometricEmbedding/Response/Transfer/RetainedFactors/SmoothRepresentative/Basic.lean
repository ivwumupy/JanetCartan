module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.ContinuousExtension
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.JetBounds.Local

/-!
# A fixed smooth representative of the retained conic phase

The cutoff is selected on a common normalized buffer before the local phase.
A second, fixed cutoff removes only spatial frequencies below the supplied
positive lower bound. On every required ray it is identically one, so exact
radial scaling and all joint phase germs survive. No amplitude or physical
multiplier is changed. Consumers: the smooth phase and annular scaling inputs
of `app:ch_response:eq:direct-envelope-profile` and the supported identities in
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
open RegularSector.Characteristic ConicPhase
variable {d : ℕ}
local notation "T" => TwoTimePoint (Euclidean d)

/-- Choose localization from the common buffers alone, before the chart phase
or coefficients (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_common_phase_localizer {K U : Set T}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : T → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ ∀ p ∈ K, χ =ᶠ[𝓝 p] (fun _ ↦ 1) := by
  obtain ⟨χ, hχ, hc, hs, _, he⟩ :=
    NormalComparison.exists_contDiff_localization hU hK hKU
      (contDiff_const (c := (1 : ℝ))).contDiffOn
  exact ⟨χ, hχ, hc, hs, he⟩

/-- Localize the original phase with the already chosen normalized cutoff.
This operation does not choose a new chart (`app:ch_response:eq:fixed-factor-transfer`). -/
def localizedPhase (χ F : T → ℝ) (p : T) : ℝ := χ p * F p

/-- Smoothness of the actual localized phase, including outside its original
open domain (`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_localizedPhase {χ F : T → ℝ} {U : Set T}
    (hχ : ContDiff ℝ ∞ χ) (hU : IsOpen U) (hs : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (localizedPhase χ F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hF.contDiffAt (hU.mem_nhds (hs hp)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    simp [localizedPhase, hq]

/-- Compact support is inherited from the fixed localizer
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem hasCompactSupport_localizedPhase {χ : T → ℝ}
    (hc : HasCompactSupport χ) (F : T → ℝ) :
    HasCompactSupport (localizedPhase χ F) :=
  HasCompactSupport.of_support_subset_isCompact hc
    ((Function.support_mul_subset_left χ F).trans (subset_tsupport χ))

/-- The explicit small-frequency bump is chosen only from the common positive
spatial-frequency lower bound (`app:ch_response:eq:direct-envelope-profile`). -/
def frequencyBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : Euclidean d) :=
  ⟨δ / 4, δ / 2, by positivity, by linarith⟩

/-- The smooth representative uses the original radial continuation above the
fixed transition, without altering the kernel's original high-pass multiplier
(`app:ch_response:eq:fixed-factor-transfer`). -/
def representative (ℓ : Euclidean d →L[ℝ] ℝ) (δ : ℝ) (hδ : 0 < δ)
    (χ F : T → ℝ) (p : T) : ℝ :=
  (1 - frequencyBump δ hδ p.2.2.2) * extend ℓ (localizedPhase χ F) p

/-- Above the transition the representative and homogeneous extension agree
as joint germs, including both time variables (`app:ch_response:eq:direct-envelope-profile`). -/
theorem representative_eventuallyEq_extend
    (ℓ : Euclidean d →L[ℝ] ℝ) {δ : ℝ} (hδ : 0 < δ) (χ F : T → ℝ)
    {p : T} (hp : δ ≤ ‖p.2.2.2‖) :
    representative ℓ δ hδ χ F =ᶠ[𝓝 p] extend ℓ (localizedPhase χ F) := by
  have hn : p.2.2.2 ∉ tsupport (frequencyBump (d := d) δ hδ) := by
    rw [ContDiffBump.tsupport_eq]
    simpa only [mem_closedBall, dist_zero_right, frequencyBump, not_le] using
      (show δ / 2 < ‖p.2.2.2‖ by linarith)
  filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    continuous_snd.snd.snd.continuousAt] with q hq
  change frequencyBump δ hδ q.2.2.2 = 0 at hq
  simp [representative, hq]

/-- The zero-frequency singularity is removed on a full neighborhood. Away
from zero the original compact radial-extension theorem supplies smoothness
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_representative (ℓ : Euclidean d →L[ℝ] ℝ)
    {δ : ℝ} (hδ : 0 < δ) {χ F : T → ℝ} {U : Set T}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hU : IsOpen U) (hs : tsupport χ ⊆ U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiff ℝ ∞ (representative ℓ δ hδ χ F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.2.2.2 = 0
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have he : (frequencyBump (d := d) δ hδ : Euclidean d → ℝ) =ᶠ[𝓝 p.2.2.2] 1 := by
      simpa only [hp] using (frequencyBump (d := d) δ hδ).eventuallyEq_one
    filter_upwards [he.comp_tendsto continuous_snd.snd.snd.continuousAt] with q hq
    change frequencyBump δ hδ q.2.2.2 = 1 at hq
    simp [representative, hq]
  · exact (contDiffAt_const.sub
      ((frequencyBump δ hδ).contDiffAt.comp p contDiffAt_snd.snd.snd)).mul
      (contDiffAt_extend_of_hasCompactSupport ℓ
        (contDiff_localizedPhase hχ hU hs hF)
        (hasCompactSupport_localizedPhase hc F) hp)

/-- Agreement with the SAME chart on the positive conic buffer, as a joint
germ. The hypotheses are normalized-buffer membership and the primitive
spatial-frequency lower bound (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem representative_eventuallyEq_phase
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ q ∈ K, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    {p : T} (hp : p ∈ domain ℓ K) (hfreq : δ ≤ ‖p.2.2.2‖) :
    representative ℓ δ hδ χ (twoTimePhase C) =ᶠ[𝓝 p] phase ℓ C := by
  apply (representative_eventuallyEq_extend ℓ hδ χ (twoTimePhase C) (p := p) hfreq).trans
  apply extend_eventuallyEq_phase ℓ C (q := p) hp.1.ne'
  filter_upwards [he _ hp.2] with q hq
  simp [localizedPhase, hq]

/-- Restricted exact degree one: both frequencies stay above the one fixed
transition when the normalized frequency has norm at least `δ` and `lam ≥ 1`.
There is no assertion of global homogeneity at zero (`app:ch_response:eq:direct-envelope-profile`). -/
theorem representative_smul (ℓ : Euclidean d →L[ℝ] ℝ)
    {δ : ℝ} (hδ : 0 < δ) (χ F : T → ℝ)
    {p : T} (hp : δ ≤ ‖p.2.2.2‖) {lam : ℝ} (hlam : 1 ≤ lam) :
    representative ℓ δ hδ χ F (p.1, (p.2.1, (p.2.2.1, lam • p.2.2.2))) =
      lam * representative ℓ δ hδ χ F p := by
  have hpos : 0 < lam := zero_lt_one.trans_le hlam
  have hscaled : δ ≤ ‖lam • p.2.2.2‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    exact hp.trans (le_mul_of_one_le_left (norm_nonneg _) hlam)
  rw [(representative_eventuallyEq_extend ℓ hδ χ F
    (p := (p.1, (p.2.1, (p.2.2.1, lam • p.2.2.2)))) hscaled).eq_of_nhds,
    (representative_eventuallyEq_extend ℓ hδ χ F (p := p) hp).eq_of_nhds]
  exact extend_smul ℓ (localizedPhase χ F) p hpos

end JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
