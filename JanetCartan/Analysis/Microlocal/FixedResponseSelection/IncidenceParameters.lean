module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.NormalizedIncidence
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.SourceDomain

/-!
# Compact parameter buffers for every angular source incidence

Construct actual parameter neighborhoods from the unchanged original full
source compact and a fixed open cone. Their compact closures stay in the
original free-covector domain. The full-momentum comparison then captures every
original source that meets the selected angular mask, before masks, fields or
operators are chosen. Consumer: same-family stationary source-radius selection
for `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu LeadingWave.FullModulation
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d

/-- The complete original parameter compact intersected with a closed
angular incidence collar has an open buffer with compact closure in the
original free-covector domain and prescribed conic neighborhood. All source
labels and radii in that incidence are retained
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_full_source_incidence_parameter_buffer
    {Csrc : Set Param} (hCsrc : IsCompact Csrc)
    (hcsrc : ∀ c ∈ Csrc,
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    (η₀ : E) {r : ℝ} (hr : 0 < r)
    {W : Set E} (hW : IsOpen W)
    (hcone : ∀ θ ∈ W, ∀ a : ℝ, 0 < a → a • θ ∈ W)
    (hball : closedBall η₀ (3 * r) ⊆ W) :
    ∃ V : Set Param, IsOpen V ∧ IsCompact (closure V) ∧
      {c ∈ Csrc | NormedSpace.normalize (T.reference.covector (0, c.2)) ∈
        closedBall η₀ (2 * r)} ⊆ V ∧
      ∀ c ∈ closure V,
        c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius ∧
        T.reference.covector (0, c.2) ∈ W := by
  let D : Set Param := univ ×ˢ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius
  have hD : IsOpen D := isOpen_univ.prod isOpen_ball
  let F : Param → E := fun c ↦ T.reference.covector (0, c.2)
  have hF : ContinuousOn F D := T.continuousOn_frozen_full_source_pair.snd.comp
    (f := fun c : Param ↦ ((0 : E), c)) (continuousOn_const.prodMk continuousOn_id)
    (fun c hc ↦ T.full_source_mem_phaseDomain_of_physical_buffer
      (mem_closedBall_self T.physicalRadius_pos.le) hc.2)
  have hnonzero c (hc : c ∈ D) : F c ≠ 0 := (T.full_source_frozen_covector_regular hc.2).1
  have hN : ContinuousOn (fun c ↦ NormedSpace.normalize (F c)) D := by
    intro c hc
    exact ((hF.norm c hc).inv₀ (norm_ne_zero_iff.mpr (hnonzero c hc))).smul (hF c hc)
  have hCD : Csrc ⊆ D := fun c hc ↦ ⟨mem_univ _, hcsrc c hc⟩
  let C := {c ∈ Csrc | NormedSpace.normalize (F c) ∈ closedBall η₀ (2 * r)}
  have hC : IsCompact C := hCsrc.of_isClosed_subset
    ((hN.mono hCD).preimage_isClosed_of_isClosed hCsrc.isClosed isClosed_closedBall)
    inter_subset_left
  let O := D ∩ F ⁻¹' W
  have hO : IsOpen O := hF.isOpen_inter_preimage hD hW
  have hCO : C ⊆ O := by
    intro c hc
    have hcD := hCD hc.1
    refine ⟨hcD, ?_⟩
    change F c ∈ W
    have hθW := hball (closedBall_subset_closedBall (by linarith : 2 * r ≤ 3 * r) hc.2)
    simpa only [NormedSpace.norm_smul_normalize] using
      hcone (NormedSpace.normalize (F c)) hθW ‖F c‖ (norm_pos_iff.mpr (hnonzero c hcD))
  obtain ⟨V, hV, hCV, hVO, hVK⟩ := exists_open_between_and_isCompact_closure hC hO hCO
  exact ⟨V, hV, hVK, hCV, fun c hc ↦ ⟨(hVO hc).1.2, (hVO hc).2⟩⟩

/-- At a retained sector direction choose an angular radius, a compactly
buffered FULL parameter incidence domain, and a coefficient threshold BEFORE
masks and current fields. Every original source meeting any positive-frequency dilation of a conic mask in that
angular radius belongs to this domain, including closed support shoulders.
The frozen source covectors throughout its closure lie in the prescribed cone;
there is no chart/source anchor equality
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_full_source_scaled_conic_incidence_buffer
    {Csrc : Set Param} (hCsrc : IsCompact Csrc)
    (hcsrc : ∀ c ∈ Csrc,
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    {Xsrc : Set E} (hXsrc : IsCompact Xsrc) (hsource : Xsrc ×ˢ Csrc ⊆ domain T)
    {ξ : E} (hξ : ξ ≠ 0) {W : Set E} (hW : IsOpen W) (hξW : ξ ∈ W)
    (hcone : ∀ θ ∈ W, ∀ a : ℝ, 0 < a → a • θ ∈ W) :
    ∃ r > (0 : ℝ), ∃ V : Set Param, IsOpen V ∧ IsCompact (closure V) ∧
      (∀ c ∈ closure V,
        c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius ∧
        T.reference.covector (0, c.2) ∈ W) ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      ∀ mask : E → ℝ,
        tsupport mask ∩ sphere (0 : E) 1 ⊆ closedBall (NormedSpace.normalize ξ) r →
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ x ∈ Xsrc, ∀ c ∈ Csrc, ∀ scale : ℝ, 0 < scale →
        scale • phaseGradient T Q x c.2 ∈ tsupport (RegularSector.FiniteMasks.conicMask mask) → c ∈ V := by
  have hnormalized : NormedSpace.normalize ξ ∈ W :=
    hcone ξ hξW ‖ξ‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr hξ))
  obtain ⟨a, ha, haW⟩ := Metric.isOpen_iff.mp hW _ hnormalized
  let r := a / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : closedBall (NormedSpace.normalize ξ) (3 * r) ⊆ W :=
    (closedBall_subset_ball (by dsimp [r]; linarith : 3 * r < a)).trans haW
  obtain ⟨V, hV, hVK, hcover, hclosure⟩ :=
    T.exists_full_source_incidence_parameter_buffer hCsrc hcsrc (NormedSpace.normalize ξ) hr hW hcone hball
  obtain ⟨δ, hδ, hδT, hcapture⟩ :=
    T.exists_uniform_full_source_scaled_angular_incidence_capture (hXsrc.prod hCsrc) hsource hr
  refine ⟨r, hr, V, hV, hVK, hclosure, δ, hδ, hδT, ?_⟩
  intro mask hmask Q hQ x hx c hc scale hscale hincidence
  exact hcover ⟨hc, ball_subset_closedBall (hcapture Q hQ _ mask hmask (x, c) ⟨hx, hc⟩ scale hscale hincidence)⟩

/-- At a retained sector direction choose an angular radius, a compactly
buffered FULL parameter incidence domain, and a coefficient threshold BEFORE
masks and current fields. Every original source meeting any conic mask in that
angular radius belongs to this domain, including closed support shoulders.
The frozen source covectors throughout its closure lie in the prescribed cone;
there is no chart/source anchor equality
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_full_source_conic_incidence_buffer
    {Csrc : Set Param} (hCsrc : IsCompact Csrc)
    (hcsrc : ∀ c ∈ Csrc,
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    {Xsrc : Set E} (hXsrc : IsCompact Xsrc) (hsource : Xsrc ×ˢ Csrc ⊆ domain T)
    {ξ : E} (hξ : ξ ≠ 0) {W : Set E} (hW : IsOpen W) (hξW : ξ ∈ W)
    (hcone : ∀ θ ∈ W, ∀ a : ℝ, 0 < a → a • θ ∈ W) :
    ∃ r > (0 : ℝ), ∃ V : Set Param, IsOpen V ∧ IsCompact (closure V) ∧
      (∀ c ∈ closure V,
        c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius ∧
        T.reference.covector (0, c.2) ∈ W) ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      ∀ mask : E → ℝ,
        tsupport mask ∩ sphere (0 : E) 1 ⊆ closedBall (NormedSpace.normalize ξ) r →
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ x ∈ Xsrc, ∀ c ∈ Csrc,
        phaseGradient T Q x c.2 ∈ tsupport (RegularSector.FiniteMasks.conicMask mask) → c ∈ V := by
  have hnormalized : NormedSpace.normalize ξ ∈ W :=
    hcone ξ hξW ‖ξ‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr hξ))
  obtain ⟨a, ha, haW⟩ := Metric.isOpen_iff.mp hW _ hnormalized
  let r := a / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : closedBall (NormedSpace.normalize ξ) (3 * r) ⊆ W :=
    (closedBall_subset_ball (by dsimp [r]; linarith : 3 * r < a)).trans haW
  obtain ⟨V, hV, hVK, hcover, hclosure⟩ :=
    T.exists_full_source_incidence_parameter_buffer hCsrc hcsrc (NormedSpace.normalize ξ) hr hW hcone hball
  obtain ⟨δ, hδ, hδT, hcapture⟩ :=
    T.exists_uniform_full_source_angular_incidence_capture (hXsrc.prod hCsrc) hsource hr
  refine ⟨r, hr, V, hV, hVK, hclosure, δ, hδ, hδT, ?_⟩
  intro mask hmask Q hQ x hx c hc hincidence
  exact hcover ⟨hc, ball_subset_closedBall (hcapture Q hQ _ mask hmask (x, c) ⟨hx, hc⟩ hincidence)⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
