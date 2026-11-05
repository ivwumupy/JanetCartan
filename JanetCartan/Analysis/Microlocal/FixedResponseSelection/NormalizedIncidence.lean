module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.FullSourceRegularity
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.FullSourceIncidence
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.Conic

/-!
# Capture every original source meeting a conic solver mask

Uniform full-momentum comparison and compactness control normalization of the
original free covectors. Thus the current angular incidence lies in a fixed
slightly larger frozen incidence neighborhood, including every closed mask
shoulder. These lemmas do not identify independently selected source families.
Consumer: finite same-family source-radius selection for
`app:ch_response:eq:direct-envelope-profile`.
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

/-- The actual full-momentum comparison uniformly controls the normalized
current and frozen covectors on the entire original compact source support.
Nonvanishing is proved from the original frozen Hamilton chart. The threshold
precedes every angular mask and source label
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem exists_uniform_full_source_normalized_covector_comparison
    {J : Set (E × Param)} (hJ : IsCompact J) (hJT : J ⊆ domain T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ w ∈ J,
        phaseGradient T Q w.1 w.2.2 ≠ 0 ∧
        dist (NormedSpace.normalize (phaseGradient T Q w.1 w.2.2))
          (NormedSpace.normalize (T.reference.covector (0, w.2.2))) < ε := by
  let F : E × Param → E := fun w ↦ T.reference.covector (0, w.2.2)
  have hF : ContinuousOn F J := (T.continuousOn_frozen_full_source_pair.mono hJT).snd
  have hnonzero w (hw : w ∈ J) : F w ≠ 0 := by
    have hphase : (w.1, w.2.2) ∈ phaseDomain T := hJT hw
    have hζ : w.2.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius := by
      change dist (w.1, w.2.2) (0, FullPhaseCharts.ActualPhase.covectorCenter T) <
        T.family.radius at hphase
      rw [Prod.dist_eq] at hphase
      exact (max_lt_iff.mp hphase).2
    exact (T.full_source_frozen_covector_regular hζ).1
  let A : Set (E × E) := {p | p.1 ≠ 0 ∧ p.2 ≠ 0}
  have hA : IsOpen A :=
    (isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)
  have hnormalize : ContinuousOn
      (fun p : E × E ↦ dist (NormedSpace.normalize p.1) (NormedSpace.normalize p.2)) A := by
    intro p hp
    have h₁ : ContinuousAt (fun p : E × E ↦ NormedSpace.normalize p.1) p :=
      ((continuous_norm.comp continuous_fst).continuousAt.inv₀ (norm_ne_zero_iff.mpr hp.1)).smul
        continuousAt_fst
    have h₂ : ContinuousAt (fun p : E × E ↦ NormedSpace.normalize p.2) p :=
      ((continuous_norm.comp continuous_snd).continuousAt.inv₀ (norm_ne_zero_iff.mpr hp.2)).smul
        continuousAt_snd
    exact (show ContinuousAt (fun p : E × E ↦
      dist (NormedSpace.normalize p.1) (NormedSpace.normalize p.2)) p from
        h₁.dist h₂).continuousWithinAt
  let B := A ∩ (fun p : E × E ↦ dist (NormedSpace.normalize p.1)
    (NormedSpace.normalize p.2)) ⁻¹' Iio ε
  have hB : IsOpen B := hnormalize.isOpen_inter_preimage hA isOpen_Iio
  have hK : IsCompact ((fun w ↦ (F w, F w)) '' J) :=
    hJ.image_of_continuousOn (hF.prodMk hF)
  have hKB : (fun w ↦ (F w, F w)) '' J ⊆ B := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨⟨hnonzero w hw, hnonzero w hw⟩, by simpa using hε⟩
  obtain ⟨η, hη, hηB⟩ := hK.exists_thickening_subset_open hB hKB
  obtain ⟨δ, hδ, hcompare⟩ := T.exists_full_source_covector_comparison hη
  refine ⟨min δ T.family.threshold, lt_min hδ T.family.threshold_pos, min_le_right _ _, ?_⟩
  intro Q hQ w hw
  have hc : dist (phaseGradient T Q w.1 w.2.2) (F w) < η :=
    hcompare Q (hQ.trans_le (min_le_left _ _)) (w.1, w.2.2) (hJT hw)
  have hb : (phaseGradient T Q w.1 w.2.2, F w) ∈ B := by
    apply hηB
    apply mem_thickening_iff.mpr
    exact ⟨(F w, F w), mem_image_of_mem (fun w ↦ (F w, F w)) hw, by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hc⟩
  exact ⟨hb.1.1, hb.2⟩

/-- Every current full source whose covector meets the closed conic-mask
support at ANY positive frequency scale belongs to the doubled FROZEN angular incidence neighborhood. The
threshold is uniform over all masks obeying the given angular margin and
retains all original source parameters, including closed support shoulders
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_uniform_full_source_scaled_angular_incidence_capture
    {J : Set (E × Param)} (hJ : IsCompact J) (hJT : J ⊆ domain T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ (η₀ : E) (mask : E → ℝ),
        tsupport mask ∩ sphere (0 : E) 1 ⊆ closedBall η₀ ε →
      ∀ w ∈ J, ∀ scale : ℝ, 0 < scale →
        scale • phaseGradient T Q w.1 w.2.2 ∈ tsupport (RegularSector.FiniteMasks.conicMask mask) →
        NormedSpace.normalize (T.reference.covector (0, w.2.2)) ∈ ball η₀ (2 * ε) := by
  obtain ⟨δ, hδ, hδT, hcompare⟩ :=
    T.exists_uniform_full_source_normalized_covector_comparison hJ hJT hε
  refine ⟨δ, hδ, hδT, ?_⟩
  intro Q hQ η₀ mask hmask w hw scale hscale hsource
  have hc := hcompare Q hQ w hw
  have hs := RegularSector.FiniteMasks.conicMask_tsupport_subset mask hsource
  simp only [Set.mem_ofPred_eq, NormedSpace.normalize_smul_of_pos hscale] at hs
  have hnorm : NormedSpace.normalize (phaseGradient T Q w.1 w.2.2) ∈ sphere (0 : E) 1 := by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hc.1
  have hb := hmask ⟨hs.2, hnorm⟩
  have hd := dist_triangle (NormedSpace.normalize (T.reference.covector (0, w.2.2)))
    (NormedSpace.normalize (phaseGradient T Q w.1 w.2.2)) η₀
  rw [dist_comm (NormedSpace.normalize (T.reference.covector (0, w.2.2)))
    (NormedSpace.normalize (phaseGradient T Q w.1 w.2.2))] at hd
  exact lt_of_le_of_lt hd (by linarith [hc.2, mem_closedBall.mp hb])

/-- Every current full source whose covector meets the closed conic-mask
support belongs to the doubled FROZEN angular incidence neighborhood. The
threshold is uniform over all masks obeying the given angular margin and
retains all original source parameters, including closed support shoulders
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_uniform_full_source_angular_incidence_capture
    {J : Set (E × Param)} (hJ : IsCompact J) (hJT : J ⊆ domain T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ (η₀ : E) (mask : E → ℝ),
        tsupport mask ∩ sphere (0 : E) 1 ⊆ closedBall η₀ ε →
      ∀ w ∈ J,
        phaseGradient T Q w.1 w.2.2 ∈ tsupport (RegularSector.FiniteMasks.conicMask mask) →
        NormedSpace.normalize (T.reference.covector (0, w.2.2)) ∈ ball η₀ (2 * ε) := by
  obtain ⟨δ, hδ, hδT, hcompare⟩ :=
    T.exists_uniform_full_source_normalized_covector_comparison hJ hJT hε
  refine ⟨δ, hδ, hδT, ?_⟩
  intro Q hQ η₀ mask hmask w hw hsource
  have hc := hcompare Q hQ w hw
  have hs := RegularSector.FiniteMasks.conicMask_tsupport_subset mask hsource
  have hnorm : NormedSpace.normalize (phaseGradient T Q w.1 w.2.2) ∈ sphere (0 : E) 1 := by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hc.1
  have hb := hmask ⟨hs.2, hnorm⟩
  have hd := dist_triangle (NormedSpace.normalize (T.reference.covector (0, w.2.2)))
    (NormedSpace.normalize (phaseGradient T Q w.1 w.2.2)) η₀
  rw [dist_comm (NormedSpace.normalize (T.reference.covector (0, w.2.2)))
    (NormedSpace.normalize (phaseGradient T Q w.1 w.2.2))] at hd
  exact lt_of_le_of_lt hd (by linarith [hc.2, mem_closedBall.mp hb])

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
