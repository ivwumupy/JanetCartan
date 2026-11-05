module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.DiagonalBuffers.Geometry

/-!
# Uniform diagonal margins for compact negative source incidences

The compact support retains all original source labels and free covectors.
Its frozen diagonals lie in the same retained integration domain. Compactness
and the actual full Hamilton momentum comparison then protect every current
diagonal by one metric margin, before histories, masks and operators.
Consumer: finite source-incidence stationary selection in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ArbitraryAccuracy
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open ResponseTransfer.RetainedFactors ResponseTransfer.DirectEvolution LeadingWave.FullModulation
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d + 1)

/-- Every original source in a compact incidence set has a fourfold
diagonal margin in the SAME integration domain, uniformly for all admitted
nearby fields. The frozen frequency containment is geometric; the actual
full-momentum comparison proves the varying-field statement. No anchor
identity, carrier restriction or stationary-map premise is used
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_uniform_negative_full_source_compact_diagonal_margin
    (i : Fin (d + 1)) (z : RootState (Euclidean d)) {ε : ℝ} (hε : 0 < ε)
    {J : Set (E × Param)} (hJ : IsCompact J) (hJT : J ⊆ domain T)
    (hphysical : ∀ w ∈ J, primaryCoordinateChange i w.1 ∈
      closure (elapsedPhysicalBox z (ε / 2)))
    {O : Set E} (hO : IsOpen O)
    (hfrequency : ∀ w ∈ J,
      primaryCoordinateChange i (-T.reference.covector (0, w.2.2)) ∈ O) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ ρ > (0 : ℝ),
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ w ∈ J,
        closedBall (WithLp.toLp 2
          (primaryCoordinateChange i w.1,
            gradient (fun y ↦ T.negativeFullSourcePhaseInCoordinates i Q y w.2)
              (primaryCoordinateChange i w.1))) (4 * ρ) ⊆
          retainedOpenIntegrationDomain z ε O := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let p := primaryCoordinateChange i
  let F : E × Param → W := fun w ↦ e.symm (p w.1, p (-T.reference.covector (0, w.2.2)))
  have hF : ContinuousOn F J := e.symm.continuous.comp_continuousOn
    ((p.continuous.comp continuous_fst).continuousOn.prodMk
      (p.continuous.comp_continuousOn
        ((T.continuousOn_frozen_full_source_pair.mono hJT).snd.neg)))
  have hK : IsCompact (F '' J) := hJ.image_of_continuousOn hF
  have hD : IsOpen (retainedOpenIntegrationDomain z ε O) :=
    ((isOpen_elapsedPhysicalBox z ε).prod hO).preimage e.continuous
  have hKD : F '' J ⊆ retainedOpenIntegrationDomain z ε O := by
    rintro v ⟨w, hw, rfl⟩
    exact ⟨UniformEvolution.closure_elapsedPhysicalBox_half_subset hε (hphysical w hw),
      hfrequency w hw⟩
  obtain ⟨r, hr, hthick⟩ := hK.exists_thickening_subset_open hD hKD
  let B := (1 + ‖e.symm.toContinuousLinearMap‖) * (1 + ‖p.toContinuousLinearMap‖)
  have hB : 0 < B := by dsimp [B]; positivity
  have hAB : ‖e.symm.toContinuousLinearMap‖ * ‖p.toContinuousLinearMap‖ ≤ B := by
    dsimp [B]
    nlinarith [norm_nonneg e.symm.toContinuousLinearMap, norm_nonneg p.toContinuousLinearMap]
  obtain ⟨δ, hδ, hcompare⟩ := T.exists_negative_full_source_covector_comparison
    (show 0 < r / (2 * B) by positivity)
  refine ⟨min δ T.family.threshold, lt_min hδ T.family.threshold_pos,
    min_le_right _ _, r / 16, by positivity, ?_⟩
  intro Q hQ w hw
  have hwphase : (w.1, w.2.2) ∈ phaseDomain T := hJT hw
  have hgrad := T.negativeFullSourcePhaseInCoordinates_gradient i Q (c := w.2)
    (x := p w.1) (by simpa [p] using hwphase)
  simp only [p, ContinuousLinearEquiv.symm_apply_apply] at hgrad
  rw [hgrad]
  let θ := -phaseGradient T Q w.1 w.2.2
  let θ₀ := -T.reference.covector (0, w.2.2)
  have hclose : dist θ θ₀ < r / (2 * B) :=
    hcompare Q (hQ.trans_le (min_le_left _ _)) (w.1, w.2.2) hwphase
  have hd : dist (e.symm (p w.1, p θ)) (F w) < r / 2 := by
    calc
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * dist (p w.1, p θ) (p w.1, p θ₀) :=
        e.symm.toContinuousLinearMap.dist_le_opNorm _ _
      _ = ‖e.symm.toContinuousLinearMap‖ * dist (p θ) (p θ₀) := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖p.toContinuousLinearMap‖ * dist θ θ₀) :=
        mul_le_mul_of_nonneg_left (p.toContinuousLinearMap.dist_le_opNorm _ _)
          (norm_nonneg _)
      _ ≤ B * dist θ θ₀ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hAB dist_nonneg
      _ < B * (r / (2 * B)) := mul_lt_mul_of_pos_left hclose hB
      _ = r / 2 := by field_simp
  intro v hv
  apply hthick
  apply mem_thickening_iff.mpr
  refine ⟨F w, mem_image_of_mem F hw, ?_⟩
  have htri := dist_triangle v (e.symm (p w.1, p θ)) (F w)
  have hv' : dist v (e.symm (p w.1, p θ)) ≤ 4 * (r / 16) := hv
  linarith

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
