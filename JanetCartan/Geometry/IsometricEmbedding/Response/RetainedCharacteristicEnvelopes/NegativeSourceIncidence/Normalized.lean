module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence.Phase
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.IncidenceParameters

/-!
# Capture of the negative original source by angular masks

Normalize the actual negative momentum and construct its own compact parameter
buffer. The original source labels and free covectors are never changed.
Consumer: the negative incidence selector, before fixing masks, for
`app:ch_response:eq:fixed-factor-transfer`.
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

/-- Negation preserves normalized momentum comparison on the complete
original source compact. The uniform threshold precedes every angular mask
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem exists_uniform_negative_full_source_normalized_covector_comparison
    {J : Set (E × Param)} (hJ : IsCompact J) (hJT : J ⊆ domain T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ w ∈ J,
        -phaseGradient T Q w.1 w.2.2 ≠ 0 ∧
        dist (NormedSpace.normalize (-phaseGradient T Q w.1 w.2.2))
          (NormedSpace.normalize (-T.reference.covector (0, w.2.2))) < ε := by
  obtain ⟨δ, hδ, hδT, hcompare⟩ :=
    T.exists_uniform_full_source_normalized_covector_comparison hJ hJT hε
  refine ⟨δ, hδ, hδT, ?_⟩
  intro Q hQ w hw
  simpa only [neg_ne_zero, NormedSpace.normalize_neg, dist_neg_neg] using
    hcompare Q hQ w hw

/-- Every negative current full source whose covector meets the closed conic-mask
support at ANY positive frequency scale belongs to the doubled FROZEN angular incidence neighborhood. The
threshold is uniform over all masks obeying the given angular margin and
retains all original source parameters, including closed support shoulders
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_uniform_negative_full_source_scaled_angular_incidence_capture
    {J : Set (E × Param)} (hJ : IsCompact J) (hJT : J ⊆ domain T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ (η₀ : E) (mask : E → ℝ),
        tsupport mask ∩ sphere (0 : E) 1 ⊆ closedBall η₀ ε →
      ∀ w ∈ J, ∀ scale : ℝ, 0 < scale →
        scale • (-phaseGradient T Q w.1 w.2.2) ∈ tsupport (RegularSector.FiniteMasks.conicMask mask) →
        NormedSpace.normalize (-T.reference.covector (0, w.2.2)) ∈ ball η₀ (2 * ε) := by
  obtain ⟨δ, hδ, hδT, hcompare⟩ :=
    T.exists_uniform_negative_full_source_normalized_covector_comparison hJ hJT hε
  refine ⟨δ, hδ, hδT, ?_⟩
  intro Q hQ η₀ mask hmask w hw scale hscale hsource
  have hc := hcompare Q hQ w hw
  have hs := RegularSector.FiniteMasks.conicMask_tsupport_subset mask hsource
  simp only [Set.mem_ofPred_eq, NormedSpace.normalize_smul_of_pos hscale] at hs
  have hnorm : NormedSpace.normalize ((-phaseGradient T Q w.1 w.2.2)) ∈ sphere (0 : E) 1 := by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hc.1
  have hb := hmask ⟨hs.2, hnorm⟩
  have hd := dist_triangle (NormedSpace.normalize (-T.reference.covector (0, w.2.2)))
    (NormedSpace.normalize ((-phaseGradient T Q w.1 w.2.2))) η₀
  rw [dist_comm (NormedSpace.normalize (-T.reference.covector (0, w.2.2)))
    (NormedSpace.normalize ((-phaseGradient T Q w.1 w.2.2)))] at hd
  exact lt_of_le_of_lt hd (by linarith [hc.2, mem_closedBall.mp hb])


end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
