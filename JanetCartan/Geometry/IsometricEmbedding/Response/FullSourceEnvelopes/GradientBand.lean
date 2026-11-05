module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.SourceDomain
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.PrimaryGradientBand

/-!
# The selector's gradient band for the original full source

Use full-source incidence at the frozen covector to produce the two radial
bounds of the complementary estimate. The parameter neighborhood here is
only an upper bound for the working domain; it is never identified with the
independently supplied stationary radius.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullSourceEnvelopes
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu CompatibleResponse HamiltonPhase
open LeadingWave.FullModulation RetainedFactors
variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d

/-- The original source has a positive spatial gradient band, uniformly
before the varying frame, at every point of the closed physical buffer and
every full parameter in the supplied smaller working domain. This supplies
`a₀, B₀` for `fullSource_capped_solver_residual_envelopes` from
`exists_uniform_full_source_parameter_neighborhood`
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_fullSource_gradient_band
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U) {c₀ : Par}
    (hc₀ : c₀.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    (hξ : T.reference.covector (0, c₀.2) ≠ 0) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ s > (0 : ℝ),
      ∀ V : Set Par, V ⊆ closedBall c₀ (4 * s) →
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ i : Fin (d + 1), ∀ y : E,
        (primaryCoordinateChange i).symm y ∈ closedBall 0 T.physicalRadius →
      ∀ c ∈ V, ‖T.reference.covector (0, c₀.2)‖ / 2 ≤
          ‖fderiv ℝ (fun x ↦ T.fullSourcePhaseInCoordinates i Q x c) y‖ ∧
        ‖fderiv ℝ (fun x ↦ T.fullSourcePhaseInCoordinates i Q x c) y‖ ≤
          2 * ‖T.reference.covector (0, c₀.2)‖ := by
  let b := ‖T.reference.covector (0, c₀.2)‖
  have hb : 0 < b := norm_pos_iff.mpr hξ
  let N : Set ((Fin (d + 1) → MetricTensor (d + 1)) × E) :=
    univ ×ˢ {ξ : E | b/2 < ‖ξ‖ ∧ ‖ξ‖ < 2*b}
  have hN : IsOpen N := isOpen_univ.prod ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const))
  have hbase : (cubeStress (d + 1), T.reference.covector (0, c₀.2)) ∈ N :=
    ⟨mem_univ _, by change b/2 < b ∧ b < 2*b; constructor <;> linarith only [hb]⟩
  obtain ⟨δ, hδ, hδT, s, hs, hpar, hpair⟩ := T.exists_uniform_full_source_parameter_neighborhood
    hframe hc₀ hN hbase
  refine ⟨δ, hδ, hδT, s, hs,?_⟩
  intro V hV Q hQ i y hy c hc
  have hc' := hV hc
  have hband := (hpair Q hQ _ hy c hc').2
  have he : ‖fderiv ℝ (fun x ↦ T.fullSourcePhaseInCoordinates i Q x c) y‖ =
      ‖phaseGradient T Q ((primaryCoordinateChange i).symm y) c.2‖ := by
    rw [← (InnerProductSpace.toDual ℝ E).symm.norm_map]
    change ‖gradient (fun x ↦ T.fullSourcePhaseInCoordinates i Q x c) y‖ = _
    rw [T.fullSourcePhaseInCoordinates_gradient i Q
      (T.full_source_mem_phaseDomain_of_physical_buffer hy (hpar hc').2), norm_primaryCoordinateChange]
  rw [he]
  exact ⟨hband.1.le, hband.2.le⟩

end JanetCartan.ResponseTransfer.FullSourceEnvelopes
