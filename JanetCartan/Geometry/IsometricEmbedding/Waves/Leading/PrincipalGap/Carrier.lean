module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualCoefficients

/-!
# Gaps for the literal carrier gradient and selected cofactor column

These are the two carrier inputs to the positive principal-normal estimate
in `app:ch_waves:thm:leading`. The gradient uses the original quantitative
Hamilton family, and the column uses the original transport minor indices.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport

/-- A common gradient gap on the buffered parameter cube follows from the
nonvanishing frozen covectors and the actual Hamilton comparison. The constants
precede the current frame (`app:ch_waves:thm:leading`). -/
theorem exists_buffered_carrierGradient_norm_lower {n : ℕ} {P : Patch n}
    {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU) :
    ∃ δ > (0 : ℝ), ∃ cξ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius,
      ∀ z ∈ parameterCube (3 * P.radius / 2),
        cξ ≤ ‖T.carrierGradient Q x z‖ := by
  have hsub : parameterCube (3 * P.radius / 2) ⊆
      parameterInterior (2 * P.radius) := by
    intro z hz i
    exact (hz i).trans_lt (by linarith [hP.1])
  have hne : (parameterCube (3 * P.radius / 2)).Nonempty := by
    refine ⟨0, fun i ↦ ?_⟩
    simp only [PiLp.zero_apply, abs_zero]
    linarith [hP.1]
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_parameterCube (3 * P.radius / 2)).exists_isMinOn
    hne (hP.2.2.2.1.continuousOn.mono hsub).norm
  have hp : 0 < ‖P.toFun z₀‖ := norm_pos_iff.mpr
    (T.data.buffered_nonzero (fun i ↦ (hsub hz₀ i).le))
  obtain ⟨δ, hδ, hcomp⟩ := exists_buffered_carrier_value_threshold T (half_pos hp)
  refine ⟨δ, hδ, ‖P.toFun z₀‖ / 2, half_pos hp, ?_⟩
  intro Q hQ x hx z hz
  have hc := hcomp Q hQ x hx z (hsub hz)
  have hm : ‖P.toFun z₀‖ ≤ ‖P.toFun z‖ := hmin hz
  have hd := norm_sub_norm_le (P.toFun z) (T.carrierGradient Q x z)
  rw [norm_sub_rev] at hd
  linarith

/-- The fixed adjugate entry is a coordinate of the literal transport column.
Thus its primitive minor gap bounds that same column from below, with no
renormalization or new nullvector choice (`app:ch_waves:thm:leading`). -/
theorem carrierNullvector_norm_lower_of_minor {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (w : Euclidean n × Euclidean 3) (r c : Fin n) {μ : ℝ}
    (hminor : μ ≤ |(reducedSymbol (Q.1 w.1)
      (T.carrierGradient Q w.1 w.2)).adjugate r c|) :
    μ ≤ ‖carrierNullvector T Q c w‖ := by
  exact hminor.trans (PiLp.norm_apply_le (carrierNullvector T Q c w) r)

end JanetCartan.LeadingWave
