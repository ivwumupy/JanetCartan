module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FrequencyCutoffs
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms

/-!
# Fixed-mask contributions to the canonical primitive budgets

The measurement, angular and high-frequency contributions in
`app:ch_background:eq:bg-full-complex-amplitude` are fixed before the immersion
and initial scalar. Their constants are their actual finite norms on the
supplied primitive charts. The remaining normal and detector fields are
geometric estimates, not part of these fixed-mask inputs.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ContinuumNormalReduction.TransportSymbol

/-- Actual fixed norms supply all three mask controls on the existing
coefficient charts. The high-frequency mask is the literal cutoff with
plateaus at one and two, and the physical measurement is the same cutoff
as the periodic row. Consumer: the first three fields of
`CoefficientNormCharts.Controls`; source: `app:ch_background:eq:bg-T`. -/
theorem exists_fixedMask_controls {n : ℕ} (D : CoefficientNormCharts n)
    {r : ℝ} (hr : 0 < r)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (hang : ContDiffOn ℝ ∞ (Function.uncurry angular) D.angular.region) :
    ∃ M ≥ 0, ∃ B : ℕ → ℝ, (∀ s, 1 ≤ B s) ∧
      ∀ s H, 1 ≤ H →
        D.measurement.Controls s M (B s) H (FixedCutoffs.physical hr 1) ∧
        D.angular.Controls s M (B s) H (Function.uncurry angular) ∧
        D.high.Controls s M (B s) H FixedCutoffs.highFrequency := by
  let f : Euclidean n → ℝ := FixedCutoffs.physical hr 1
  let a := Function.uncurry angular
  let h := FixedCutoffs.highFrequency
  let M := cNorm D.measurement.carrier 1 f + cNorm D.angular.carrier 1 a +
    cNorm D.high.carrier 1 h
  let B := fun s ↦ 1 + cNorm D.measurement.carrier s f + cNorm D.angular.carrier s a +
    cNorm D.high.carrier s h
  have hM : 0 ≤ M :=
    add_nonneg (add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..)) (cNorm_nonneg ..)
  have hB (s) : 1 ≤ B s := by
    dsimp [B]
    linarith [cNorm_nonneg D.measurement.carrier s f,
      cNorm_nonneg D.angular.carrier s a, cNorm_nonneg D.high.carrier s h]
  refine ⟨M, hM, B, hB, ?_⟩
  intro s H hH
  have hBH : B s ≤ B s * H := le_mul_of_one_le_right (zero_le_one.trans (hB s)) hH
  have hl₁ := cNorm_nonneg D.measurement.carrier 1 f
  have hl₂ := cNorm_nonneg D.angular.carrier 1 a
  have hl₃ := cNorm_nonneg D.high.carrier 1 h
  have hh₁ := cNorm_nonneg D.measurement.carrier s f
  have hh₂ := cNorm_nonneg D.angular.carrier s a
  have hh₃ := cNorm_nonneg D.high.carrier s h
  refine ⟨⟨(FixedCutoffs.physical hr 1).contDiff.contDiffOn, ?_, ?_⟩,
    ⟨hang, ?_, ?_⟩, ⟨FixedCutoffs.highFrequency_smooth.contDiffOn, ?_, ?_⟩⟩
  · change cNorm D.measurement.carrier 1 f ≤ M
    dsimp [M]
    linarith
  · change 1 + cNorm D.measurement.carrier s f ≤ B s * H
    apply le_trans _ hBH
    dsimp [B]
    linarith
  · change cNorm D.angular.carrier 1 a ≤ M
    dsimp [M]
    linarith
  · change 1 + cNorm D.angular.carrier s a ≤ B s * H
    apply le_trans _ hBH
    dsimp [B]
    linarith
  · change cNorm D.high.carrier 1 h ≤ M
    dsimp [M]
    linarith
  · change 1 + cNorm D.high.carrier s h ≤ B s * H
    apply le_trans _ hBH
    dsimp [B]
    linarith

end JanetCartan.ContinuumRow.CanonicalCarrier
