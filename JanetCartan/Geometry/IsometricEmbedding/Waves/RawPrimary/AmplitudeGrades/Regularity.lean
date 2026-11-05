module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial

/-!
# Smoothness of the literal WKB amplitudes from their geometric coefficients

The deduction used after reconstructing the SAME corrected family in
`exists_fullAmplitude_grades_of_corrected_family_outputs`. The derivative is
the actual polynomial identified in `app:ch_waves:eq:WKB-amplitude-difference`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open JanetCartan.RawPrimary.AmplitudeGrades.Polynomial

/-- Smoothness of the SAME displacement and derivative amplitudes from their
four actual geometric coefficients (`app:ch_waves:eq:individual-representation`).
The quantitative assembly below produces all four smoothness hypotheses. -/
theorem contDiffOn_fullAmplitudes_of_coefficients
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {τ : ℝ} (hτ : τ ≠ 0) :
    ContDiffOn ℝ ∞ (fullDisplacementAmplitude T Q F row col Φ Y r τ) Ω ∧
      ContDiffOn ℝ ∞ (fullDerivativeAmplitude T Q F row col Φ Y r τ) Ω := by
  have hS := contDiffOn_fullPhase T Q hphase
  have hξ : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) Ω :=
    (phaseGradient_smooth T Q).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  have h1 := contDiffOn_correctionOne hΩ hξ hν₀ hν₁ hV₀
  have h2 := contDiffOn_correctionTwo hΩ hξ hν₁ hV₀ hV₁
  have h3 := contDiffOn_physicalJacobian hΩ hV₁
  constructor
  · rw [fullDisplacementAmplitude_eq_polynomial]
    exact ((hν₀.const_smul _).add ((hV₀.add (hν₁.const_smul _)).const_smul _)).add
      (hV₁.const_smul _)
  · apply ((contDiffOn_normalTensor hξ hν₀).neg.add
      (((h1.const_smul (τ : ℂ)).add (h2.const_smul ((τ : ℂ) ^ 2))).add
        (h3.const_smul ((τ : ℂ) ^ 3)))).congr
    intro w hw
    exact fullDerivativeAmplitude_eq_polynomial T Q F row col Φ Y r hτ
      ((hS.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
      ((hν₀.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
      ((hν₁.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
      ((hV₀.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))
      ((hV₁.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp))

end JanetCartan.RawPrimary.AmplitudeGrades
