module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedKernelBounds

/-!
# Global smoothness of the literal cut corrected amplitude

The corrected sampling constructor requires continuity on the entire ambient
space. Its original cutoff support and the SAME locally smooth raw and response
fields produce this regularity without any choice of a new amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling
open CorrectedAtoms RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- Extend the literal corrected derivative smoothly using its supplied
cutoff. Only the original coefficient and SAME response smoothness on the
cutoff support are needed. This supplies the continuity input of
`correctedColoredCrossBandData` (`app:ch_mean_pairs:defn:mean-canonical`,
`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem contDiff_cutCorrectedDerivativeAmplitude
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (κ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hκ : ContDiff ℝ ∞ κ) (hκsupport : tsupport κ ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {τ : ℝ} (hτ : τ ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω) :
    ContDiff ℝ ∞ (fun w ↦ κ w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w) := by
  have hraw := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ).2
  have hr := contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r
    hΩ hphase χ B τ hresponse
  have hcorr : ContDiffOn ℝ ∞
      (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ) Ω := hraw.sub hr
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w ∈ tsupport κ
  · exact hκ.contDiffAt.smul (hcorr.contDiffAt (hΩ.mem_nhds (hκsupport hw)))
  · have hz : κ =ᶠ[𝓝 w] 0 := notMem_tsupport_iff_eventuallyEq.mp hw
    apply (contDiffAt_const (c := (0 : Matrix (Fin N) (Fin n) ℂ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_smul]

end JanetCartan.Sampling
