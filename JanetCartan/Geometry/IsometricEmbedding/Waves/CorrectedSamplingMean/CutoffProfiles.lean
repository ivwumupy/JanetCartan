module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedProfileBounds

/-!
# Global jets of the supplied corrected coefficient cutoff

The original five raw profiles and the SAME response jets produce global
spatial/carrier/covector bounds for the coefficient used by
`correctedColoredCrossBandData`. The physical rate stays fixed throughout.
These are the factor bounds for the fixed-rate corrected normal homotopy
(`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedMean
open CorrectedAtoms RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {J Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {rpar : ℕ} {C A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j)
    {τ L : ℝ} (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hL : 1 ≤ L)
    (hpξ : HasDerivativeProfile J (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L C)
    (hpν₀ : HasDerivativeProfile J (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀)
    (hpν₁ : HasDerivativeProfile J (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁)
    (hpV₀ : HasDerivativeProfile J (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀)
    (hpV₁ : HasDerivativeProfile J (fullCorrectionReconstruction T Q F row col Φ Y r) (rpar + 1) L B₁)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    (hresponseJets : ∀ j, ∀ w ∈ J,
      ‖iteratedFDeriv ℝ j (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
        τ * Cresp j * L ^ (j - rpar))


include hJ hΩ hJΩ hphase hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hCresp hτ hτ₁ hL
  hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets

/-- The literal supplied cutoff times the corrected derivative has global
smoothness and every graded joint jet. Its displayed constant depends only
on the fixed cutoff and the six primitive profile sequences; it is independent
of the current fields, physical rate and history scale. No solver-frequency
regularity is used (`app:ch_response:eq:current-atomic-amplitudes`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem cutCorrectedDerivativeAmplitude_budgets_of_profiles
    (κ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (hsupport : tsupport κ ⊆ J) :
    let A := fun j ↦ derivativeProfile n N C A₀ A₁ B₀ B₁ j + Cresp j
    let D := productProfile (ContinuousLinearMap.lsmul ℝ ℝ
      (E := Matrix (Fin N) (Fin n) ℂ)) (fun j ↦ cNorm J j κ) A
    let f := fun w ↦ κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w
    ContDiff ℝ ∞ f ∧ ∀ w, ∀ j, ‖iteratedFDeriv ℝ j f w‖ ≤ D j * L ^ (j - rpar) := by
  intro A D f
  have hA (j : ℕ) : 0 ≤ A j :=
    add_nonneg (polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁ j).2.2.2.2 (hCresp j)
  have hcut (j : ℕ) : 0 ≤ cNorm J j κ := cNorm_nonneg _ _ _
  have hraw := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphase hν₀ hν₁ hV₀ hV₁ hτ.ne').2
  have hresp := contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r
    hΩ hphase χ B τ hresponse
  have ha : ContDiffOn ℝ ∞ (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ) Ω :=
    hraw.sub hresp
  have hz (w) (hw : w ∉ tsupport κ) : f =ᶠ[𝓝 w] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with y hy
    simp only [f, hy, Pi.zero_apply, zero_smul]
  have hf : ContDiff ℝ ∞ f := by
    apply contDiff_iff_contDiffAt.mpr
    intro w
    by_cases hw : w ∈ tsupport κ
    · exact hκ.contDiffAt.smul (ha.contDiffAt (hΩ.mem_nhds (hJΩ (hsupport hw))))
    · exact contDiffAt_const.congr_of_eventuallyEq (hz w hw)
  refine ⟨hf, ?_⟩
  intro w j
  by_cases hw : w ∈ tsupport κ
  · have hj := hsupport hw
    have hbκ (k : ℕ) : ‖iteratedFDeriv ℝ k κ w‖ ≤ cNorm J k κ * L ^ (k - rpar) :=
      (norm_iteratedFDeriv_le_cNorm hJ (hκ.of_le (by simp)) hj le_rfl).trans
        (le_mul_of_one_le_right (hcut k) (one_le_pow₀ hL))
    have hbA (k : ℕ) :
        ‖iteratedFDeriv ℝ k (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
          A k * L ^ (k - rpar) :=
      (fullCorrectedDerivativeAmplitude_joint_bounds T Q F row col Φ Y χ B r
        hJ hΩ hJΩ hphase hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hCresp hτ hτ₁ hL
        hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets k hj).1
    exact jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ
      (E := Matrix (Fin N) (Fin n) ℂ)) hΩ hκ.contDiffOn ha (hJΩ hj) hL hcut hA hbκ hbA j
  · rw [((hz w hw).iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (productProfile_nonneg _ hcut hA j) (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.Sampling.CorrectedMean
