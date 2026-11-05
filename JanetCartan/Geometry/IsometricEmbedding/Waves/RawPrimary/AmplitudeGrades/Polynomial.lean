module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.JointProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Literal

/-!
# Conditional joint grades for the SAME full WKB amplitudes

The four inputs are the actual leading and correction geometric coefficients.
The leading normal and reconstruction come from `Correction.ActualFamily` via
the real inclusion identities; the two correction profiles must be supplied
by the separate ambient reconstruction producer. No amplitude grade is assumed.

The constants are the explicit fixed functions `displacementProfile`,
`derivativeProfile`, and `errorProfile`. They depend only on dimensions and
input profiles, before the choice of scale, frequency, or coefficient fields.
The strongest common baselines are `rpar+1` for displacement and `rpar` for
derivative/error. This does not upgrade the input of differentiated-slice
`OriginalProfiles` to baseline `rpar+2`.

Sources: `app:ch_waves:eq:exact-W-amplitude`,
`app:ch_waves:eq:WKB-amplitude-difference`, and `app:ch_waves:thm:wkb`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseTransfer AmbientResponse

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {J Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}

/-- All joint jets of the SAME published amplitudes, from exactly the five
permitted coefficient profiles. The derivative error is measured against
the literal signed real principal matrix, complexified with the Frobenius
norm (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem full_amplitude_joint_bounds
    (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {rpar : ℕ} {C A₀ A₁ B₀ B₁ : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j)
    {τ L : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hL : 1 ≤ L)
    (hpξ : HasDerivativeProfile J (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L C)
    (hpν₀ : HasDerivativeProfile J (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀)
    (hpν₁ : HasDerivativeProfile J (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁)
    (hpV₀ : HasDerivativeProfile J (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀)
    (hpV₁ : HasDerivativeProfile J (fullCorrectionReconstruction T Q F row col Φ Y r)
      (rpar + 1) L B₁)
    (j : ℕ) {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ J) :
    ‖iteratedFDeriv ℝ j (fullDisplacementAmplitude T Q F row col Φ Y r τ) w‖ ≤
        τ * displacementProfile A₀ A₁ B₀ B₁ j * L ^ (j - (rpar + 1)) ∧
      ‖iteratedFDeriv ℝ j (fullDerivativeAmplitude T Q F row col Φ Y r τ) w‖ ≤
        derivativeProfile n N C A₀ A₁ B₀ B₁ j * L ^ (j - rpar) ∧
      ‖iteratedFDeriv ℝ j (fun y ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ y -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r y) w‖ ≤
        τ * errorProfile n N C A₀ A₁ B₀ B₁ j * L ^ (j - rpar) := by
  have hS := contDiffOn_fullPhase T Q hphase
  have hξ : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) Ω :=
    (phaseGradient_smooth T Q).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  have hx := hJΩ hw
  have hξj := fun j ↦ norm_iteratedFDeriv_le_profile hJ hΩ hJΩ hξ hpξ j hw
  have hν₀j := fun j ↦ norm_iteratedFDeriv_le_profile hJ hΩ hJΩ hν₀ hpν₀ j hw
  have hν₁j := fun j ↦ norm_iteratedFDeriv_le_profile hJ hΩ hJΩ hν₁ hpν₁ j hw
  have hV₀j := fun j ↦ norm_iteratedFDeriv_le_profile hJ hΩ hJΩ hV₀ hpV₀ j hw
  have hV₁j := fun j ↦ norm_iteratedFDeriv_le_profile hJ hΩ hJΩ hV₁ hpV₁ j hw
  have hd : fullDerivativeAmplitude T Q F row col Φ Y r τ =ᶠ[𝓝 w]
      derivativePolynomial τ (fun y ↦ phaseGradient T Q y.1 y.2.2)
        (fullLeadingNormal T Q F row col Φ Y r)
        (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
        (fullLeadingReconstruction T Q F row col Φ Y r)
        (fullCorrectionReconstruction T Q F row col Φ Y r) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact fullDerivativeAmplitude_eq_polynomial T Q F row col Φ Y r (ne_of_gt hτ)
      ((hS.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hν₀.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hν₁.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hV₀.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hV₁.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
  have he : (fun y ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ y -
      fullLeadingPrincipalMatrix T Q F row col Φ Y r y) =ᶠ[𝓝 w]
      derivativeError τ (fun y ↦ phaseGradient T Q y.1 y.2.2)
        (fullLeadingNormal T Q F row col Φ Y r)
        (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
        (fullLeadingReconstruction T Q F row col Φ Y r)
        (fullCorrectionReconstruction T Q F row col Φ Y r) := by
    filter_upwards [hd] with y hy
    rw [hy, fullLeadingPrincipalMatrix_eq_tensor, derivativePolynomial]
    abel
  refine ⟨?_, ?_, ?_⟩
  · rw [fullDisplacementAmplitude_eq_polynomial]
    exact jet_displacement_profile
      (hν₀.contDiffAt (hΩ.mem_nhds hx)) (hν₁.contDiffAt (hΩ.mem_nhds hx))
      (hV₀.contDiffAt (hΩ.mem_nhds hx)) (hV₁.contDiffAt (hΩ.mem_nhds hx))
      hτ.le hτ1 hL hA₀ hB₀ hν₀j hν₁j hV₀j hV₁j j
  · rw [(hd.iteratedFDeriv (𝕜 := ℝ) (n := j)).eq_of_nhds]
    exact jet_derivative_profile hΩ hξ hν₀ hν₁ hV₀ hV₁ hx hτ.le hτ1 hL
      hC hA₀ hA₁ hB₀ hB₁ hξj hν₀j hν₁j hV₀j hV₁j j
  · rw [(he.iteratedFDeriv (𝕜 := ℝ) (n := j)).eq_of_nhds]
    exact jet_error_profile hΩ hξ hν₀ hν₁ hV₀ hV₁ hx hτ.le hτ1 hL
      hC hA₀ hA₁ hB₀ hB₁ hξj hν₀j hν₁j hV₀j hV₁j j

/-- All mixed orders `s` in space and `k ≤ rpar` in joint patch/carrier
parameters are controlled by the total joint jet. These are the three
`τ L^s`, `L^s`, `τ L^s` estimates for the SAME published amplitudes
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem full_amplitude_mixed_bounds
    (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {rpar : ℕ} {C A₀ A₁ B₀ B₁ : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j)
    {τ L : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hL : 1 ≤ L)
    (hpξ : HasDerivativeProfile J (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L C)
    (hpν₀ : HasDerivativeProfile J (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀)
    (hpν₁ : HasDerivativeProfile J (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁)
    (hpV₀ : HasDerivativeProfile J (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀)
    (hpV₁ : HasDerivativeProfile J (fullCorrectionReconstruction T Q F row col Φ Y r)
      (rpar + 1) L B₁)
    (s k : ℕ) (hk : k ≤ rpar)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ J) :
    ‖iteratedFDeriv ℝ (s + k) (fullDisplacementAmplitude T Q F row col Φ Y r τ) w‖ ≤
        τ * displacementProfile A₀ A₁ B₀ B₁ (s + k) * L ^ s ∧
      ‖iteratedFDeriv ℝ (s + k) (fullDerivativeAmplitude T Q F row col Φ Y r τ) w‖ ≤
        derivativeProfile n N C A₀ A₁ B₀ B₁ (s + k) * L ^ s ∧
      ‖iteratedFDeriv ℝ (s + k) (fun y ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ y -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r y) w‖ ≤
        τ * errorProfile n N C A₀ A₁ B₀ B₁ (s + k) * L ^ s := by
  have hh := full_amplitude_joint_bounds T Q F row col Φ Y r hJ hΩ hJΩ hphase
    hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hτ hτ1 hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ (s+k) hw
  have hc := polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁ (s+k)
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega)) (mul_nonneg hτ.le hc.1)),
    hh.2.1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega)) hc.2.2.2.2),
    hh.2.2.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega)) (mul_nonneg hτ.le hc.2.2.2.1))⟩

/-- The strongest common `cNorm` profiles justified by the primitive
budgets. The sums of fixed constants do not alter either baseline or the
powers of `τ` (`app:ch_waves:thm:wkb`). -/
theorem full_amplitude_profiles
    (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {rpar : ℕ} {C A₀ A₁ B₀ B₁ : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j)
    {τ L : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hL : 1 ≤ L)
    (hpξ : HasDerivativeProfile J (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L C)
    (hpν₀ : HasDerivativeProfile J (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀)
    (hpν₁ : HasDerivativeProfile J (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁)
    (hpV₀ : HasDerivativeProfile J (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀)
    (hpV₁ : HasDerivativeProfile J (fullCorrectionReconstruction T Q F row col Φ Y r)
      (rpar + 1) L B₁)
    : HasDerivativeProfile J (fullDisplacementAmplitude T Q F row col Φ Y r τ)
        (rpar + 1) L (fun j ↦ τ * ∑ i ∈ Finset.range (j + 1), displacementProfile A₀ A₁ B₀ B₁ i) ∧
      HasDerivativeProfile J (fullDerivativeAmplitude T Q F row col Φ Y r τ)
        rpar L (fun j ↦ ∑ i ∈ Finset.range (j + 1), derivativeProfile n N C A₀ A₁ B₀ B₁ i) ∧
      HasDerivativeProfile J (fun y ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ y -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r y) rpar L
        (fun j ↦ τ * ∑ i ∈ Finset.range (j + 1), errorProfile n N C A₀ A₁ B₀ B₁ i) := by
  have hh := fun j w hw ↦ full_amplitude_joint_bounds T Q F row col Φ Y r hJ hΩ hJΩ hphase
    hν₀ hν₁ hV₀ hV₁ hC hA₀ hA₁ hB₀ hB₁ hτ hτ1 hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ j (w := w) hw
  have hc := polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁
  refine ⟨profile_of_jet_bounds hL hτ.le (fun j ↦ (hc j).1)
    (fun j w hw ↦ (hh j w hw).1), ?_,
    profile_of_jet_bounds hL hτ.le (fun j ↦ (hc j).2.2.2.1)
      (fun j w hw ↦ (hh j w hw).2.2)⟩
  simpa only [one_mul] using profile_of_jet_bounds hL zero_le_one
    (fun j ↦ (hc j).2.2.2.2) (fun j w hw ↦ by
      simpa only [one_mul] using (hh j w hw).2.1)

end JanetCartan.RawPrimary.AmplitudeGrades.Polynomial
