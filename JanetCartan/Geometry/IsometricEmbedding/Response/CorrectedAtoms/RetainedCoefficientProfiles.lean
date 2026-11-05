module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Assembly

/-!
# The five actual coefficient profiles on a retained corrected cell

Apply the published reconstruction and phase estimates to the original leading
and correction budgets. The resulting literal coefficients supply
`CorrectedAtoms.exists_uniform_correctedPrimary_sliceSobolev`,
`Sampling.correctedColoredCrossBandData_uniform_bounds_of_profiles` and
`Sampling.norm_fullCorrectedCrossAmplitude_sub_leading_le_of_profiles` without
selecting new rows, flows, source scales or scalar functions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CorrectedAtoms
open RawPrimary RawPrimary.AmplitudeGrades LeadingWave LeadingWave.FullModulation
open RawPrimary.AmplitudeGrades.Polynomial
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame AmbientResponse ResponseTransfer

/-- The retained initializer's leading and correction covector budgets produce
the five actual coefficient profiles required by corrected slices and the
literal sampling kernels (`app:ch_waves:eq:WKB-grading`,
`app:ch_response:eq:current-atomic-amplitudes`). All constants precede the
immersion, original scalar, flow, history scale and derivative reserve. Reserve
sixteen is retained, including the free-covector derivative budget. -/
theorem exists_retainedPrimary_coefficient_profiles
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (I : Set (Euclidean (n - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j) :
    ∃ Pξ Pζ Clead Ccorr : ℕ → ℝ,
      (∀ j, 0 < Pξ j) ∧ (∀ j, 0 < Pζ j) ∧
      (∀ j, 0 < Clead j) ∧ (∀ j, 0 < Ccorr j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      ∀ (RF Rr rpar : ℕ) (L : ℝ), 1 ≤ L →
      14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I r Rr L Ar →
      let J := closedBall a ρ
      let O := ball a (2 * ρ)
      ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) O ∧
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) O ∧
      ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) O ∧
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) O ∧
      HasDerivativeProfile J (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Pξ ∧
      HasDerivativeProfile J (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L Clead ∧
      HasDerivativeProfile J (fullCorrectionPrincipalNormal T Q F row col Φ Y r) (rpar + 1) L Ccorr ∧
      HasDerivativeProfile J (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L Clead ∧
      HasDerivativeProfile J (fullCorrectionReconstruction T Q F row col Φ Y r) (rpar + 1) L Ccorr ∧
      ∀ j, ∀ w ∈ J,
        ‖iteratedFDeriv ℝ j (fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
          fderiv ℝ (phase T Q w.1) w.2.2) w‖ ≤ Pζ j * L ^ (j - 1 - (rpar + 2)) := by
  have hsmall : closedBall a ρ ⊆ closedBall a (2*ρ) :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨Pξ, hPξ, hξgrade⟩ := exists_fullPhase_gradient_grades (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (AF 4 + 1) hγ hκ AF hAF
  obtain ⟨Pζ, hPζ, hζgrade⟩ := exists_fullPhase_parameter_grades (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (AF 4 + 1) hγ hκ AF hAF
  obtain ⟨Ccorr, hCcorr, hcorrectionGrade⟩ := exists_fullCorrection_reconstruction_grades
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar Γ hAF hAr hΓ
  let Clead := fun j ↦ E j * (1 + AF (j+14) + Ar (j+14))
  have hClead (j) : 0 < Clead j := by
    dsimp [Clead]
    exact mul_pos (hE j) (by linarith [hAF (j+14), hAr (j+14)])
  refine ⟨Pξ, Pζ, Clead, Ccorr, hPξ, hPζ, hClead, hCcorr, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  have hFM : cNorm K 4 F ≤ AF 4 + 1 := by
    have hh := hpF 4
    have he : 4 - RF = 0 := by omega
    simp only [he, pow_zero, mul_one] at hh
    linarith
  have hpξ := (hξgrade F hF hi hrank hFM hmetric hnormal hlow RF rpar L hL hRF hpF).1
  have hpζ := (hζgrade F hF hi hrank hFM hmetric hnormal hlow RF rpar L hL hRF hpF).1
  obtain ⟨hν₁, hV₁, hpν₁, hpV₁⟩ := hcorrectionGrade F hF hi hrank hmetric hnormal hlow
    row col Φ Y r Ω hΩ hflow hb₁ hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hν₀, hV₀, hpν₀, hpV₀⟩ := fullLeading_profiles_of_retained_budget T Q F row col Φ Y r
    a hρ (ball_subset_closedBall.trans (hspace.trans hKU)) hphase hF hi hrank
    (hb₀.mono (ball_subset_closedBall.trans hflow)) hAF hAr (fun j ↦ (hE j).le)
    hleading hL hRF hRr hpF hpr
  exact ⟨hν₀, hν₁, hV₀, hV₁, hpξ, hpν₀, hpν₁, hpV₀, hpV₁, hpζ⟩

/-- Choose the retained coefficient profiles before the fixed cell geometry
is exposed by the initialized history. Only geometry is reordered; the exact
phase and reconstruction estimates remain those of the preceding theorem.
Consumer: `exists_common_initialized_history_primary_coefficient_profiles`
(`main:prop:current-scale`, `app:ch_waves:eq:WKB-grading`). -/
theorem exists_retainedPrimary_coefficient_profiles_before_geometry
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (I : Set (Euclidean (n - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j) :
    ∃ Pξ Pζ Clead Ccorr : ℕ → ℝ,
      (∀ j, 0 < Pξ j) ∧ (∀ j, 0 < Pζ j) ∧
      (∀ j, 0 < Clead j) ∧ (∀ j, 0 < Ccorr j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      closedBall a.1 (2 * ρ) ⊆ K → closedBall a (2 * ρ) ⊆ domain T →
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      ∀ (RF Rr rpar : ℕ) (L : ℝ), 1 ≤ L →
      14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I r Rr L Ar →
      let J := closedBall a ρ
      let O := ball a (2 * ρ)
      ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) O ∧
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) O ∧
      ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) O ∧
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) O ∧
      HasDerivativeProfile J (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Pξ ∧
      HasDerivativeProfile J (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L Clead ∧
      HasDerivativeProfile J (fullCorrectionPrincipalNormal T Q F row col Φ Y r) (rpar + 1) L Ccorr ∧
      HasDerivativeProfile J (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L Clead ∧
      HasDerivativeProfile J (fullCorrectionReconstruction T Q F row col Φ Y r) (rpar + 1) L Ccorr ∧
      ∀ j, ∀ w ∈ J,
        ‖iteratedFDeriv ℝ j (fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
          fderiv ℝ (phase T Q w.1) w.2.2) w‖ ≤ Pζ j * L ^ (j - 1 - (rpar + 2)) := by
  classical
  by_cases hgeometry : closedBall a.1 (2 * ρ) ⊆ K ∧ closedBall a (2 * ρ) ⊆ domain T
  · obtain ⟨Pξ, Pζ, Clead, Ccorr, hPξ, hPζ, hClead, hCcorr, hprofiles⟩ :=
      exists_retainedPrimary_coefficient_profiles (N := N) T a hρ hK hKU hball
        hgeometry.1 hgeometry.2 I hγ hκ AF Ar E Γ hAF hAr hE hΓ
    refine ⟨Pξ, Pζ, Clead, Ccorr, hPξ, hPζ, hClead, hCcorr, ?_⟩
    intro F hF hi hrank _ _
    exact hprofiles F hF hi hrank
  · refine ⟨fun _ ↦ 1, fun _ ↦ 1, fun _ ↦ 1, fun _ ↦ 1,
      fun _ ↦ zero_lt_one, fun _ ↦ zero_lt_one, fun _ ↦ zero_lt_one,
      fun _ ↦ zero_lt_one, ?_⟩
    intro F hF hi hrank hspace hphase
    exact (hgeometry ⟨hspace, hphase⟩).elim

end JanetCartan.CorrectedAtoms
