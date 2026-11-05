module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.LeadingProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.ActualFamily

/-!
# Actual ambient amplitude grades from retained corrected-family outputs

This is the quantitative deduction from the SAME corrected-family producer,
not a new family selection. Its inputs are the primitive geometric gaps,
original immersion/scalar profiles, and the producer's literal real-leading
and correction-covector budgets. Ambient correction profiles are reconstructed
here, and the exact polynomial then gives the displacement, derivative and
leading-error grades. The reserve stays fourteen; reconstruction and final
differentiation spend the additional `r_par+2` allowance.

Consumers are `cNorm_rawPrimaryDemodulatedIntegral_le`,
`SliceBounds.exists_rawPhysicalSliceSobolev_wkbGrades`, and the final
`fullPrimaryWave` construction. The parent retains the initialized common-history
instantiation and the slice normal-data geometry. Sources:
`app:ch_waves:thm:wkb`, `app:ch_waves:eq:WKB-amplitude-difference`,
`app:ch_waves:eq:graded-phase`, and `app:ch_waves:eq:individual-grading`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer
open JanetCartan.RawPrimary.AmplitudeGrades.Polynomial

/-- The working-ball geometry needed below is a consequence of the exact
`hstatic` outputs retained by `exists_finite_actual_corrected_family`. Use
`ρ = σ j`, `R = 2 * ρ j` there; its smaller-ball containment supplies
`hsmall`. Thus this assembly adds no physical-domain premise
(`app:ch_waves:thm:wkb`). -/
theorem correctedFamily_workingBall_geometry
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ R : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)}
    (hsmall : closedBall a (2 * ρ) ⊆ closedBall a R)
    (hphase : closedBall a R ⊆ domain T)
    (hspace : MapsTo Prod.fst (closedBall a R)
      (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
        (ball (0 : Euclidean n) T.physicalRadius ∩ interior K))) :
    closedBall a.1 (2 * ρ) ⊆ K ∧ closedBall a (2 * ρ) ⊆ domain T := by
  refine ⟨?_, hsmall.trans hphase⟩
  intro x hx
  have hp : (x, a.2) ∈ closedBall a (2 * ρ) := by
    rw [← closedBall_prod_same a.1 a.2 (2 * ρ)]
    exact ⟨hx, mem_closedBall_self (by positivity)⟩
  exact interior_subset (hspace (hsmall hp)).2.2

/-- Joint and mixed amplitude grades of the SAME corrected atom. All constants
precede the immersion, flow, initial scalar, scale and frequency. `hleading` is
the five-term real leading budget and `hcorrection` is the reserve-fourteen
covector budget of `exists_finite_actual_corrected_family`. Its smooth leading
covector and correction supply `hb₀` and `hb₁`, and its doubled working ball
supplies the flow buffer. No desired ambient grade is an input.

The strongest retained baselines are `rpar+1` for displacement, `rpar` for
derivative/error and `rpar+3` for both phase covectors. They imply the requested
`τ L^s`, `L^s`, `τ L^s` bounds for every `k ≤ rpar`, and `L^(s-1)` for the phase
covectors when `s ≥ 1`. They meet the proved weaker slice endpoint without
increasing the manuscript reserve (`app:ch_waves:thm:wkb`). -/
theorem exists_fullAmplitude_grades_of_corrected_family_outputs
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
    ∃ C Pξ Pζ : ℕ → ℝ, (∀ j, 0 < C j) ∧ (∀ j, 0 < Pξ j) ∧ (∀ j, 0 < Pζ j) ∧
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
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      let J := closedBall a ρ
      let D := fullDisplacementAmplitude T Q F row col Φ Y r τ
      let A := fullDerivativeAmplitude T Q F row col Φ Y r τ
      let R := fun w ↦ A w - fullLeadingPrincipalMatrix T Q F row col Φ Y r w
      let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        phaseGradient T Q w.1 w.2.2
      let ζ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        fderiv ℝ (phase T Q w.1) w.2.2
      ContDiffOn ℝ ∞ D (ball a (2 * ρ)) ∧ ContDiffOn ℝ ∞ A (ball a (2 * ρ)) ∧
      (∀ j, ∀ w ∈ J,
        ‖iteratedFDeriv ℝ j D w‖ ≤ τ * C j * L ^ (j - (rpar + 1)) ∧
        ‖iteratedFDeriv ℝ j A w‖ ≤ C j * L ^ (j - rpar) ∧
        ‖iteratedFDeriv ℝ j R w‖ ≤ τ * C j * L ^ (j - rpar)) ∧
      (∀ s k : ℕ, k ≤ rpar → ∀ w ∈ J,
        ‖iteratedFDeriv ℝ (s + k) D w‖ ≤ τ * C (s + k) * L ^ s ∧
        ‖iteratedFDeriv ℝ (s + k) A w‖ ≤ C (s + k) * L ^ s ∧
        ‖iteratedFDeriv ℝ (s + k) R w‖ ≤ τ * C (s + k) * L ^ s) ∧
      (∀ s : ℕ, ∀ w ∈ J,
        ‖iteratedFDeriv ℝ s (fun x ↦ D (x, w.2)) w.1‖ ≤ τ * C s * L ^ s ∧
        ‖iteratedFDeriv ℝ s (fun x ↦ A (x, w.2)) w.1‖ ≤ C s * L ^ s ∧
        ‖iteratedFDeriv ℝ s (fun x ↦ R (x, w.2)) w.1‖ ≤ τ * C s * L ^ s) ∧
      HasDerivativeProfile J D (rpar + 1) L (fun j ↦ τ * ∑ i ∈ Finset.range (j + 1), C i) ∧
      HasDerivativeProfile J A rpar L (fun j ↦ ∑ i ∈ Finset.range (j + 1), C i) ∧
      HasDerivativeProfile J R rpar L (fun j ↦ τ * ∑ i ∈ Finset.range (j + 1), C i) ∧
      HasDerivativeProfile J ξ (rpar + 3) L Pξ ∧
      (∀ j, ∀ w ∈ J, ‖iteratedFDeriv ℝ j ζ w‖ ≤ Pζ j * L ^ (j - 1 - (rpar + 2))) ∧
      (∀ s k : ℕ, 1 ≤ s → k ≤ rpar → ∀ w ∈ J,
        ‖iteratedFDeriv ℝ (s + k) ξ w‖ ≤ Pξ (s + k) * L ^ (s - 1) ∧
        ‖iteratedFDeriv ℝ (s + k) ζ w‖ ≤ Pζ (s + k) * L ^ (s - 1)) ∧
      (∀ s : ℕ, 1 ≤ s → ∀ w ∈ J,
        ‖iteratedFDeriv ℝ s (fun x ↦ fderiv ℝ (phase T Q x) w.2.2) w.1‖ ≤
          Pζ s * L ^ (s - 1)) := by
  have hsmall : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hJΩ : closedBall a ρ ⊆ ball a (2 * ρ) := closedBall_subset_ball (by linarith)
  obtain ⟨Pξ, hPξ, hξgrade⟩ := exists_fullPhase_gradient_grades (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (AF 4 + 1) hγ hκ AF hAF
  obtain ⟨Pζ, hPζ, hζgrade⟩ := exists_fullPhase_parameter_grades (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (AF 4 + 1) hγ hκ AF hAF
  obtain ⟨B, hB, hcorrectionGrade⟩ := exists_fullCorrection_reconstruction_grades
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar Γ hAF hAr hΓ
  let A₀ := fun j ↦ E j * (1 + AF (j + 14) + Ar (j + 14))
  have hA₀ (j) : 0 ≤ A₀ j := by
    dsimp [A₀]; have := hAF (j + 14); have := hAr (j + 14); have := hE j; positivity
  have hc := polynomialProfiles_nonneg n N (fun j ↦ (hPξ j).le) hA₀
    (fun j ↦ (hB j).le) hA₀ (fun j ↦ (hB j).le)
  let C := fun j ↦ 1 + displacementProfile A₀ B A₀ B j +
    derivativeProfile n N Pξ A₀ B A₀ B j + errorProfile n N Pξ A₀ B A₀ B j
  have hC (j) : 0 < C j := by
    have := hc j
    dsimp only [C]
    linarith [this.1, this.2.2.2.1, this.2.2.2.2]
  have hdC (j) : displacementProfile A₀ B A₀ B j ≤ C j := by
    have := hc j
    dsimp only [C]
    linarith [this.2.2.2.1, this.2.2.2.2]
  have haC (j) : derivativeProfile n N Pξ A₀ B A₀ B j ≤ C j := by
    have := hc j
    dsimp only [C]
    linarith [this.1, this.2.2.2.1]
  have hrC (j) : errorProfile n N Pξ A₀ B A₀ B j ≤ C j := by
    have := hc j
    dsimp only [C]
    linarith [this.1, this.2.2.2.2]
  refine ⟨C, Pξ, Pζ, hC, hPξ, hPζ, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro row col Φ Y r Ω hΩ hflow hb₀ hb₁ hleading hcorrection
    RF Rr rpar L hL hRF hRr hpF hpr τ hτ hτ1
  have hFM : cNorm K 4 F ≤ AF 4 + 1 := by
    have hh := hpF 4
    have he : 4 - RF = 0 := by omega
    simp only [he, pow_zero, mul_one] at hh
    linarith
  obtain ⟨hpξ, hjξ⟩ := hξgrade F hF hi hrank hFM hmetric hnormal hlow RF rpar L hL hRF hpF
  obtain ⟨hjζ, hmζ, hxζ⟩ := hζgrade F hF hi hrank hFM hmetric hnormal hlow RF rpar L hL hRF hpF
  obtain ⟨hν₁, hV₁, hpν₁, hpV₁⟩ := hcorrectionGrade F hF hi hrank hmetric hnormal hlow
    row col Φ Y r Ω hΩ hflow hb₁ hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hν₀, hV₀, hpν₀, hpV₀⟩ := fullLeading_profiles_of_retained_budget T Q F row col Φ Y r
    a hρ (ball_subset_closedBall.trans (hspace.trans hKU)) hphase hF hi hrank
    (hb₀.mono (ball_subset_closedBall.trans hflow)) hAF hAr (fun j ↦ (hE j).le)
    hleading hL hRF hRr hpF hpr
  have hphase' : ∀ w ∈ ball a (2 * ρ), (w.1, w.2.2) ∈ phaseDomain T :=
    fun _ hw ↦ hphase (ball_subset_closedBall hw)
  have hs := contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r isOpen_ball
    hphase' hν₀ hν₁ hV₀ hV₁ (ne_of_gt hτ)
  have hξsmooth : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) (ball a (2 * ρ)) :=
    (phaseGradient_joint_smooth T Q).mono (ball_subset_closedBall.trans hphase)
  have hprincipal : ContDiffOn ℝ ∞ (fullLeadingPrincipalMatrix T Q F row col Φ Y r)
      (ball a (2 * ρ)) :=
    (contDiffOn_normalTensor hξsmooth hν₀).neg.congr
      (fun w _ ↦ fullLeadingPrincipalMatrix_eq_tensor T Q F row col Φ Y r w)
  have hj (j : ℕ) (w) (hw : w ∈ closedBall a ρ) :
      ‖iteratedFDeriv ℝ j (fullDisplacementAmplitude T Q F row col Φ Y r τ) w‖ ≤
          τ * C j * L ^ (j - (rpar + 1)) ∧
        ‖iteratedFDeriv ℝ j (fullDerivativeAmplitude T Q F row col Φ Y r τ) w‖ ≤
          C j * L ^ (j - rpar) ∧
        ‖iteratedFDeriv ℝ j (fun y ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ y -
          fullLeadingPrincipalMatrix T Q F row col Φ Y r y) w‖ ≤
          τ * C j * L ^ (j - rpar) := by
    have hh := full_amplitude_joint_bounds T Q F row col Φ Y r (isCompact_closedBall a ρ)
      isOpen_ball hJΩ hphase' hν₀ hν₁ hV₀ hV₁ (fun j ↦ (hPξ j).le) hA₀
      (fun j ↦ (hB j).le) hA₀ (fun j ↦ (hB j).le) hτ hτ1 hL
      hpξ hpν₀ hpν₁ hpV₀ hpV₁ j hw
    refine ⟨hh.1.trans ?_, hh.2.1.trans ?_, hh.2.2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdC j) hτ.le)
        (pow_nonneg (le_trans zero_le_one hL) _)
    · exact mul_le_mul_of_nonneg_right (haC j) (pow_nonneg (le_trans zero_le_one hL) _)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hrC j) hτ.le)
        (pow_nonneg (le_trans zero_le_one hL) _)
  refine ⟨hs.1, hs.2, hj, ?_, ?_, ?_, ?_, ?_, hpξ, hjζ, ?_, hxζ⟩
  · intro s k hk w hw
    have hh := hj (s + k) w hw
    exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by omega)) (mul_nonneg hτ.le (hC _).le)),
      hh.2.1.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by omega)) (hC _).le),
      hh.2.2.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by omega)) (mul_nonneg hτ.le (hC _).le))⟩
  · intro s w hw
    have hh := hj s w hw
    refine ⟨(norm_iteratedFDeriv_physical_slice_le isOpen_ball hs.1 (hJΩ hw) s).trans
      (hh.1.trans ?_),
      (norm_iteratedFDeriv_physical_slice_le isOpen_ball hs.2 (hJΩ hw) s).trans
      (hh.2.1.trans ?_),
      (norm_iteratedFDeriv_physical_slice_le isOpen_ball (hs.2.sub hprincipal) (hJΩ hw) s).trans
      (hh.2.2.trans ?_)⟩
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (mul_nonneg hτ.le (hC _).le)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (hC _).le
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (mul_nonneg hτ.le (hC _).le)
  · exact profile_of_jet_bounds hL hτ.le (fun j ↦ (hC j).le) (fun j w hw ↦ (hj j w hw).1)
  · simpa only [one_mul] using profile_of_jet_bounds hL zero_le_one (fun j ↦ (hC j).le)
      (fun j w hw ↦ by simpa only [one_mul] using (hj j w hw).2.1)
  · exact profile_of_jet_bounds hL hτ.le (fun j ↦ (hC j).le) (fun j w hw ↦ (hj j w hw).2.2)
  · intro s k hs hk w hw
    exact ⟨hjξ s k hs hk w hw, hmζ s k hs hk w hw⟩

end JanetCartan.RawPrimary.AmplitudeGrades
