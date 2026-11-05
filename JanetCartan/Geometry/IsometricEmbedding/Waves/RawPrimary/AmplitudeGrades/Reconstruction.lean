module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Reconstruction.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ActualReconstruction

/-!
# Grades of the actual ambient correction

For `app:ch_waves:eq:primary-algebraic-correction` and
`app:ch_waves:eq:exact-W-amplitude`, use the SAME correction covector, phase
and canonical ambient reconstruction as the literal full amplitudes.

The sole correction estimate below is the reserve-fourteen budget exported
by `exists_finite_actual_corrected_family`. Its original immersion
and initial-scalar profiles supply the fixed order-15 bounds. The phase
profile is derived from the SAME projected stress and primitive geometry.
Reconstruction loses one derivative of the correction, giving baseline
`rpar + 1`; the polynomial consumer retains one further derivative. The
parent must instantiate the actual corrected-family budget and smoothness,
and retains the stronger differentiated-slice compatibility obligation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer

/-- The SAME correction's ambient coefficients have joint baseline `rpar+1`.
All constants precede the immersion, flow, initial scalar, scale and frequency.
The producer of `hbudget` and `hb` is
`exists_finite_actual_corrected_family`; the doubled ball is its
retained buffer in the actual open flow domain. The phase gradient estimate
is instantiated here from primitive geometry, not assumed as an ambient
coefficient bound (`app:ch_waves:eq:WKB-amplitude-difference`,
`app:ch_waves:thm:wkb`). -/
theorem exists_fullCorrection_reconstruction_grades
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
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hΓ : ∀ j, 0 < Γ j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
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
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      ∀ (RF Rr rpar : ℕ) (L : ℝ), 1 ≤ L →
      14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I r Rr L Ar →
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) (ball a (2 * ρ)) ∧
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) (ball a (2 * ρ)) ∧
      HasDerivativeProfile (closedBall a ρ)
        (fullCorrectionPrincipalNormal T Q F row col Φ Y r) (rpar + 1) L C ∧
      HasDerivativeProfile (closedBall a ρ)
        (fullCorrectionReconstruction T Q F row col Φ Y r) (rpar + 1) L C := by
  have hsmall : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hsmallx : closedBall a.1 ρ ⊆ K :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hspace
  let M := AF 4 + 1
  have hM : 0 < M := by dsimp [M]; have := hAF 4; positivity
  obtain ⟨Aξ, hAξ, hξgrade⟩ := exists_fullPhase_gradient_grades (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball M hγ hκ AF hAF
  let Ab := fun j ↦ Γ j * (1 + AF (j + 14) + Ar (j + 14))
  have hAb (j) : 0 ≤ Ab j := by
    dsimp [Ab]; have := hAF (j + 14); have := hAr (j + 14); have := hΓ j; positivity
  obtain ⟨D, hD, hbound⟩ := exists_cNorm_complex_reconstruction_le_of_primitive_bounds
    (N := N) a hρ hM hγ hκ (Ab 1 + Aξ 1)
  refine ⟨fun j ↦ D j * (1 + AF (j + 2) + Ab (j + 1) + Aξ j), ?_, ?_⟩
  · intro j
    exact mul_pos (hD j) (by have := hAF (j + 2); have := hAb (j + 1); have := hAξ j; positivity)
  intro F hF hi hrank hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro row col Φ Y r Ω hΩ hflow hb hbudget RF Rr rpar L hL hRF hRr hpF hpr
  let b := fullCorrectionCovector T Q F row col Φ Y r
  let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ phaseGradient T Q w.1 w.2.2
  have hFM : cNorm K 4 F ≤ M := by
    have hh := hpF 4
    have he : 4 - RF = 0 := by omega
    simp only [he, pow_zero, mul_one] at hh
    exact hh.trans (by dsimp [M]; linarith)
  have hpξ : HasDerivativeProfile (closedBall a ρ) ξ (rpar + 3) L Aξ :=
    (hξgrade F hF hi hrank hFM hmetric hnormal hlow RF rpar L hL hRF hpF).1
  have hpb : HasDerivativeProfile (closedBall a ρ) b (rpar + 2) L Ab :=
    profile_of_two_input_budget hpF hpr hL hAF hAr (fun j ↦ (hΓ j).le) hRF hRr hbudget
  have hbLow : cNorm (closedBall a ρ) 1 b ≤ Ab 1 := by
    simpa using hpb 1
  have hξLow : cNorm (closedBall a ρ) 1 ξ ≤ Aξ 1 := by
    simpa using hpξ 1
  have hXU : ball a.1 (2 * ρ) ⊆ U := ball_subset_closedBall.trans (hspace.trans hKU)
  have hprod : ball a.1 (2 * ρ) ×ˢ ball a.2 (2 * ρ) = ball a (2 * ρ) :=
    ball_prod_same a.1 a.2 (2 * ρ)
  have hb' : ContDiffOn ℝ ∞ b (ball a.1 (2 * ρ) ×ˢ ball a.2 (2 * ρ)) := by
    rw [hprod]; exact hb.mono (ball_subset_closedBall.trans hflow)
  have hξ' : ContDiffOn ℝ ∞ ξ (ball a.1 (2 * ρ) ×ˢ ball a.2 (2 * ρ)) := by
    rw [hprod]; exact (phaseGradient_joint_smooth T Q).mono (ball_subset_closedBall.trans hphase)
  have hn := contDiffOn_joint_canonicalPrincipalNormalComplex isOpen_ball isOpen_ball
    (hF.mono hXU) hb' hξ' (fun x hx ↦ hi x (hXU hx)) (fun x hx ↦ hrank x (hXU hx))
  have hv := contDiffOn_joint_completedVariationComplex_zero isOpen_ball isOpen_ball
    (hF.mono hXU) hb' (fun x hx ↦ hi x (hXU hx)) (fun x hx ↦ hrank x (hXU hx))
  have hprincipal : fullCorrectionPrincipalNormal T Q F row col Φ Y r =
      fun p ↦ canonicalPrincipalNormalComplex F p.1 (ξ p) (b p) := by
    funext p
    simp only [fullCorrectionPrincipalNormal, scalarDifferential_eq_gradient, ξ, phaseGradient, b]
  have hreconstruction : fullCorrectionReconstruction T Q F row col Φ Y r =
      fun p ↦ completedVariationComplex F (fun x ↦ b (x, p.2)) 0 p.1 := rfl
  rw [hprincipal, hreconstruction]
  refine ⟨by rwa [hprod] at hn, by rwa [hprod] at hv, ?_, ?_⟩
  all_goals
    intro j
    have hFmono (k : ℕ) : cNorm (closedBall a.1 ρ) k F ≤ cNorm K k F :=
      cNorm_mono_set_of_contDiffAt hsmallx hK
        (fun x hx ↦ (hF.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
    have hh := hbound (ball a.1 (2 * ρ)) (ball a.2 (2 * ρ)) isOpen_ball isOpen_ball
      (closedBall_subset_ball (by linarith : ρ < 2 * ρ))
      (closedBall_subset_ball (by linarith : ρ < 2 * ρ)) F b ξ
      (hF.mono hXU) (fun x hx ↦ hi x (hXU hx)) (fun x hx ↦ hrank x (hXU hx)) hb' hξ'
      ((hFmono 4).trans hFM) (fun x hx ↦ hmetric x (hsmallx hx))
      (fun x hx ↦ hnormal x (hsmallx hx))
      (hbLow.trans (le_add_of_nonneg_right (hAξ 1).le))
      (hξLow.trans (le_add_of_nonneg_left (hAb 1))) j
    have hFhigh : cNorm (closedBall a.1 ρ) (j + 2) F ≤ AF (j + 2) * L ^ (j - (rpar + 1)) :=
      ((hFmono (j + 2)).trans (hpF (j + 2))).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (hAF _))
    have hbhigh : cNorm (closedBall a ρ) (j + 1) b ≤ Ab (j + 1) * L ^ (j - (rpar + 1)) := by
      convert hpb (j + 1) using 1
      congr 2
      omega
    have hξhigh : cNorm (closedBall a ρ) j ξ ≤ Aξ j * L ^ (j - (rpar + 1)) :=
      (hpξ j).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (hAξ j).le)
    have htotal := hh.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add (one_le_pow₀ hL : 1 ≤ L ^ (j - (rpar + 1))) hFhigh) hbhigh) hξhigh) (hD j).le)
    have hn0 := cNorm_nonneg (closedBall a ρ) j
      (fun p ↦ canonicalPrincipalNormalComplex F p.1 (ξ p) (b p))
    have hv0 := cNorm_nonneg (closedBall a ρ) j
      (fun p ↦ completedVariationComplex F (fun x ↦ b (x, p.2)) 0 p.1)
    dsimp only
    nlinarith

end JanetCartan.RawPrimary.AmplitudeGrades
