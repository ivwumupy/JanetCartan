module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.JointPolynomial
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedGrades.Constants

/-!
# Joint homotopy budgets on the retained raw family

Apply the actual ambient reconstruction producers to the SAME selected cells,
minors, flows and initial scalar of `RetainedCorrection`. The input covector
budgets are precisely its retained outputs. The conclusion supplies all joint
inverse-frequency jets of the actual polynomial, including the zero endpoint.

For the sampling input reserve `M = 20*(n+1)`, choose `rpar = M+1` and original
map/scalar profile orders at least `M+17`. Thus the extra parameter derivative
uses fixed higher profiles; a C14 bound alone is never substituted for them.
The consumer is the nonzero measured amplitude of `UniformNormalData`, for
`app:ch_waves:eq:sampling-operator-bounds` and
`app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer

/-- Construct the original polynomial's joint homotopy bounds by applying
phase, leading and correction reconstruction to the retained covector outputs.
Constants precede every varying field, frequency and scale. The same witnesses
of `RetainedCorrection.exists_finite_retained_corrected_family_before_geometry`
supply `hb₀`, `hb₁`, `hleading`, and `hcorrection`; this theorem selects no new
chart, minor, flow, or reference (`app:ch_waves:setup:oscillatory`). -/
theorem exists_retained_jointPolynomial_budgets
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
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
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
      let poly := fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦
        derivativePolynomial q.1 (fun w ↦ phaseGradient T Q w.1 w.2.2)
          (fullLeadingNormal T Q F row col Φ Y r)
          (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
          (fullLeadingReconstruction T Q F row col Φ Y r)
          (fullCorrectionReconstruction T Q F row col Φ Y r) q.2
      ContDiffOn ℝ ∞ poly (univ ×ˢ ball a (2 * ρ)) ∧
        ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w ∈ closedBall a ρ, ∀ j,
          ‖iteratedFDeriv ℝ j poly (τ, w)‖ ≤ A j * L ^ (j - rpar) := by
  have hsmall : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hJΩ : closedBall a ρ ⊆ ball a (2 * ρ) := closedBall_subset_ball (by linarith)
  obtain ⟨Pξ, hPξ, hξgrade⟩ := exists_fullPhase_gradient_grades (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (AF 4 + 1) hγ hκ AF hAF
  obtain ⟨B, hB, hcorrectionGrade⟩ := exists_fullCorrection_reconstruction_grades
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar Γ hAF hAr hΓ
  let A₀ := fun j ↦ E j * (1 + AF (j + 14) + Ar (j + 14))
  have hA₀ (j) : 0 ≤ A₀ j := by
    dsimp [A₀]; have := hAF (j + 14); have := hAr (j + 14); have := hE j; positivity
  let A := jointPolynomialBudget n N Pξ A₀ B A₀ B
  have hA (j) : 0 ≤ A j := jointPolynomialBudget_nonneg n N
    (fun j ↦ (hPξ j).le) hA₀ (fun j ↦ (hB j).le) hA₀ (fun j ↦ (hB j).le) j
  refine ⟨fun j ↦ 1 + A j, fun j ↦ by linarith [hA j], ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection
    RF Rr rpar L hL hRF hRr hpF hpr
  have hFM : cNorm K 4 F ≤ AF 4 + 1 := by
    have hh := hpF 4
    have he : 4 - RF = 0 := by omega
    simp only [he, pow_zero, mul_one] at hh
    linarith
  obtain ⟨hpξ, _hjξ⟩ := hξgrade F hF hi hrank hFM hmetric hnormal hlow RF rpar L hL hRF hpF
  obtain ⟨hν₁, hV₁, hpν₁, hpV₁⟩ := hcorrectionGrade F hF hi hrank hmetric hnormal hlow
    row col Φ Y r Ω hΩ hflow hb₁ hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hν₀, hV₀, hpν₀, hpV₀⟩ := fullLeading_profiles_of_retained_budget T Q F row col Φ Y r
    a hρ (ball_subset_closedBall.trans (hspace.trans hKU)) hphase hF hi hrank
    (hb₀.mono (ball_subset_closedBall.trans hflow)) hAF hAr (fun j ↦ (hE j).le)
    hleading hL hRF hRr hpF hpr
  have hξ : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) (ball a (2 * ρ)) :=
    (phaseGradient_joint_smooth T Q).mono (ball_subset_closedBall.trans hphase)
  refine ⟨contDiffOn_joint_derivativePolynomial isOpen_ball hξ hν₀ hν₁ hV₀ hV₁, ?_⟩
  intro τ hτ w hw j
  have hjξ := fun k ↦ norm_iteratedFDeriv_le_profile (isCompact_closedBall a ρ)
    isOpen_ball hJΩ hξ hpξ k hw
  have hjν₀ := fun k ↦ norm_iteratedFDeriv_le_profile (isCompact_closedBall a ρ)
    isOpen_ball hJΩ hν₀ hpν₀ k hw
  have hjν₁ := fun k ↦ norm_iteratedFDeriv_le_profile (isCompact_closedBall a ρ)
    isOpen_ball hJΩ hν₁ hpν₁ k hw
  have hjV₀ := fun k ↦ norm_iteratedFDeriv_le_profile (isCompact_closedBall a ρ)
    isOpen_ball hJΩ hV₀ hpV₀ k hw
  have hjV₁ := fun k ↦ norm_iteratedFDeriv_le_profile (isCompact_closedBall a ρ)
    isOpen_ball hJΩ hV₁ hpV₁ k hw
  exact (norm_joint_derivativePolynomial_le isOpen_ball hξ hν₀ hν₁ hV₀ hV₁ (hJΩ hw)
    hτ hL (fun k ↦ (hPξ k).le) hA₀ (fun k ↦ (hB k).le) hA₀ (fun k ↦ (hB k).le)
    hjξ hjν₀ hjν₁ hjV₀ hjV₁ j).trans (mul_le_mul_of_nonneg_right
      (by dsimp [A]; linarith) (pow_nonneg (le_trans zero_le_one hL) _))

end JanetCartan.Sampling.MeasuredAmplitude
