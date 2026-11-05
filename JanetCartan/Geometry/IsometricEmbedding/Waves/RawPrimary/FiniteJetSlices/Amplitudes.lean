module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FiniteJetSlices.Leading
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FiniteJetSlices.Reconstruction

/-!
# Finite joint bounds from the retained primitive budgets

Consumer: the all-cutoff-scale raw slice estimate of
`app:ch_waves:eq:individual-raw-slice`. The immersion and scalar bounds
stop at a prescribed order. The original reserve fourteen is unchanged;
reconstruction and the derivative polynomial spend two additional orders.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RawPrimary.FiniteJetSlices
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer AmplitudeGrades AmplitudeGrades.Polynomial

/-- Finite amplitude and free-covector bounds for the SAME retained atom,
with constants before the immersion, scalar, flows and inverse frequency.
The primitive budgets are exactly those of `RetainedCorrection.Finite`.
No amplitude estimate or all-order bounded profile is assumed. Consumer:
`app:ch_waves:eq:individual-raw-slice` at each prescribed finite order. -/
theorem exists_fullAmplitude_finiteJets
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
    ∃ C Pζ : ℕ → ℝ, (∀ j, 0 < C j) ∧ (∀ j, 0 < Pζ j) ∧
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
      ∀ m : ℕ,
      (∀ j ≤ m + 1,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j ≤ m + 2, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j ≤ m + 16, cNorm K j F ≤ AF j) →
      (∀ j ≤ m + 16, cNorm I j r ≤ Ar j) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ContDiffOn ℝ ∞ (fullDerivativeAmplitude T Q F row col Φ Y r τ) (ball a (2 * ρ)) ∧
      (∀ j ≤ m, ∀ w ∈ closedBall a ρ,
        ‖iteratedFDeriv ℝ j (fullDerivativeAmplitude T Q F row col Φ Y r τ) w‖ ≤ C j) ∧
      (∀ j ≤ m, ∀ w ∈ closedBall a ρ,
        ‖iteratedFDeriv ℝ j
          (fun y : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦
            fderiv ℝ (phase T Q y.1) y.2.2) w‖ ≤ Pζ j) := by
  have hsmall : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hJΩ : closedBall a ρ ⊆ ball a (2 * ρ) := closedBall_subset_ball (by linarith)
  obtain ⟨X, hX, hξbound⟩ := exists_phaseGradient_projected_sharp_bound (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (AF 4 + 1) hγ hκ
  obtain ⟨Z, hZ, hSbound⟩ := exists_phase_joint_projected_sharp_bound (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (AF 4 + 1) hγ hκ
  obtain ⟨B, hB, hcorrection⟩ := exists_fullCorrection_reconstruction_finiteJets
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar Γ hAF hAr hΓ
  let Pξ := fun j ↦ X j * (1 + AF (j+4))
  let Pζ := fun j ↦ Z (j+1) * (1 + AF (j+1+3))
  let A₀ := fun j ↦ E j * (1 + AF (j+14) + Ar (j+14))
  have hPξ (j) : 0 ≤ Pξ j := mul_nonneg (hX j).le (by have := hAF (j+4); positivity)
  have hPζ (j) : 0 < Pζ j := mul_pos (hZ (j+1)) (by have := hAF (j+1+3); positivity)
  have hA₀ (j) : 0 ≤ A₀ j := by
    have := hAF (j+14); have := hAr (j+14); have := hE j
    dsimp [A₀]; positivity
  let C := fun j ↦ 1 + derivativeProfile n N Pξ A₀ B A₀ B j
  have hC (j) : 0 < C j := by
    have := (polynomialProfiles_nonneg n N hPξ hA₀ (fun j ↦ (hB j).le)
      hA₀ (fun j ↦ (hB j).le) j).2.2.2.2
    dsimp [C]; linarith
  refine ⟨C, Pζ, hC, hPζ, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro row col Φ Y r Ω hΩ hflow hb₀ hb₁ m hleading hcorrectionBudget hpF hpr τ hτ hτ1
  have hFM : cNorm K 4 F ≤ AF 4 + 1 := (hpF 4 (by omega)).trans (by linarith)
  obtain ⟨hν₁, hV₁, hpν₁, hpV₁⟩ := hcorrection F hF hi hrank hmetric hnormal hlow
    row col Φ Y r Ω hΩ hflow hb₁ m hcorrectionBudget hpF hpr
  obtain ⟨hν₀, hV₀, hpν₀, hpV₀⟩ := fullLeading_finite_of_retained_budget T Q F row col Φ Y r
    a hρ (ball_subset_closedBall.trans (hspace.trans hKU)) hphase hF hi hrank
    (hb₀.mono (ball_subset_closedBall.trans hflow)) m (fun j ↦ (hE j).le) hleading hpF hpr
  have hphase' : ∀ w ∈ ball a (2 * ρ), (w.1, w.2.2) ∈ phaseDomain T :=
    fun _ hw ↦ hphase (ball_subset_closedBall hw)
  have hs := contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r isOpen_ball
    hphase' hν₀ hν₁ hV₀ hV₁ (ne_of_gt hτ)
  have hpξ (j : ℕ) (hj : j ≤ m+1) :
      cNorm (closedBall a ρ) j (fun w ↦ phaseGradient T Q w.1 w.2.2) ≤ Pξ j :=
    (hξbound F hF hi hrank hFM hmetric hnormal hlow j).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) (hpF (j+4) (by omega))) (hX j).le)
  refine ⟨hs.2, ?_, ?_⟩
  · intro j hj w hw
    exact (fullDerivativeAmplitude_jet_le_finite_coefficients T Q F row col Φ Y r
      (isCompact_closedBall a ρ) isOpen_ball hJΩ hphase' hν₀ hν₁ hV₀ hV₁ hτ hτ1
      (fun k hk ↦ hpξ k (by omega)) (fun k hk ↦ hpν₀ k (by omega))
      (fun k hk ↦ hpν₁ k (by omega)) (fun k hk ↦ hpV₀ k (by omega))
      (fun k hk ↦ hpV₁ k (by omega)) hw).trans (by dsimp [C]; linarith)
  · intro j hj w hw
    apply (norm_iteratedFDeriv_fullPhase_parameter_fderiv_le T Q (hsmall.trans hphase hw) j).trans
    have hS := contDiffOn_fullPhase T Q (Ω := domain T) (fun _ h ↦ h)
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ (hS.contDiffAt ((isOpen_domain T).mem_nhds
        (hsmall.trans hphase hy))).of_le (by simp)) hw (le_refl (j+1))).trans
    exact (hSbound F hF hi hrank hFM hmetric hnormal hlow (j+1)).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) (hpF (j+1+3) (by omega))) (hZ _).le)

end JanetCartan.RawPrimary.FiniteJetSlices
