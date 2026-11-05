module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FiniteJetSlices.Reconstruction

/-!
# Additive high bounds for the same correction reconstruction

The retained correction covector's actual reserve-fourteen budget feeds the
canonical ambient reconstruction. Its one covector derivative gives reserve
fifteen. Fixed order-fifteen bounds suffice for the constants; every higher
immersion and scalar seminorm stays explicit. Both original quadratures and
the full free carrier parameter are retained.

Consumers: all-order raw amplitude estimates, the preparation discrepancy,
and the fixed offset in `app:ch_response:cor:current-atoms`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.CorrectedAtoms
open RawPrimary RawPrimary.AmplitudeGrades
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer

/-- The actual correction reconstruction has one high immersion/scalar norm
and fixed reserve fifteen. Only the order-fifteen input budgets enter the
constants. The complete correction covector is the one produced by the
retained scalar construction, with both quadratures unchanged
(`app:ch_response:eq:current-atomic-offset`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_fullCorrection_reconstruction_tameBounds
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
    (M Mr : ℝ) (hM : 0 ≤ M) (hMr : 0 ≤ Mr)
    (Γ : ℕ → ℝ) (hΓ : ∀ j, 0 < Γ j) :
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
      cNorm K 15 F ≤ M → cNorm I 15 r ≤ Mr →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) (ball a (2 * ρ)) ∧
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) (ball a (2 * ρ)) ∧
      ∀ j, cNorm (closedBall a ρ) j (fullCorrectionPrincipalNormal T Q F row col Φ Y r) +
        cNorm (closedBall a ρ) j (fullCorrectionReconstruction T Q F row col Φ Y r) ≤
          C j * (1 + cNorm K (j+15) F + cNorm I (j+15) r) := by
  have hsmall : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hsmallx : closedBall a.1 ρ ⊆ K :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hspace
  obtain ⟨A, hA, hξbound⟩ := exists_phaseGradient_projected_sharp_bound (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (M+1) hγ hκ
  let B := Γ 1 * (1 + M + Mr) + A 1 * (1 + M)
  obtain ⟨D, hD, hbound⟩ := exists_cNorm_complex_reconstruction_le_of_primitive_bounds
    (N := N) a hρ (by linarith : 0 < M+1) hγ hκ B
  refine ⟨fun j ↦ D j * (1 + Γ (j+1) + A j),
    fun j ↦ mul_pos (hD j) (by have := hΓ (j+1); have := hA j; positivity), ?_⟩
  intro F hF hi hrank hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro row col Φ Y r Ω hΩ hflow hb hFM hrM hbudget
  let b := fullCorrectionCovector T Q F row col Φ Y r
  let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ phaseGradient T Q w.1 w.2.2
  have hFM4 : cNorm K 4 F ≤ M+1 := (cNorm_mono_order (by omega : 4 ≤ 15)).trans
    (hFM.trans (by linarith))
  have hpξ (j : ℕ) : cNorm (closedBall a ρ) j ξ ≤ A j * (1 + cNorm K (j+4) F) :=
    hξbound F hF hi hrank hFM4 hmetric hnormal hlow j
  have hbLow : cNorm (closedBall a ρ) 1 b ≤ B := by
    have hh := (hbudget 1).trans (mul_le_mul_of_nonneg_left
      (show 1 + cNorm K (1+14) F + cNorm I (1+14) r ≤ 1 + M + Mr by linarith) (hΓ 1).le)
    dsimp [B]
    have : 0 ≤ A 1 * (1 + M) := mul_nonneg (hA 1).le (by linarith)
    linarith
  have hξLow : cNorm (closedBall a ρ) 1 ξ ≤ B := by
    have hh := (hpξ 1).trans (mul_le_mul_of_nonneg_left
      (show 1 + cNorm K (1+4) F ≤ 1 + M by
        linarith [cNorm_mono_order (s := K) (f := F) (by omega : 5 ≤ 15)]) (hA 1).le)
    dsimp [B]
    have : 0 ≤ Γ 1 * (1 + M + Mr) := mul_nonneg (hΓ 1).le (by linarith)
    linarith
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
  refine ⟨by rwa [hprod] at hn, by rwa [hprod] at hv, ?_⟩
  intro j
  have hFmono (k : ℕ) : cNorm (closedBall a.1 ρ) k F ≤ cNorm K k F :=
    cNorm_mono_set_of_contDiffAt hsmallx hK
      (fun x hx ↦ (hF.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
  have hh := hbound (ball a.1 (2 * ρ)) (ball a.2 (2 * ρ)) isOpen_ball isOpen_ball
    (closedBall_subset_ball (by linarith : ρ < 2 * ρ))
    (closedBall_subset_ball (by linarith : ρ < 2 * ρ)) F b ξ
    (hF.mono hXU) (fun x hx ↦ hi x (hXU hx)) (fun x hx ↦ hrank x (hXU hx)) hb' hξ'
    ((hFmono 4).trans hFM4) (fun x hx ↦ hmetric x (hsmallx hx))
    (fun x hx ↦ hnormal x (hsmallx hx)) hbLow hξLow j
  let H := 1 + cNorm K (j+15) F + cNorm I (j+15) r
  have hFhigh : 1 + cNorm (closedBall a.1 ρ) (j+2) F ≤ H := by
    have hh := (hFmono (j+2)).trans (cNorm_mono_order (by omega : j+2 ≤ j+15))
    dsimp [H]
    linarith [cNorm_nonneg I (j+15) r]
  have hbhigh : cNorm (closedBall a ρ) (j+1) b ≤ Γ (j+1) * H := by
    simpa only [H, Nat.add_assoc, Nat.reduceAdd] using hbudget (j+1)
  have hξhigh : cNorm (closedBall a ρ) j ξ ≤ A j * H := by
    apply (hpξ j).trans
    apply mul_le_mul_of_nonneg_left _ (hA j).le
    dsimp [H]
    linarith [cNorm_mono_order (s := K) (f := F) (by omega : j+4 ≤ j+15),
      cNorm_nonneg I (j+15) r]
  apply hh.trans
  calc
    _ ≤ D j * ((1 + Γ (j+1) + A j) * H) := by
      apply mul_le_mul_of_nonneg_left _ (hD j).le
      nlinarith
    _ = _ := by dsimp [H]; ring

end JanetCartan.CorrectedAtoms
