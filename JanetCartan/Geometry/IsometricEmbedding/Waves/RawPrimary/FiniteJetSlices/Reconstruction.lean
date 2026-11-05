module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Reconstruction.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ActualReconstruction

/-!
# Finite bounds for the actual ambient correction

Use the SAME correction covector, phase and canonical ambient reconstruction
as the literal full amplitudes in `app:ch_waves:eq:primary-algebraic-correction`
and `app:ch_waves:eq:exact-W-amplitude`.

The reserve-fourteen retained covector budget is used only through `m+2`.
Original immersion/scalar jets through `m+16` supply its low bounds and the
finite reconstruction bounds through `m+1`. The phase gradient is derived
from the SAME projected stress and primitive geometry. Both quadratures are
retained. Consumer: `exists_fullAmplitude_finiteJets`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.FiniteJetSlices
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer AmplitudeGrades

/-- Finite ambient reconstruction of BOTH quadratures of the retained correction.
Only primitive orders through `m+16` enter the coefficient bounds through
`m+1`. Consumer: `exists_fullAmplitude_finiteJets`; sources
`app:ch_waves:eq:exact-W-amplitude`, `app:ch_waves:eq:individual-raw-slice`. -/
theorem exists_fullCorrection_reconstruction_finiteJets
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
      ∀ m : ℕ,
      (∀ j ≤ m + 2, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j ≤ m + 16, cNorm K j F ≤ AF j) →
      (∀ j ≤ m + 16, cNorm I j r ≤ Ar j) →
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) (ball a (2 * ρ)) ∧
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) (ball a (2 * ρ)) ∧
      (∀ j ≤ m + 1, cNorm (closedBall a ρ) j
        (fullCorrectionPrincipalNormal T Q F row col Φ Y r) ≤ C j) ∧
      (∀ j ≤ m + 1, cNorm (closedBall a ρ) j
        (fullCorrectionReconstruction T Q F row col Φ Y r) ≤ C j) := by
  have hsmall : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hsmallx : closedBall a.1 ρ ⊆ K :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hspace
  let M := AF 4 + 1
  have hM : 0 < M := by dsimp [M]; have := hAF 4; positivity
  obtain ⟨A, hA, hξbound⟩ := exists_phaseGradient_projected_sharp_bound (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball M hγ hκ
  let Aξ := fun j ↦ A j * (1 + AF (j + 4))
  have hAξ (j) : 0 < Aξ j :=
    mul_pos (hA j) (by have := hAF (j+4); positivity)
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
  intro row col Φ Y r Ω hΩ hflow hb m hbudget hpF hpr
  let b := fullCorrectionCovector T Q F row col Φ Y r
  let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ phaseGradient T Q w.1 w.2.2
  have hFM : cNorm K 4 F ≤ M :=
    (hpF 4 (by omega)).trans (by dsimp [M]; linarith)
  have hpξ (j : ℕ) (hj : j ≤ m + 1) : cNorm (closedBall a ρ) j ξ ≤ Aξ j :=
    (hξbound F hF hi hrank hFM hmetric hnormal hlow j).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) (hpF (j+4) (by omega))) (hA j).le)
  have hpb (j : ℕ) (hj : j ≤ m + 2) : cNorm (closedBall a ρ) j b ≤ Ab j :=
    (hbudget j hj).trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (le_refl (1 : ℝ)) (hpF (j+14) (by omega)))
        (hpr (j+14) (by omega))) (hΓ j).le)
  have hbLow : cNorm (closedBall a ρ) 1 b ≤ Ab 1 := hpb 1 (by omega)
  have hξLow : cNorm (closedBall a ρ) 1 ξ ≤ Aξ 1 := hpξ 1 (by omega)
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
    intro j hj
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
    have hFhigh : cNorm (closedBall a.1 ρ) (j + 2) F ≤ AF (j + 2) :=
      (hFmono (j+2)).trans (hpF (j+2) (by omega))
    have hbhigh := hpb (j+1) (by omega)
    have hξhigh := hpξ j hj
    have htotal := hh.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add (le_refl (1 : ℝ)) hFhigh) hbhigh) hξhigh) (hD j).le)
    have hn0 := cNorm_nonneg (closedBall a ρ) j
      (fun p ↦ canonicalPrincipalNormalComplex F p.1 (ξ p) (b p))
    have hv0 := cNorm_nonneg (closedBall a ρ) j
      (fun p ↦ completedVariationComplex F (fun x ↦ b (x, p.2)) 0 p.1)
    linarith

end JanetCartan.RawPrimary.FiniteJetSlices
