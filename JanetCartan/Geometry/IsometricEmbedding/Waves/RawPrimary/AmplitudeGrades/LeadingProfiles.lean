module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Reconstruction

/-!
# Transfer of the retained real leading coefficients

The real normal and reconstruction in `exists_finite_actual_corrected_family`
are the coefficients of the literal complex WKB polynomial. Complex inclusion
costs no derivatives and no norm factor. This closes the leading input of
`exists_fullAmplitude_grades_of_corrected_family_outputs`, with reserve fourteen
and the additional `r_par+2` allowance of `app:ch_waves:thm:wkb`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseTransfer AmbientResponse
open JanetCartan.RawPrimary.AmplitudeGrades.Polynomial

private theorem middle_terms_le {u v w x y z : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : u + v + w + x + y ≤ z) : w ≤ z ∧ x ≤ z := by
  constructor <;> linarith

/-- Transfer the SAME retained real leading normal and reconstruction to their
literal complex coefficients. The sum in `hbudget` is exactly the leading
budget retained by `exists_finite_actual_corrected_family`; none of the complex
coefficient grades is assumed (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem fullLeading_profiles_of_retained_budget
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) {ρ : ℝ} (hρ : 0 < ρ)
    (hspace : ball a.1 (2 * ρ) ⊆ U) (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hb : ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) (ball a (2 * ρ)))
    {K : Set (Euclidean n)} {I : Set (Euclidean (n - 1) × Euclidean 3)}
    {AF Ar E : ℕ → ℝ} (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 ≤ E j)
    (hbudget : ∀ j,
      let J := closedBall a ρ
      let b₀ := fullLeadingCovector T Q F row col Φ Y r
      let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        phaseGradient T Q w.1 w.2.2
      let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
      let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
      cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
        cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
          E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r))
    {RF Rr rpar : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (hRF : 14 + (rpar + 2) ≤ RF) (hRr : 14 + (rpar + 2) ≤ Rr)
    (hpF : HasDerivativeProfile K F RF L AF) (hpr : HasDerivativeProfile I r Rr L Ar) :
    ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) (ball a (2 * ρ)) ∧
    ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) (ball a (2 * ρ)) ∧
    HasDerivativeProfile (closedBall a ρ) (fullLeadingNormal T Q F row col Φ Y r)
      (rpar + 2) L (fun j ↦ E j * (1 + AF (j + 14) + Ar (j + 14))) ∧
    HasDerivativeProfile (closedBall a ρ) (fullLeadingReconstruction T Q F row col Φ Y r)
      (rpar + 2) L (fun j ↦ E j * (1 + AF (j + 14) + Ar (j + 14))) := by
  let b₀ := fullLeadingCovector T Q F row col Φ Y r
  let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
    phaseGradient T Q w.1 w.2.2
  let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
  let V := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
    reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
  have hprod : ball a.1 (2 * ρ) ×ˢ ball a.2 (2 * ρ) = ball a (2 * ρ) :=
    ball_prod_same a.1 a.2 (2 * ρ)
  have hb' : ContDiffOn ℝ ∞ b₀ (ball a.1 (2 * ρ) ×ˢ ball a.2 (2 * ρ)) := by
    rwa [hprod]
  have hξ : ContDiffOn ℝ ∞ ξ (ball a.1 (2 * ρ) ×ˢ ball a.2 (2 * ρ)) := by
    rw [hprod]
    exact (phaseGradient_joint_smooth T Q).mono (ball_subset_closedBall.trans hphase)
  have hν : ContDiffOn ℝ ∞ ν (ball a (2 * ρ)) := by
    rw [← hprod]
    exact contDiffOn_joint_principalNormal_canonical isOpen_ball isOpen_ball
      (hF.mono hspace) hb' hξ (fun x hx ↦ hi x (hspace hx)) (fun x hx ↦ hrank x (hspace hx))
  have hV : ContDiffOn ℝ ∞ V (ball a (2 * ρ)) := by
    rw [← hprod]
    exact JointReconstruction.contDiffOn_joint_reconstruction_canonical isOpen_ball isOpen_ball
      (hF.mono hspace) hb' (fun x hx ↦ hi x (hspace hx)) (fun x hx ↦ hrank x (hspace hx))
  have heν : fullLeadingNormal T Q F row col Φ Y r = euclideanComplexInclusion ∘ ν := by
    funext w
    exact fullLeadingNormal_eq_inclusion T Q F row col Φ Y r w
  have heV : EqOn (fullLeadingReconstruction T Q F row col Φ Y r)
      (euclideanComplexInclusion ∘ V) (ball a (2 * ρ)) := by
    intro w hw
    exact fullLeadingReconstruction_eq_inclusion T Q F row col Φ Y r
      (((hb.contDiffAt (isOpen_ball.mem_nhds hw)).comp w.1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  have hsub : closedBall a ρ ⊆ ball a (2 * ρ) := closedBall_subset_ball (by linarith)
  have hn : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) (ball a (2 * ρ)) := by
    rw [heν]; exact euclideanComplexInclusion.contDiff.comp_contDiffOn hν
  have hv : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) (ball a (2 * ρ)) :=
    ((euclideanComplexInclusion (ι := Fin N)).contDiff.comp_contDiffOn hV).congr heV
  have hinc {f : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Euclidean N}
      (hf : ContDiffOn ℝ ∞ f (ball a (2 * ρ))) (j : ℕ) :
      cNorm (closedBall a ρ) j (euclideanComplexInclusion ∘ f) ≤ cNorm (closedBall a ρ) j f :=
    (FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on (isCompact_closedBall a ρ) j
      (euclideanComplexInclusion (ι := Fin N)) (fun w hw ↦
        (hf.contDiffAt (isOpen_ball.mem_nhds (hsub hw))).of_le (by simp))).trans
      (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (euclideanComplexInclusion_norm_le (ι := Fin N))
          (cNorm_nonneg (closedBall a ρ) j f))
  have hνbudget (j : ℕ) : cNorm (closedBall a ρ) j ν ≤
      E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r) :=
    (middle_terms_le
      (cNorm_nonneg (closedBall a ρ) j (fun w ↦ phase T Q w.1 w.2.2))
      (cNorm_nonneg (closedBall a ρ) j b₀) (cNorm_nonneg (closedBall a ρ) j ν)
      (cNorm_nonneg (closedBall a ρ) j V)
      (cNorm_nonneg (closedBall a ρ) j (fun w ↦ principalMatrix (ν w) (ξ w))) (hbudget j)).1
  have hVbudget (j : ℕ) : cNorm (closedBall a ρ) j V ≤
      E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r) :=
    (middle_terms_le
      (cNorm_nonneg (closedBall a ρ) j (fun w ↦ phase T Q w.1 w.2.2))
      (cNorm_nonneg (closedBall a ρ) j b₀) (cNorm_nonneg (closedBall a ρ) j ν)
      (cNorm_nonneg (closedBall a ρ) j V)
      (cNorm_nonneg (closedBall a ρ) j (fun w ↦ principalMatrix (ν w) (ξ w))) (hbudget j)).2
  refine ⟨hn, hv, ?_, ?_⟩
  · apply profile_of_two_input_budget hpF hpr hL hAF hAr hE hRF hRr
    intro j
    rw [heν]
    exact (hinc hν j).trans (hνbudget j)
  · apply profile_of_two_input_budget hpF hpr hL hAF hAr hE hRF hRr
    intro j
    rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun w hw ↦
      heV.eventuallyEq_of_mem (isOpen_ball.mem_nhds (hsub hw))) j]
    exact (hinc hV j).trans (hVbudget j)

end JanetCartan.RawPrimary.AmplitudeGrades
