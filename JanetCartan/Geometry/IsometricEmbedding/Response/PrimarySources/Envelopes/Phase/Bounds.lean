module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Phase.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.Annular
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Phase

/-!
# Physical bounds for the retained full primary phase

The lower bound comes from the actual frozen momentum and the original
Hamilton family's primitive frame comparison. Higher physical jets come
from the sharp reserve-three phase estimate and the immersion profile.
Both apply on the entire supplied compact joint set; no carrier restriction,
new working ball, or phase-gradient hypothesis is introduced.
Consumer: `exists_retainedPhase_sourceGeometry`, for
`app:ch_response:prop:response-graded`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponsePrimarySources
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary.AmplitudeGrades ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Uniform bounds for the physical differential of the SAME full phase on
the entire retained compact set. The threshold is produced by PhaseChoice's
comparison with the nonzero frozen momentum; it is selected before the
current frame (`app:ch_response:thm:response-literal-transfer`). -/
theorem exists_fullPhase_differential_bounds
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJ : IsCompact J) (hJT : J ⊆ domain T) :
    ∃ a G δ : ℝ, 0 < a ∧ a < G ∧ 0 < δ ∧ δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ w ∈ J,
        a ≤ ‖fderiv ℝ (fun y ↦ phase T Q y w.2.2) w.1‖ ∧
        ‖fderiv ℝ (fun y ↦ phase T Q y w.2.2) w.1‖ ≤ G := by
  let ψ := (zeroEnergyInclusion (n := n)).comp physicalCovectorProjection
  have htarget : ψ '' J ⊆ T.target := by
    rintro _ ⟨w, hw, rfl⟩
    exact (inclusion_mem_ball T (w := (w.1, w.2.2))).mpr (hJT hw)
  obtain ⟨a, ha, b, hb, δ, hδ, hbound⟩ :=
    T.exists_compact_sectionEnergy_momentum_bounds (hJ.image ψ.continuous) htarget
  refine ⟨a, a + b + 1, min δ T.family.threshold, ha, by linarith,
    lt_min hδ T.family.threshold_pos, min_le_right _ _, ?_⟩
  intro Q hQ w hw
  have he : ‖fderiv ℝ (fun y ↦ phase T Q y w.2.2) w.1‖ =
      ‖(T.currentChart Q).chartMomentum (ψ w)‖ := by
    rw [← (InnerProductSpace.toDual ℝ (Euclidean n)).symm.norm_map]
    change ‖phaseGradient T Q w.1 w.2.2‖ = _
    rw [phaseGradient_eq_chartMomentum T Q (w := (w.1, w.2.2)) (hJT hw)]
    rfl
  rw [he]
  have h := hbound Q (hQ.trans_le (min_le_left _ _)) (ψ w) ⟨w, hw, rfl⟩
  exact ⟨h.1, h.2.trans (by linarith)⟩

/-- All physical phase grades are derived from the primitive immersion
profile, with the original `14 + (rpar + 2)` reserve unchanged. Constants
precede the immersion, its frame, every carrier and the varying slow scale
(`app:ch_response:prop:response-graded`, `app:ch_response:cor:current-atoms`). -/
theorem exists_fullPhase_physical_grades {N : ℕ}
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJ : IsCompact J) (hJT : J ⊆ domain T)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K 4 F ≤ M →
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (RF rpar : ℕ) (L : ℝ), 1 ≤ L → 14 + (rpar + 2) ≤ RF →
      HasDerivativeProfile K F RF L AF →
      ∀ w ∈ J, ∀ j : ℕ,
        ‖iteratedFDeriv ℝ (j + 1) (fun y ↦ phase T Q y w.2.2) w.1‖ ≤ B j * L ^ j := by
  obtain ⟨A, hA, hbound⟩ := exists_phase_joint_projected_sharp_bound
    (N := N) T hJ hJT hK hKU hball M hγ hκ
  refine ⟨fun j ↦ A (j + 1) * (1 + AF (j + 1 + 3)),
    fun j ↦ mul_pos (hA _) (by have := hAF (j + 1 + 3); positivity), ?_⟩
  intro F hF hi hrank hFM hmetric hnormal hlow Q RF rpar L hL hRF hprofile w hw j
  have hS := RawPrimary.contDiffOn_fullPhase T Q (Ω := domain T) (fun _ h ↦ h)
  have hp : HasDerivativeProfile J
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ phase T Q w.1 w.2.2)
      1 L (fun k ↦ A k * (1 + AF (k + 3))) := by
    intro k
    exact JointBudget.fixed_profile_transfer_bound hL (hAF _) (hA k).le
      (by omega : 3 + 1 ≤ RF) (hprofile (k + 3))
      (hbound F hF hi hrank hFM hmetric hnormal hlow k)
  exact (norm_iteratedFDeriv_physical_slice_le (isOpen_domain T) hS (hJT hw) (j + 1)).trans
    (by simpa only [Nat.add_sub_cancel] using
      norm_iteratedFDeriv_le_profile hJ (isOpen_domain T) hJT hS hp (j + 1) hw)

end JanetCartan.ResponsePrimarySources
