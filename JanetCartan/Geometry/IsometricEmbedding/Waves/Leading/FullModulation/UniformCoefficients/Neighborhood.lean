module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.GapAlgebra
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Formulas

/-!
# Uniform full-covector neighborhoods from the existing carrier gap

The sole gap input is at the fixed center. A uniform first-derivative bound,
derived from primitive frame closeness, extends it to a ball of fixed radius.
This is the neighborhood producer for `app:ch_waves:thm:leading`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation.UniformCoefficients
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport.CoefficientBounds

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Choose a fixed closed full-modulation ball around the zero-time carrier
center, with physical room inside the construction compactum. This uses only
the original patch buffer (`app:ch_waves:thm:leading`). -/
theorem exists_carrier_center_ball {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius)
    {K : Set (Euclidean n)}
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ R > (0 : ℝ),
      closedBall (0, (z₀, T.reference.spatialPatch z₀)) R ⊆ domain T ∧
      MapsTo Prod.fst (closedBall (0, (z₀, T.reference.spatialPatch z₀)) R)
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) := by
  let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
    (0, (z₀, T.reference.spatialPatch z₀))
  let Ω := domain T ∩ Prod.fst ⁻¹'
    (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
      (ball (0 : Euclidean n) T.physicalRadius ∩ interior K))
  have hΩ : IsOpen Ω := (isOpen_domain T).inter
    ((isOpen_ball.inter (isOpen_ball.inter isOpen_interior)).preimage continuous_fst)
  have hstate : (0 : Euclidean n) ∈ ball 0 T.data.localReference.stateRadius :=
    mem_ball_self T.data.localReference.stateRadius_pos
  have hphysical : (0 : Euclidean n) ∈ ball 0 T.physicalRadius :=
    mem_ball_self T.physicalRadius_pos
  have hK : (0 : Euclidean n) ∈ interior K :=
    interior_maximal (ball_subset_closedBall.trans hball) isOpen_ball hstate
  have ha : a ∈ Ω := ⟨carrier_mem_phaseDomain T hphysical
    (fun i ↦ (hz₀ i).trans (by linarith [hP.1])), hstate, hphysical, hK⟩
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds ha)
  exact ⟨R, hR, fun w hw ↦ (hsub hw).1, fun w hw ↦ (hsub hw).2⟩

/-- Uniformly extend the existing center denominator gap without changing the
row or column. All constants and the radius precede the current frame. The
input bound is produced from phase continuity, not assumed
(`app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_uniform_denominator_neighborhood (hn : 2 ≤ n)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {R : ℝ} (hR : 0 < R)
    (hx : MapsTo Prod.fst (closedBall a R)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hballU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hdom : closedBall a R ⊆ domain T) (r c : Fin n) {g : ℝ} (hg : 0 < g) :
    ∃ δ ρ L b : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 < L ∧ 0 < b ∧ 2 * ρ ≤ R ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        g ≤ |adaptedDenominator T Q r c a| →
        cNorm (closedBall a (2 * ρ)) 1 (fullInput T Q) ≤ L ∧
        ∀ w ∈ closedBall a (2 * ρ),
          g / 2 ≤ |adaptedDenominator T Q r c w| ∧
          b ≤ ‖nullvector T Q c w‖ ∧ b ≤ ‖conullvector T Q r w‖ ∧
          b ≤ ‖phaseGradient T Q w.1 w.2.2‖ := by
  obtain ⟨δ, L, hδ, hL, hinput⟩ := exists_fullInput_low_bound T a R hx hballU hdom
  obtain ⟨C, hC, hcomp⟩ :=
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hR (isCompact_closedBall (0 : Input n) L) (r := 1) (k := 1) le_rfl
      (g := denominator T.data.adapted.normal r c)
      (fun _ _ ↦ (smooth_denominator T.data.adapted.normal r c).contDiffAt.of_le (by simp))
  let B := C * (1 + L)
  have hB : 0 < B := mul_pos hC (by linarith)
  let ρ := min (R / 2) (g / (4 * B))
  have hρ : 0 < ρ := lt_min (half_pos hR) (div_pos hg (by positivity))
  have hρR : 2 * ρ ≤ R := by have := min_le_left (R / 2) (g / (4 * B)); dsimp [ρ]; linarith
  have hρg : B * (2 * ρ) ≤ g / 2 := by
    have hh := min_le_right (R / 2) (g / (4 * B))
    have hmul : ρ * (4 * B) ≤ g := (le_div_iff₀ (by positivity)).mp hh
    nlinarith
  obtain ⟨b, hb, hgap⟩ := exists_admissible_input_gaps hn T.data.adapted.normal r c L (half_pos hg)
  refine ⟨δ, ρ, L, b, hδ, hρ, hL, hb, hρR, ?_⟩
  intro Q hclose hcenter
  have hΩ : closedBall a R ⊆ inputDomain T := fun w hw ↦ ⟨hdom hw, hballU (hx hw)⟩
  have hs := smooth_fullInput T Q
  have hlow := hinput Q hclose
  have hval (w) (hw : w ∈ closedBall a R) : ‖fullInput T Q w‖ ≤ L := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a R)
      (fun y hy ↦ (hs.contDiffAt ((isOpen_inputDomain T).mem_nhds (hΩ hy))).of_le
        (by simp : (1 : ℕ∞ω) ≤ ∞)) hw (Nat.zero_le 1)
    have hv : ‖fullInput T Q w‖ ≤ cNorm (closedBall a R) 1 (fullInput T Q) := by
      simpa only [norm_iteratedFDeriv_zero] using hh
    exact hv.trans hlow
  have hdenSmooth : ContDiffOn ℝ ∞ (adaptedDenominator T Q r c) (inputDomain T) := by
    rw [adaptedDenominator_eq_formula]
    exact (smooth_denominator T.data.adapted.normal r c).comp_contDiffOn hs
  have hdenBound : cNorm (closedBall a R) 1 (adaptedDenominator T Q r c) ≤ B := by
    rw [adaptedDenominator_eq_formula]
    exact (hcomp (inputDomain T) (isOpen_inputDomain T) hΩ (fullInput T Q) hs
      (fun w hw ↦ mem_closedBall_zero_iff.mpr (hval w hw))).trans
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hlow) hC.le)
  have hder (w) (hw : w ∈ closedBall a R) : ‖fderiv ℝ (adaptedDenominator T Q r c) w‖ ≤ B := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a R)
      (fun y hy ↦ (hdenSmooth.contDiffAt ((isOpen_inputDomain T).mem_nhds (hΩ hy))).of_le
        (by simp : (1 : ℕ∞ω) ≤ ∞)) hw (le_refl 1)
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans hdenBound
  have hlip : LipschitzOnWith ⟨B, hB.le⟩ (adaptedDenominator T Q r c) (closedBall a R) :=
    (convex_closedBall a R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun w hw ↦ (hdenSmooth.contDiffAt ((isOpen_inputDomain T).mem_nhds (hΩ hw))).differentiableAt (by simp))
      (fun w hw ↦ by exact_mod_cast hder w hw)
  have hsub : closedBall a (2 * ρ) ⊆ closedBall a R := closedBall_subset_closedBall hρR
  refine ⟨(cNorm_mono_set_of_contDiffAt hsub (isCompact_closedBall a R)
    (fun y hy ↦ (hs.contDiffAt ((isOpen_inputDomain T).mem_nhds (hΩ hy))).of_le (by simp))).trans hlow, ?_⟩
  intro w hw
  have hdist := (hlip.dist_le_mul w (hsub hw) a (mem_closedBall_self hR.le)).trans
    (mul_le_mul_of_nonneg_left (mem_closedBall.mp hw) hB.le)
  have hd : g / 2 ≤ |adaptedDenominator T Q r c w| := by
    rw [Real.dist_eq] at hdist
    change |adaptedDenominator T Q r c w - adaptedDenominator T Q r c a| ≤ B * (2 * ρ) at hdist
    have habs := abs_sub_abs_le_abs_sub (adaptedDenominator T Q r c a)
      (adaptedDenominator T Q r c w)
    rw [abs_sub_comm] at habs
    linarith
  exact ⟨hd, hgap (fullInput T Q w) ⟨mem_closedBall_zero_iff.mpr (hval w (hsub hw)), hd⟩⟩

end JanetCartan.LeadingWave.FullModulation.UniformCoefficients
