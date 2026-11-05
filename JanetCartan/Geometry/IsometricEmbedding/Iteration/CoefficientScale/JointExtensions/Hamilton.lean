module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.FixedCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.SharpPhaseBounds

/-!
# Fixed extensions of the canonical Hamilton phases

This is the phase extension in `main:prop:current-scale` and
`app:eq:uniform-high-coeff`. The full physical and energy/spatial-covector
variables are retained. The operator, its agreement ball and its compact
support are fixed by the canonical Hamilton family before the current frame,
the history, the derivative order and accuracy.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CurrentCoefficientProfiles.JointExtensions
open ActualCarriers CurrentFullPhase FrozenMenu HamiltonPhase ProjectedStressFrame

/-- Fixed Hilbert coordinates for the full Hamilton phase, with the original
nested product norm retained in the target (`app:eq:uniform-high-coeff`). -/
def hamiltonExtensionCoordinates (n : ℕ) :
    WithLp 2 (Euclidean n × WithLp 2 (ℝ × Euclidean (n - 1))) ≃L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1))) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).trans
    ((ContinuousLinearEquiv.refl ℝ (Euclidean n)).prodCongr
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean (n - 1))))

/-- The Hilbert-to-product coordinate map is a contraction. This preserves
the input domain in `app:eq:uniform-high-coeff`. -/
theorem norm_hamiltonExtensionCoordinates_le (n : ℕ) : ‖(hamiltonExtensionCoordinates n).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change max ‖q.ofLp.1‖ (max ‖q.ofLp.2.ofLp.1‖ ‖q.ofLp.2.ofLp.2‖) ≤ 1 * ‖q‖
  rw [one_mul]
  exact max_le (WithLp.norm_fst_le _ q)
    (max_le ((WithLp.norm_fst_le _ q.ofLp.2).trans (WithLp.norm_snd_le _ q))
      ((WithLp.norm_snd_le _ q.ofLp.2).trans (WithLp.norm_snd_le _ q)))

private theorem lpPair_norm_le {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (x : A) (y : B) :
    ‖WithLp.toLp 2 (x, y)‖ ≤ ‖x‖ + ‖y‖ := by
  have he : WithLp.toLp 2 (x, y) = WithLp.toLp 2 (x, (0 : B)) + WithLp.toLp 2 ((0 : A), y) := by
    apply WithLp.ofLp_injective
    simp
  rw [he]
  simpa only [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] using
    norm_add_le (WithLp.toLp 2 (x, (0 : B))) (WithLp.toLp 2 ((0 : A), y))

/-- The inverse fixed coordinate map costs at most three. This explicit
constant keeps the phase buffer of `app:ch_seed:prop:seed-phase-charts`. -/
theorem norm_hamiltonExtensionCoordinates_symm_le (n : ℕ) : ‖(hamiltonExtensionCoordinates n).symm.toContinuousLinearMap‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  change ‖WithLp.toLp 2 (q.1, WithLp.toLp 2 q.2)‖ ≤ 3 * ‖q‖
  have houter := lpPair_norm_le q.1 (WithLp.toLp 2 q.2)
  have hinner := lpPair_norm_le q.2.1 q.2.2
  have hx := norm_fst_le q
  have ht := (norm_fst_le q.2).trans (norm_snd_le q)
  have hy := (norm_snd_le q.2).trans (norm_snd_le q)
  linarith

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The literal full phase center, shared with `CommonProfiles`
(`app:ch_seed:prop:seed-phase-charts`). -/
def hamiltonExtensionCenter : Euclidean n × (ℝ × Euclidean (n - 1)) :=
  (T.data.adapted.embedding T.data.adapted.baseData.1, T.data.adapted.baseData.2)

/-- Fixed extension parameters for the actual Hamilton phase
(`app:eq:uniform-high-coeff`). -/
def hamiltonExtensionParameters :
    BallExtension.Parameters (WithLp 2 (Euclidean n × WithLp 2 (ℝ × Euclidean (n - 1)))) :=
  coordinateBallParameters (hamiltonExtensionCoordinates n) (hamiltonExtensionCenter T)
    T.family.radius_pos

/-- The positive radius of the extended Hamilton phase's agreement ball in
the original product norm (`app:eq:uniform-high-coeff`). -/
def hamiltonExtensionRadius : ℝ :=
  coordinateWorkingRadius (hamiltonExtensionCoordinates n) (hamiltonExtensionCenter T)
    T.family.radius_pos

/-- The fixed support of every extended current Hamilton phase
(`app:eq:uniform-high-coeff`). -/
def hamiltonExtensionSupport : Set (Euclidean n × (ℝ × Euclidean (n - 1))) :=
  hamiltonExtensionCoordinates n '' closedBall (hamiltonExtensionParameters T).center
    ((hamiltonExtensionParameters T).radius + (hamiltonExtensionParameters T).width / 2)

/-- The actual canonical phase extended by one fixed Seeley operator
(`app:eq:uniform-high-coeff`). -/
def extendedHamiltonPhase (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold}) :
    (Euclidean n × (ℝ × Euclidean (n - 1))) → ℝ :=
  coordinateSeeley (hamiltonExtensionCoordinates n) (hamiltonExtensionParameters T)
    (phase (T.currentChart Q).coordinates)

/-- The agreement domain is a genuine fixed neighborhood
(`app:eq:uniform-high-coeff`). -/
theorem hamiltonExtensionRadius_pos : 0 < hamiltonExtensionRadius T :=
  coordinateWorkingRadius_pos _ _ _

/-- The original `family.radius / 8` phase buffer is retained by the fixed
extension, in the ACTUAL nested product norm. This is the radius appearing
in the inequality `3 * qrad < family.radius / 8` in `CommonProfiles`
(`app:ch_seed:prop:seed-phase-charts`, `app:eq:uniform-high-coeff`). -/
theorem eighth_radius_le_hamiltonExtensionRadius :
    T.family.radius / 8 ≤ hamiltonExtensionRadius T := by
  have hf := norm_hamiltonExtensionCoordinates_le n
  have hb := norm_hamiltonExtensionCoordinates_symm_le n
  have hnf := norm_nonneg (hamiltonExtensionCoordinates n).toContinuousLinearMap
  have hnb := norm_nonneg (hamiltonExtensionCoordinates n).symm.toContinuousLinearMap
  change T.family.radius / 8 ≤
    (T.family.radius / (1 + ‖(hamiltonExtensionCoordinates n).toContinuousLinearMap‖)) /
      (1 + ‖(hamiltonExtensionCoordinates n).symm.toContinuousLinearMap‖)
  rw [div_div]
  exact div_le_div_of_nonneg_left T.family.radius_pos.le (by positivity) (by nlinarith)

/-- All supports lie in one compact set chosen before the current frame
(`app:eq:uniform-high-coeff`). -/
theorem isCompact_hamiltonExtensionSupport : IsCompact (hamiltonExtensionSupport T) :=
  (isCompact_closedBall _ _).image (hamiltonExtensionCoordinates n).continuous

private theorem phase_contDiffAt (Q : _) :
    ∀ x ∈ closedBall (hamiltonExtensionCenter T) T.family.radius,
      ContDiffAt ℝ ∞ (phase (T.currentChart Q).coordinates) x := by
  intro x hx
  exact (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
    (closedBall_subset_ball (by linarith [T.family.radius_pos]) hx))

/-- Smoothness, agreement and fixed support for the ACTUAL full Hamilton
phase, including joint physical/energy/covector variables
(`app:eq:uniform-high-coeff`). -/
theorem extendedHamiltonPhase_properties (Q : _) :
    ContDiff ℝ ∞ (extendedHamiltonPhase T Q) ∧
    EqOn (extendedHamiltonPhase T Q) (phase (T.currentChart Q).coordinates)
      (closedBall (hamiltonExtensionCenter T) (hamiltonExtensionRadius T)) ∧
    tsupport (extendedHamiltonPhase T Q) ⊆ hamiltonExtensionSupport T := by
  refine ⟨?_, ?_, tsupport_coordinateSeeley_subset _ _ _⟩
  · apply contDiff_coordinateSeeley
    rintro _ ⟨x, hx, rfl⟩
    exact phase_contDiffAt T Q _ (coordinateBallParameters_mapsTo _ _ _ hx)
  · exact (coordinateSeeley_eqOn _ _ _).mono (coordinateWorkingBall_subset _ _ _)

/-- Agreement on the explicit phase buffer used by the quotient chart
construction (`app:ch_seed:prop:seed-phase-charts`). The inclusion in the
extension's agreement ball is proved with the original norms. -/
theorem extendedHamiltonPhase_eqOn_eighth_ball (Q : _) :
    EqOn (extendedHamiltonPhase T Q) (phase (T.currentChart Q).coordinates)
      (closedBall (hamiltonExtensionCenter T) (T.family.radius / 8)) :=
  (extendedHamiltonPhase_properties T Q).2.1.mono
    (closedBall_subset_closedBall (eighth_radius_le_hamiltonExtensionRadius T))

/-- Global jets of the actual phase extension are bounded by the literal
local phase seminorm at the SAME order (`app:eq:uniform-high-coeff`). -/
theorem exists_extendedHamiltonPhase_cNorm_bound (m : ℕ) :
    ∃ C > (0 : ℝ), ∀ Q,
      cNorm univ m (extendedHamiltonPhase T Q) ≤
        C * cNorm (closedBall (hamiltonExtensionCenter T) T.family.radius) m
          (phase (T.currentChart Q).coordinates) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_coordinateSeeley_le (F := ℝ)
    (hamiltonExtensionCoordinates n) (hamiltonExtensionParameters T) m
  exact ⟨C, hC, fun Q ↦ hb _ (isCompact_closedBall _ _)
    (coordinateBallParameters_mapsTo _ _ _) _ (phase_contDiffAt T Q)⟩

/-- The actual extended Hamilton phase retains the sharp immersion reserve
THREE. The primitive geometric hypotheses are precisely those produced by
`CommonProfiles`; no extension bound or phase profile is assumed
(`main:prop:current-scale`, `app:eq:uniform-high-coeff`). -/
theorem exists_extendedHamiltonPhase_sharp_bound {N : ℕ}
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ m, cNorm univ m (extendedHamiltonPhase T Q) ≤
          A m * (1 + cNorm K (m + 3) F) := by
  obtain ⟨A, hA, hb⟩ := T.exists_projected_phase_sharp_bound hK hKU hball C₀ hκmet hκ
  choose C hC hext using exists_extendedHamiltonPhase_cNorm_bound T
  refine ⟨fun m ↦ C m * A m, fun m ↦ mul_pos (hC m) (hA m), ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow
  dsimp only
  intro m
  exact (hext m _).trans ((mul_le_mul_of_nonneg_left
    (hb F hF hi hrank hlowF hmet hnormal hlow m) (hC m).le).trans_eq (mul_assoc _ _ _).symm)

end JanetCartan.CurrentCoefficientProfiles.JointExtensions
