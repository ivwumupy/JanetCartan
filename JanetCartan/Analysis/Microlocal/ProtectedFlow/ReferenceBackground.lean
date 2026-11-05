module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ReducedContinuity

/-!
# The fixed lower-order completion of the cube background

For `app:ch_regular:eq:coefficient-extension`, choose a globally smooth
completion equal to the actual reference connection on a neighborhood of the
coefficient ball. Its full-array error is then controlled by the reference
principal-frame error alone. This supplies the fixed-reference margin in
`exists_extendedReducedCoefficients_low_neighborhood`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open GeometricProfile ProjectedStressFrame ContinuumRow.ImageGeometry
open CurrentGeometricNeighborhood

/-- Insert the principal frame in the complete reduced array, with zero
connection entries (`app:ch_waves:eq:reduced-symbol`). -/
def reducedPrincipalInclusion (n : ℕ) :
    (Fin n → MetricTensor n) →L[ℝ] (ReducedCoefficientIndex n → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun Q k ↦ match k with
      | .inl (a, i, k) => Q i a k
      | .inr _ => 0
    map_add' := by intro Q Q'; ext (⟨a, i, k⟩ | ⟨i, k⟩) <;> simp
    map_smul' := by intro a Q; ext (⟨a, i, k⟩ | ⟨i, k⟩) <;> simp }

/-- Construct one smooth lower-order completion from the fixed reference,
before derivative orders or current maps. The entire reference array error
then costs only the principal-frame error; all connection entries cancel on
an open neighborhood of the coefficient ball
(`app:ch_regular:thm:no-return`). -/
theorem exists_reference_coefficient_background {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius) :
    ∃ Z₀ : Euclidean n → Fin n × Fin n → ℝ, ContDiff ℝ ∞ Z₀ ∧
      (∀ x ∈ closedBall 0 r, ∀ ik,
        Z₀ x ik = geometricReducedCoefficients G.map x (.inr ik)) ∧
      ∀ m,
        cNorm (closedBall 0 r) m
          (geometricReducedCoefficients G.map - reducedCoefficientBackground Z₀) ≤
          ((m + 1 : ℝ) * (‖reducedPrincipalInclusion n‖ + 1)) *
            cNorm (closedBall 0 r) m (projectedStress G.map - fun _ ↦ cubeStress n) := by
  let s := (r + R) / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  let q : BallExtension.Parameters (Euclidean n) := {
    center := 0
    radius := s
    radius_pos := hs
    width := s / 4
    width_pos := by positivity
    width_lt := by linarith }
  have hi : IsImmersionOn G.map (ball 0 R) := fun x _ ↦ reference_isImmersion G x
  have hrank : HasFullNormalRankOn G.map (ball 0 R) :=
    fun x hx ↦ G.fullNormalRank x (ball_subset_ball hR.le hx)
  have harray := contDiffOn_geometricReducedCoefficients G.contDiff isOpen_ball hi hrank
  let Z : Euclidean n → Fin n × Fin n → ℝ :=
    fun x ik ↦ geometricReducedCoefficients G.map x (.inr ik)
  have hZ : ContDiffOn ℝ ∞ Z (ball 0 R) :=
    contDiffOn_pi.mpr (fun ik ↦ contDiffOn_pi.mp harray (.inr ik))
  let Z₀ := q.seeleyExtension Z
  have hZ₀ : ContDiff ℝ ∞ Z₀ := q.contDiff_seeleyExtension
    (hZ.mono (closedBall_subset_ball hsR))
  have heq : EqOn Z₀ Z (closedBall (0 : Euclidean n) s) :=
    fun x hx ↦ q.seeleyExtension_eq_on_closedBall Z hx
  let L := reducedPrincipalInclusion n
  have hevent (x : Euclidean n) (hx : x ∈ closedBall 0 r) :
      geometricReducedCoefficients G.map - reducedCoefficientBackground Z₀ =ᶠ[𝓝 x]
        L ∘ (projectedStress G.map - fun _ ↦ cubeStress n) := by
    filter_upwards [isOpen_ball.mem_nhds (closedBall_subset_ball hrs hx)] with y hy
    have hyR := ball_subset_ball hsR.le hy
    have hlower := heq (ball_subset_closedBall hy)
    funext k
    rcases k with ⟨a, i, k⟩ | ⟨i, k⟩
    · change (StressFrame.geometricCubeStress G.map y i).val a k - cubeStress n i a k = _
      rw [geometricCubeStress_val_eq_projectedStress
        (G.contDiff.contDiffAt.of_le (by simp)) (hrank y hyR) i]
      rfl
    · change geometricReducedCoefficients G.map y (.inr (i, k)) - Z₀ y (i, k) = 0
      rw [hlower]
      exact sub_self _
  have hframe : ContDiffOn ℝ ∞ (projectedStress G.map - fun _ ↦ cubeStress n) (ball 0 R) :=
    (contDiffOn_pi.mpr (fun i ↦ contDiffOn_projectedStress isOpen_ball G.contDiff.contDiffOn
      hi hrank i)).sub contDiffOn_const
  refine ⟨Z₀, hZ₀, fun x hx ik ↦ congrFun (heq (closedBall_subset_closedBall hrs.le hx)) ik, ?_⟩
  intro m
  rw [cNorm_eq_of_eventuallyEq hevent m]
  let f := projectedStress G.map - fun _ ↦ cubeStress n
  have hjet (j : ℕ) (hj : j ≤ m) (x : Euclidean n) (hx : x ∈ closedBall 0 r) :
      ‖iteratedFDeriv ℝ j (L ∘ f) x‖ ≤ (‖L‖ + 1) * cNorm (closedBall 0 r) m f := by
    have hf : ∀ y ∈ closedBall (0 : Euclidean n) r, ContDiffAt ℝ m f y :=
      fun y hy ↦ (hframe.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hrR hy))).of_le
        (by simp)
    rw [L.iteratedFDeriv_comp_left (hf x hx) (by exact_mod_cast hj)]
    exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      ((mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _) hf hx hj)
          (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _)))
  have hb := cNorm_le_sum_of_bounds (fun _ (_ : _ ≤ m) ↦
    mul_nonneg (by positivity) (cNorm_nonneg (closedBall 0 r) m f)) hjet
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, ← mul_assoc] using hb

/-- The full-array low class is produced from the reference frame-to-cube
margin and primitive current-map closeness. The required reference tolerance
precedes the reference and all its higher norms. The smooth lower-order
completion is constructed, and no current-array or lower-order comparison is
an input (`app:ch_regular:thm:no-return`). -/
theorem exists_reference_frame_extension_low_class {n : ℕ}
    (p : BallExtension.Parameters (Euclidean n)) (hp0 : p.center = 0)
    {R : ℝ} (hpR : p.radius < R) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference n, R < G.domain.chartRadius →
      cNorm (closedBall 0 p.radius) m (projectedStress G.map - fun _ ↦ cubeStress n) < η →
      ∃ Z₀ : Euclidean n → Fin n × Fin n → ℝ, ContDiff ℝ ∞ Z₀ ∧
        (∀ x ∈ closedBall 0 p.radius, ∀ ik,
          Z₀ x ik = geometricReducedCoefficients G.map x (.inr ik)) ∧
        ∃ δ > (0 : ℝ), ∀ F : Euclidean n → Euclidean (embeddingDimension n),
          ContDiff ℝ ∞ F → cNorm (closedBall 0 R) (max 8 (m + 2)) (F - G.map) < δ →
          IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
          ContDiff ℝ ∞ (extendedReducedCoefficients p Z₀ F) ∧
          cNorm univ m
            (extendedReducedCoefficients p Z₀ F - reducedCoefficientBackground Z₀) < ε := by
  obtain ⟨e, he, hlow⟩ :=
    exists_extendedReducedCoefficients_low_neighborhood p hp0 hpR m hε
  let B := (m + 1 : ℝ) * (‖reducedPrincipalInclusion n‖ + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨e / B, div_pos he hB, ?_⟩
  intro G hR hreference
  obtain ⟨Z₀, hZ₀, hZagree, hreferenceBound⟩ :=
    exists_reference_coefficient_background G p.radius_pos hpR hR
  have href : cNorm (closedBall (0 : Euclidean n) p.radius) m
      (geometricReducedCoefficients G.map - reducedCoefficientBackground Z₀) < e :=
    (hreferenceBound m).trans_lt
      ((mul_lt_mul_of_pos_left hreference hB).trans_eq (mul_div_cancel₀ e hB.ne'))
  obtain ⟨δ, hδ, hnear⟩ := hlow G hR
  exact ⟨Z₀, hZ₀, hZagree, δ, hδ, hnear Z₀ hZ₀ href⟩

end JanetCartan.ProtectedFlow
