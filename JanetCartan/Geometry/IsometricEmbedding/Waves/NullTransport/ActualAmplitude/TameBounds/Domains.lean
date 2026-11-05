module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Vector

/-!
# Domain consequences of the published local amplitude construction

The forward range on the closed coefficient cylinder follows by continuity
from its proved range on the open flow tube. The smaller working cylinder is
contained in that tube. These are deductions from the exact outputs of
`exists_projected_local_positive_amplitude`, for `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport.AmplitudeTame

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The proved linear coordinate buffer also controls the half-radius ball.
This puts the composed coefficient strictly inside its smooth physical ball
(`app:ch_waves:eq:joint-tame`). -/
theorem mapsTo_half_closedBall (L : E →L[ℝ] F) (a : E) (b : F) {R ρ : ℝ}
    (hcenter : L a = b) (hmap : MapsTo L (closedBall a R) (closedBall b ρ)) :
    MapsTo L (closedBall a (R / 2)) (closedBall b (ρ / 2)) := by
  intro q hq
  have hdist : dist (a + (2 : ℝ) • (q - a)) a = 2 * dist q a := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_ofNat, ← dist_eq_norm]
  have hin : a + (2 : ℝ) • (q - a) ∈ closedBall a R := by
    rw [mem_closedBall, hdist]
    linarith [mem_closedBall.mp hq]
  have hh := mem_closedBall.mp (hmap hin)
  have he : dist (L (a + (2 : ℝ) • (q - a))) b = 2 * dist (L q) b := by
    rw [map_add, map_smul, map_sub, hcenter, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_ofNat, ← dist_eq_norm]
  rw [he] at hh
  rw [mem_closedBall]
  linarith

omit [NormedSpace ℝ E] in
/-- The entire compact coefficient cylinder lies in the larger smooth flow
buffer supplied by the producer (`app:ch_waves:thm:leading`). -/
theorem coefficientCylinder_subset_buffer (p : E) {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R) :
    Icc (-τ) τ ×ˢ closedBall p (R / 8) ⊆
      Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p (R / 4) := by
  intro q hq
  refine ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, ?_⟩
  exact closedBall_subset_ball (by linarith) hq.2

/-- The forward graph on the closed cylinder remains in the half-radius
adapted ball, by continuity at all boundary points. This is derived from the
producer's open-tube range, without a new flow assumption
(`app:ch_waves:eq:joint-tame`). -/
theorem forwardGraph_mapsTo_half_ball (p : E) {τ R : ℝ}
    (hτ : 0 < τ) (hR : 0 < R) (hτR : τ ≤ R / 16)
    {Φ : ℝ × E → E}
    (hΦ : ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p (R / 4)))
    (hmap : MapsTo (fun q ↦ (q.1, Φ q))
      (Ioo (-τ) τ ×ˢ ball p (R / 8)) (Ioo (-τ) τ ×ˢ ball p (R / 4))) :
    MapsTo (fun q ↦ (q.1, Φ q)) (Icc (-τ) τ ×ˢ closedBall p (R / 8))
      (closedBall (0, p) (R / 2)) := by
  intro q hq
  have hqcl : q ∈ closure (Ioo (-τ) τ ×ˢ ball p (R / 8)) := by
    rw [closure_prod_eq, closure_Ioo (by linarith : -τ ≠ τ),
      closure_ball p (by positivity : R / 8 ≠ 0)]
    exact hq
  have hcont : ContinuousAt (fun x ↦ dist (Φ x) p) q :=
    (hΦ.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds
      (coefficientCylinder_subset_buffer p hτ hR hq))).continuousAt.dist continuousAt_const
  have hr : dist (Φ q) p ≤ R / 4 :=
    ContinuousWithinAt.closure_le hqcl hcont.continuousWithinAt
      continuousWithinAt_const (fun x hx ↦ (mem_ball.mp (hmap hx).2).le)
  rw [mem_closedBall, Prod.dist_eq, max_le_iff]
  refine ⟨?_, by linarith⟩
  rw [Real.dist_eq, sub_zero]
  have ht : |q.1| ≤ τ := abs_le.mpr hq.1
  linarith

omit [NormedSpace ℝ E] in
/-- The prescribed compact working cylinder is inside both the open tube and
the coefficient cylinder, at every derivative order
(`app:ch_waves:eq:joint-tame`). -/
theorem workingCylinder_subsets (p : E) {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R) :
    (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p (R / 64) ⊆
      Ioo (-τ) τ ×ˢ ball p (R / 32)) ∧
    (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p (R / 64) ⊆
      Icc (-τ) τ ×ˢ closedBall p (R / 8)) := by
  constructor
  · intro q hq
    refine ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, ?_⟩
    exact closedBall_subset_ball (by linarith) hq.2
  · intro q hq
    refine ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, ?_⟩
    exact closedBall_subset_closedBall (by linarith) hq.2

end JanetCartan.NullTransport.AmplitudeTame
