module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Affine

/-!
# The real linear operator on the original closed ball

Affine transport preserves the real linear operator and its independence
of exterior representative values. Continuous real linear target maps still
commute with the SAME formula, proving the componentwise clause of
`app:ch_regular_base:lem:ball-extension` on the original ball.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual real linear smoother on the original smooth closed-ball
data (`app:ch_regular_base:lem:ball-extension`). Its values are proved smooth
and compactly supported in the prescribed open neighborhood. -/
def affineSmoothingLinear (c : E) {a : ℝ} (ha : 0 < a)
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R) :
    smoothClosedBallData (F := F) c a →ₗ[ℝ] (E → F) where
  toFun f := affineSmoothing c a R m (f : E → F)
  map_add' f g := by
    funext x
    exact congrFun (unitSmoothing_add hm hR
      (continuousOn_ballRescale_closedBall c ha.le (smoothClosedBallData_continuousOn f))
      (continuousOn_ballRescale_closedBall c ha.le (smoothClosedBallData_continuousOn g)))
        (ballNormalize c a x)
  map_smul' r f := by
    funext x
    exact congrFun (unitSmoothing_smul hm hR r (fun z ↦ (f : E → F) (ballRescale c a z)))
      (ballNormalize c a x)

/-- Only the original closed-ball values determine the transported
operator, so the representative domain gives the claimed operator on
smooth closed-ball data (`app:ch_regular_base:lem:ball-extension`). -/
theorem affineSmoothing_congr_closedBall (c : E) {a : ℝ} (ha : 0 < a)
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    {f g : E → F} (hfg : EqOn f g (closedBall c a)) :
    affineSmoothing c a R m f = affineSmoothing c a R m g := by
  have he := unitSmoothing_congr_closedBall hm hR
    (fun _ hz ↦ hfg (ballRescale_mem_closedBall c ha.le hz))
  funext x
  exact congrFun he (ballNormalize c a x)

/-- The same real operator acts componentwise after returning to the
original ball. Taking coordinate projections gives the vector and tensor
assertion in `app:ch_regular_base:lem:ball-extension`. -/
theorem affineSmoothing_map [CompleteSpace F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : F →L[ℝ] G) (c : E) {a : ℝ} (ha : 0 < a)
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    {f : E → F} (hf : ContinuousOn f (closedBall c a)) :
    affineSmoothing c a R m (fun x ↦ L (f x)) =
      fun x ↦ L (affineSmoothing c a R m f x) := by
  funext x
  exact congrFun (unitSmoothing_map L hm hR
    (continuousOn_ballRescale_closedBall c ha.le hf)) (ballNormalize c a x)

end JanetCartan.BallSmoothing
