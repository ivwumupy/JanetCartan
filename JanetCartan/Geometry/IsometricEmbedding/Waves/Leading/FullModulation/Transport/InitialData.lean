module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Coefficients
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds

/-! # Lifting the original initial scalar

The initial scalar in `app:ch_waves:thm:leading` is a function of `(y,z)`.
Projection estimates retain its ORIGINAL joint norms in
`app:ch_waves:eq:joint-tame`, without a modulation-dependent datum.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.LeadingWave.FullModulation

variable {n : ℕ}

/-- Forget the independent modulation covector on the initial section
(`app:ch_waves:thm:leading`). -/
def initialProjection :
    (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →L[ℝ]
      Euclidean (n - 1) × Euclidean 3 :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

/-- The projection does not enlarge distances (`app:ch_waves:eq:joint-tame`). -/
theorem norm_initialProjection_le : ‖initialProjection (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change max ‖p.1‖ ‖p.2.1‖ ≤ 1 * max ‖p.1‖ (max ‖p.2.1‖ ‖p.2.2‖)
  simpa only [one_mul] using max_le_max le_rfl (le_max_left _ _)

/-- Projection of a full section ball stays in the original section ball
(`app:ch_waves:thm:leading`). -/
theorem initialProjection_mapsTo_ball
    (p : Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) (R : ℝ) :
    MapsTo initialProjection (ball p R) (ball (p.1, p.2.1) R) := by
  intro q hq
  exact lt_of_le_of_lt ((initialProjection (n := n)).lipschitzWith.dist_le_mul q p |>.trans
    (mul_le_of_le_one_left dist_nonneg norm_initialProjection_le)) hq

/-- The original smooth initial scalar lifts smoothly
(`app:ch_waves:thm:leading`). -/
theorem contDiffOn_initialScalar {r : Euclidean (n - 1) × Euclidean 3 → ℝ}
    {S : Set (Euclidean (n - 1) × Euclidean 3)}
    {L : Set (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))}
    (hr : ContDiffOn ℝ ∞ r S) (hm : MapsTo initialProjection L S) :
    ContDiffOn ℝ ∞ (initialScalar r) L :=
  hr.comp initialProjection.contDiff.contDiffOn hm

/-- All joint derivatives of the lifted datum are bounded by the ORIGINAL
`(y,z)` datum. The polynomial order cost is absorbed by the final tame
constant (`app:ch_waves:eq:joint-tame`). -/
theorem cNorm_initialScalar_le
    {r : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (p : Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    {R : ℝ} (hR : 0 < R)
    (hr : ContDiffOn ℝ ∞ r (ball (p.1, p.2.1) (R / 4))) (j : ℕ) :
    cNorm (closedBall p (R / 8)) j (initialScalar r) ≤
      (j + 1 : ℝ) * cNorm (closedBall (p.1, p.2.1) (R / 8)) j r := by
  apply FullPhaseCharts.InverseEstimates.cNorm_comp_contraction_le_on
    initialProjection norm_initialProjection_le (isCompact_closedBall _ _) isOpen_ball
    (closedBall_subset_ball (by linarith : R / 8 < R / 4)) hr
  intro q hq
  exact le_trans ((initialProjection (n := n)).lipschitzWith.dist_le_mul q p |>.trans
    (mul_le_of_le_one_left dist_nonneg norm_initialProjection_le)) hq

end JanetCartan.LeadingWave.FullModulation
