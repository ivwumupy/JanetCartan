module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs
public import JanetCartan.Analysis.Fourier.Periodic.SmallSupportNegative.Support

/-!
# An inner support with fixed outer image cutoffs

For `app:ch_background:prop:bg-frame` in both manuscripts, first fix the
measurement and source cutoffs `FixedCutoffs.periodic hR hcell 1` and
`FixedCutoffs.periodic hR hcell 2`. The cutoff below can then be supported in
any smaller ball. Thus the periodic/source-mask comparison can have constants
depending on the fixed outer cutoffs before the inner support is shrunk.
The exterior is still the original channel `1 - ψ`, with normal `(1 - ψ)²`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric

namespace JanetCartan.ContinuumNormal

open ContinuumRow AmplitudeBound

variable {n : ℕ} {r R : ℝ}

/-- The physical cutoff used only for the inner localization and exterior
channel of `app:ch_background:prop:bg-frame`. -/
def innerPhysicalCutoff (hr : 0 < r) : ContDiffBump (0 : Euclidean n) :=
  bufferedBallBump 0 (r / 2) r (half_pos hr) (half_lt_self hr)

/-- The inner closed support lies strictly inside the requested ball
(`app:ch_background:prop:bg-frame`, small-support step). -/
theorem innerPhysicalCutoff_tsupport (hr : 0 < r) :
    tsupport (innerPhysicalCutoff (n := n) hr) ⊆ ball 0 r :=
  bufferedBallBump_tsupport_subset _ _ _ _ _

/-- The core retains an open plateau, before source scales or histories are
chosen (`app:ch_background:defn:bg-row`). -/
theorem innerPhysicalCutoff_plateau (hr : 0 < r) :
    closedBall (0 : Euclidean n) (r / 2) ⊆
      interior {x | innerPhysicalCutoff hr x = 1} :=
  bufferedBallBump_plateau _ _ _ _ _

/-- Periodization of the inner cutoff on the existing unit torus
(`app:ch_background:defn:bg-row`). -/
def innerCutoff (hr : 0 < r) (hcell : r < 1 / 2) : C(Torus n, ℝ) :=
  ImageGeometry.periodizedImageCutoff hcell (innerPhysicalCutoff hr)
    (innerPhysicalCutoff hr).contDiff
    ((innerPhysicalCutoff_tsupport hr).trans ball_subset_closedBall)

/-- The torus cutoff has exactly the physical representative used by the
image and carrier channels (`app:ch_background:defn:bg-row`). -/
@[simp] theorem innerCutoff_apply (hr : 0 < r) (hcell : r < 1 / 2) (z : Torus n) :
    innerCutoff hr hcell z = innerPhysicalCutoff hr (centeredTorusRepresentative z) := rfl

/-- The inner cutoff is smooth (`app:ch_background:defn:bg-row`). -/
theorem innerCutoff_smooth (hr : 0 < r) (hcell : r < 1 / 2) :
    IsSmoothPeriodic (innerCutoff (n := n) hr hcell) :=
  ImageGeometry.isSmoothPeriodic_periodizedImageCutoff _ _ _ _

/-- The inner cutoff has values in `[0,1]`
(`app:ch_background:prop:bg-frame`). -/
theorem innerCutoff_mem_Icc (hr : 0 < r) (hcell : r < 1 / 2) (z : Torus n) :
    innerCutoff hr hcell z ∈ Icc (0 : ℝ) 1 :=
  ⟨(innerPhysicalCutoff hr).nonneg, (innerPhysicalCutoff hr).le_one⟩

/-- Every localized L² field has the literal small physical support required
by the Fourier support estimate (`app:ch_background:prop:bg-frame`). -/
theorem innerCutoff_supported (hr : 0 < r) (hcell : r < 1 / 2) (f : OutputL2 n) :
    ∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) r →
      cutoffMultiplier (innerCutoff hr hcell) f z = 0 := by
  filter_upwards [cutoffMultiplier_coeFn (innerCutoff hr hcell) f] with z hz hzs
  have hzero : innerPhysicalCutoff hr (centeredTorusRepresentative z) = 0 := by
    by_contra h
    exact hzs ⟨centeredTorusRepresentative z,
      innerPhysicalCutoff_tsupport hr (subset_tsupport _ h),
      torusQuotient_centeredTorusRepresentative z⟩
  simp only [hz, innerCutoff_apply, hzero, zero_smul]

/-- The original fixed outer measurement cutoff equals one on the entire
inner support; neither outer cutoff depends on the inner radius
(`app:ch_background:prop:bg-frame`). -/
theorem outer_measurement_one_on_inner
    (hR : 0 < R) (hcell : 4 * R < 1 / 2) (hr : 0 < r)
    (hrR : r ≤ R) (hrcell : r < 1 / 2) {z : Torus n}
    (hz : innerCutoff hr hrcell z ≠ 0) :
    FixedCutoffs.periodic hR hcell 1 z = 1 := by
  have hs := innerPhysicalCutoff_tsupport hr (subset_tsupport _ hz)
  have hmem : centeredTorusRepresentative z ∈
      closedBall (0 : Euclidean n) (((1 : Fin 3) + 1 : ℝ) * R) := by
    apply (closedBall_subset_closedBall (show r ≤ (((1 : Fin 3) + 1 : ℝ) * R) by
      norm_num
      linarith)) (ball_subset_closedBall hs)
  have hp : centeredTorusRepresentative z ∈
      {x | FixedCutoffs.physical hR 1 x = 1} :=
    interior_subset (FixedCutoffs.physical_plateau hR 1 hmem)
  exact hp

/-- Multiplication by the fixed measurement cutoff fixes the inner localized
field exactly (`app:ch_background:prop:bg-frame`). -/
theorem outer_measurement_fixes_inner
    (hR : 0 < R) (hcell : 4 * R < 1 / 2) (hr : 0 < r)
    (hrR : r ≤ R) (hrcell : r < 1 / 2) (f : OutputL2 n) :
    cutoffMultiplier (FixedCutoffs.periodic hR hcell 1)
      (cutoffMultiplier (innerCutoff hr hrcell) f) =
        cutoffMultiplier (innerCutoff hr hrcell) f := by
  apply Lp.ext
  filter_upwards [cutoffMultiplier_coeFn (FixedCutoffs.periodic hR hcell 1)
    (cutoffMultiplier (innerCutoff hr hrcell) f),
    cutoffMultiplier_coeFn (innerCutoff hr hrcell) f] with z h₁ h₂
  rw [h₁, h₂]
  by_cases hz : innerCutoff hr hrcell z = 0
  · simp only [hz, zero_smul, smul_zero]
  · rw [outer_measurement_one_on_inner hR hcell hr hrR hrcell hz, one_smul]

/-- The literal exterior channel vanishes on the core of radius `r/2`
(`app:ch_background:prop:bg-frame`). -/
theorem inner_exterior_zero_on_core (hr : 0 < r) (hcell : r < 1 / 2)
    (f : OutputL2 n) :
    ∀ᵐ z ∂volume, centeredTorusRepresentative z ∈ closedBall 0 (r / 2) →
      exteriorChannel (innerCutoff hr hcell) f z = 0 := by
  apply exteriorChannel_zero_on_core (innerCutoff hr hcell)
    {z | centeredTorusRepresentative z ∈ closedBall 0 (r / 2)}
  intro z hz
  have hp : centeredTorusRepresentative z ∈ {x | innerPhysicalCutoff hr x = 1} :=
    interior_subset (innerPhysicalCutoff_plateau hr hz)
  exact hp

end JanetCartan.ContinuumNormal
