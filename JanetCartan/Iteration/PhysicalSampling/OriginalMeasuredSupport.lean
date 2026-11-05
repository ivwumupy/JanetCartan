module

public import JanetCartan.Iteration.PhysicalSampling.OriginalWeights
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.PhysicalMeasurement

/-!
# The unchanged common physical measurement lies on the actual Band core

The original six-radius separation puts the whole common physical coefficient
ball inside the selected carrier-cutoff plateau for every row. The retained
Band–cutoff geometry puts that carrier cutoff's support in the sharp ball.
This applies to the actual stress measurement of every current, even where the
physical strain identity itself is not required. No new measurement, carrier
radius, or immersion is selected (`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalSampling.OriginalMeasuredSupport
open PhysicalSeed PhysicalNormalInverse ContinuumRow Set Metric Sampling

variable {m : ℕ} (hn : 5 ≤ m + 1) (pOrder : ℕ)
  (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean (m + 1)))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : (a : Fin (OriginalBoundary.D hn).chartCount) ×
    Fin ((OriginalBoundary.D hn).patchCount a) → Euclidean (m + 1))
  (hk : ∀ a, k a ≠ 0) (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean (m + 1))) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ)
  (hmargin : ∀ a ∈ orders, 0 < margin a)
  (hextendedMargin : ∀ a ∈ orders, 0 < extendedMargin a)
  (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap)
  (userExtra : StrongExtraCaps hn)

local notation "merged" => samplingCappedExtra hn pOrder userExtra
local notation "capped" => strongCappedExtra hn merged
set_option quotPrecheck false in
local notation "selected(" f ")" =>
  f hn εframe hεframe qext hqcenter hqradius k hk hkD p orders margin extendedMargin
    hmargin hextendedMargin cap hcap incidenceCap hincidenceCap capped
set_option quotPrecheck false in
local notation "actual(" f ")" =>
  f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders margin extendedMargin
    hmargin hextendedMargin cap hcap incidenceCap hincidenceCap userExtra
set_option quotPrecheck false in
local notation "sharpRadius(" i ")" =>
  OriginalChoices.Band.a (p := pOrder) hn i.1.1 i.2
    (selected(SelectedBoundary.cell) i.1.1 i.2) (actual(OriginalAdmission.root_mem) i.1.1 i.2)

/-- The entire fixed fourfold common coefficient ball is contained in the
actual sharp-band physical ball of each selected row. -/
theorem coefficient_ball_in_original_sharp_ball (i : actual(OriginalWeights.Index)) :
    closedBall (0 : Euclidean (m + 1)) (4 * selected(SelectedBoundary.rMeasure)) ⊆
      closedBall 0 (sharpRadius(i) / 8) := by
  let μ := selected(SelectedBoundary.rMeasure)
  let a := selected(SelectedBoundary.a') i
  have hμ : 0 < μ := selected(SelectedBoundary.hrMeasure)
  have hma : 6 * μ < a := selected(SelectedBoundary.fact60) i
  have ha : 0 < a := selected(SelectedBoundary.ha') i
  have hcore : closedBall (0 : Euclidean (m + 1)) (4 * μ) ⊆
      tsupport (FixedCutoffs.physical (n := m + 1) ha 1) := by
    intro x hx
    have hinner : x ∈ closedBall (0 : Euclidean (m + 1)) (((1 : Fin 3).val + 1 : ℝ) * a) := by
      apply closedBall_subset_closedBall _ hx
      norm_num
      linarith
    have hone := interior_subset ((FixedCutoffs.physical_plateau ha 1) hinner)
    exact subset_tsupport _ (show FixedCutoffs.physical ha 1 x ≠ 0 from (show FixedCutoffs.physical ha 1 x = 1 from hone).trans_ne one_ne_zero)
  exact hcore.trans ((actual(OriginalAdmission.cutoff_on_actual_selected_row) i).2.2.1 1)

/-- The three genuine common physical/source cutoffs fit this same row's
sharp ball, including their whole topological support, not just the core. -/
theorem physical_support_in_original_sharp_ball (i : actual(OriginalWeights.Index)) (k : Fin 3) :
    tsupport (FixedCutoffs.physical (n := m + 1) selected(SelectedBoundary.hrMeasure) k) ⊆
      closedBall 0 (sharpRadius(i) / 8) :=
  (FixedCutoffs.physical_tsupport_four selected(SelectedBoundary.hrMeasure) k).trans
    (actual(coefficient_ball_in_original_sharp_ball) i)

/-- Thus the physical support hypothesis of the sharp Band41 producer holds
for the literal original Euclidean stress measurement, including the actual
projected stress of the physical finite history. -/
theorem measurement_support_in_original_sharp_ball (i : actual(OriginalWeights.Index))
    (Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1)) :
    Function.support (canonicalSamplingMeasurement Q selected(SelectedBoundary.hrMeasure)) ⊆
      closedBall 0 (sharpRadius(i) / 8) :=
  ((subset_tsupport _).trans (tsupport_canonicalSamplingMeasurement Q selected(SelectedBoundary.hrMeasure))).trans
    (actual(physical_support_in_original_sharp_ball) i 1)

end JanetCartan.PhysicalSampling.OriginalMeasuredSupport
