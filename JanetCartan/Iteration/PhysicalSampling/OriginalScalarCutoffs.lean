module

public import JanetCartan.Iteration.PhysicalSampling.OriginalWeights

/-!
# The actual scalar cutoffs on the unchanged measurement collar

The scalar physical cutoff and carrier extension are the SAME retained choices
on the original once-capped family. The existing six-radius admission puts the
whole original measurement/source/coefficient collar inside every scalar
plateau. No measurement radius is changed or identified with a varying carrier
radius (`new:eq:amplitude-test`, `app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open Set Metric
namespace JanetCartan.PhysicalSampling.OriginalScalarCutoffs
open PhysicalSeed PhysicalNormalInverse

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

/-- The retained physical scalar cutoff, with no new cutoff choice. -/
def χstar (i : actual(OriginalWeights.Index)) : ContDiffBump (0 : Euclidean (m + 1)) :=
  OriginalChoices.Scalar.χstar (p := pOrder) hn i.1.1 i.2
    (selected(SelectedBoundary.cell) i.1.1 i.2)
    (actual(OriginalAdmission.root_mem) i.1.1 i.2)

/-- The retained carrier extension used by the scalar sharp/mean factory. -/
def β (i : actual(OriginalWeights.Index)) : SeparatedSampling.Point → ℝ :=
  OriginalChoices.Scalar.β (p := pOrder) hn i.1.1 i.2
    (selected(SelectedBoundary.cell) i.1.1 i.2)
    (actual(OriginalAdmission.root_mem) i.1.1 i.2)

theorem continuous_β (i : actual(OriginalWeights.Index)) : Continuous (actual(β) i) :=
  OriginalChoices.Scalar.hβ (p := pOrder) hn i.1.1 i.2
    (selected(SelectedBoundary.cell) i.1.1 i.2)
    (actual(OriginalAdmission.root_mem) i.1.1 i.2)

theorem abs_β_le_one (i : actual(OriginalWeights.Index)) (z : SeparatedSampling.Point) :
    |actual(β) i z| ≤ 1 :=
  OriginalChoices.Scalar.hβ_one (p := pOrder) hn i.1.1 i.2
    (selected(SelectedBoundary.cell) i.1.1 i.2)
    (actual(OriginalAdmission.root_mem) i.1.1 i.2) z

theorem compact_χstar (i : actual(OriginalWeights.Index)) :
    HasCompactSupport (actual(χstar) i : Euclidean (m + 1) → ℝ) :=
  (actual(χstar) i).hasCompactSupport

/-- The upfront quarter cap gives the whole fourfold original carrier ball,
not only the supports of the three individual physical cutoffs. -/
theorem four_carrier_radius_le_inner (i : actual(OriginalWeights.Index)) :
    4 * selected(SelectedBoundary.a') i ≤ (actual(χstar) i).rIn := by
  exact (mul_le_mul_of_nonneg_left (actual(OriginalAdmission.spatial_le_sampling) i)
    (by norm_num : (0 : ℝ) ≤ 4)).trans
    (originalSamplingExtraCap_four_le_scalar_inner hn pOrder i.1.1 i.2
      (selected(SelectedBoundary.cell) i.1.1 i.2)
      (actual(OriginalAdmission.root_mem) i.1.1 i.2))

/-- The existing original common measurement radius, with its retained
six-radius separation, closes the entire five-radius coefficient collar and
all three physical measurement/source cutoffs. No radius is reselected. -/
theorem measurement_plateau (i : actual(OriginalWeights.Index)) :
    closedBall (0 : Euclidean (m + 1)) (5 * selected(SelectedBoundary.rMeasure)) ⊆
      interior {x | actual(χstar) i x = 1} ∧
    ∀ j : Fin 3,
      tsupport (ContinuumRow.FixedCutoffs.physical (n := m + 1)
        selected(SelectedBoundary.hrMeasure) j) ⊆ interior {x | actual(χstar) i x = 1} := by
  exact scalarCutoff_plateau_of_original_cap (actual(χstar) i)
    selected(SelectedBoundary.hrMeasure) (selected(SelectedBoundary.fact60) i)
    (actual(OriginalAdmission.spatial_caps) i).1
    (OriginalChoices.Scalar.hcap_χstar (p := pOrder) hn i.1.1 i.2
      (selected(SelectedBoundary.cell) i.1.1 i.2)
      (actual(OriginalAdmission.root_mem) i.1.1 i.2))

/-- Exact scalar cutoff removal on the full unchanged original measurement
or source support, including the collar outside the physical strain core. -/
theorem one_on_physical_support (i : actual(OriginalWeights.Index)) (j : Fin 3)
    {x : Euclidean (m + 1)}
    (hx : x ∈ tsupport (ContinuumRow.FixedCutoffs.physical (n := m + 1)
      selected(SelectedBoundary.hrMeasure) j)) : actual(χstar) i x = 1 :=
  interior_subset (s := {x | actual(χstar) i x = 1})
    ((actual(measurement_plateau) i).2 j hx)

/-- The full retained five-radius coefficient ball also lies in the plateau. -/
theorem one_on_coefficient_ball (i : actual(OriginalWeights.Index))
    {x : Euclidean (m + 1)}
    (hx : x ∈ closedBall 0 (5 * selected(SelectedBoundary.rMeasure))) :
    actual(χstar) i x = 1 :=
  interior_subset (s := {x | actual(χstar) i x = 1})
    ((actual(measurement_plateau) i).1 hx)

end JanetCartan.PhysicalSampling.OriginalScalarCutoffs
