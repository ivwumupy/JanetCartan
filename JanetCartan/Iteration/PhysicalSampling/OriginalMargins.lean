module

public import JanetCartan.Iteration.PhysicalSampling.OriginalWeights
public import Mathlib.Algebra.Order.Field.Pi

/-!
# One original finite phase margin and rate margin

Choose the finite positive minima of the already retained row tolerances and
rate bounds, after the original selector but before source dilation, physical
history and frequency. The source parent can include `δ` in its one common
`OriginalRegular.Graph` tolerance. No phase/profile bound is assumed and no
selected source, carrier radius or working cutoff is changed
(`new:sec:order-of-choices`, `app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalSampling.OriginalMargins
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

/-- The four retained scalar/mean/band/comparison tolerances on one actual row. -/
def rowTolerance (i : actual(OriginalWeights.Index)) : {x : ℝ // 0 < x} :=
  candidateSamplingTolerance hn pOrder i.1.1 i.2
    (selected(SelectedBoundary.cell) i.1.1 i.2)
    (actual(OriginalAdmission.root_mem) i.1.1 i.2)

/-- The actual row's retained finite-shift bound, including the phase radius. -/
def rowRate (i : actual(OriginalWeights.Index)) : {x : ℝ // 0 < x} :=
  candidateSamplingRate hn pOrder i.1.1 i.2
    (selected(SelectedBoundary.cell) i.1.1 i.2)
    (actual(OriginalAdmission.root_mem) i.1.1 i.2)

/-- A positive common low-six tolerance for every actual original row. -/
theorem exists_tolerance : ∃ δ > (0 : ℝ), ∀ i, δ ≤ (actual(rowTolerance) i).1 := by
  obtain ⟨δ, hδ, hbelow⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : actual(OriginalWeights.Index) ↦ (0 : ℝ))
    (y := fun i ↦ (actual(rowTolerance) i).1) (fun i ↦ (actual(rowTolerance) i).2)
  refine ⟨δ, hδ, ?_⟩
  intro i
  simpa only [zero_add] using (hbelow i).le

/-- A positive common rate bound for every actual original row. -/
theorem exists_rate : ∃ ε > (0 : ℝ), ∀ i, ε ≤ (actual(rowRate) i).1 := by
  obtain ⟨ε, hε, hbelow⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : actual(OriginalWeights.Index) ↦ (0 : ℝ))
    (y := fun i ↦ (actual(rowRate) i).1) (fun i ↦ (actual(rowRate) i).2)
  refine ⟨ε, hε, ?_⟩
  intro i
  simpa only [zero_add] using (hbelow i).le

/-- The ONE finite original sampler tolerance, chosen before source scale. -/
def δ : ℝ := (actual(exists_tolerance)).choose

theorem hδ : 0 < actual(δ) := (actual(exists_tolerance)).choose_spec.1

theorem δ_le (i : actual(OriginalWeights.Index)) : actual(δ) ≤ (actual(rowTolerance) i).1 :=
  (actual(exists_tolerance)).choose_spec.2 i

/-- The common source tolerance admits all FOUR original analytic factories. -/
theorem δ_caps (i : actual(OriginalWeights.Index)) :
    let q := i.1.1
    let l := i.2
    let j := selected(SelectedBoundary.cell) q l
    let hroot := actual(OriginalAdmission.root_mem) q l
    actual(δ) ≤ OriginalChoices.Scalar.δ (p := pOrder) hn q l j hroot ∧
      actual(δ) ≤ OriginalChoices.Mean.δ (p := pOrder) hn q l j hroot ∧
      actual(δ) ≤ OriginalChoices.Band.δ (p := pOrder) hn q l j hroot ∧
      actual(δ) ≤ OriginalChoices.Comparison.δ (p := pOrder) hn q l j hroot := by
  intro q l j hroot
  have hrow := candidateSamplingTolerance_spec hn pOrder q l j hroot
  have h := actual(δ_le) i
  exact ⟨h.trans hrow.1, h.trans hrow.2.1, h.trans hrow.2.2.1, h.trans hrow.2.2.2⟩

/-- The ONE finite original sampler rate bound, chosen before histories. -/
def ε : ℝ := (actual(exists_rate)).choose

theorem hε : 0 < actual(ε) := (actual(exists_rate)).choose_spec.1

theorem ε_le (i : actual(OriginalWeights.Index)) : actual(ε) ≤ (actual(rowRate) i).1 :=
  (actual(exists_rate)).choose_spec.2 i

/-- Every original scalar, measured, comparison, band and finite-shift rate
condition follows from this ONE finite family rate bound. -/
theorem ε_caps (i : actual(OriginalWeights.Index)) :
    let q := i.1.1
    let l := i.2
    let j := selected(SelectedBoundary.cell) q l
    let hroot := actual(OriginalAdmission.root_mem) q l
    let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
    let hP := ((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).1
    let ρ : ℝ := originalSamplingRadius hn q l j
    actual(ε) ≤ OriginalChoices.Scalar.ε (p := pOrder) hn q l j hroot ∧
      actual(ε) ≤ OriginalChoices.Mean.e (p := pOrder) hn q l j hroot ∧
      actual(ε) ≤ OriginalChoices.Comparison.e (p := pOrder) hn q l j hroot ∧
      actual(ε) ≤ OriginalChoices.Band.e (p := pOrder) hn q l j hroot / 2 ∧
      actual(ε) ≤ Sampling.MeasuredAmplitude.measuredPhaseRadius T hP (ρ := ρ) := by
  intro q l j hroot T hP ρ
  have hrow := candidateSamplingRate_spec hn pOrder q l j hroot
  have h := actual(ε_le) i
  exact ⟨h.trans hrow.1, h.trans hrow.2.1, h.trans hrow.2.2.1,
    h.trans hrow.2.2.2.1, h.trans hrow.2.2.2.2⟩

end JanetCartan.PhysicalSampling.OriginalMargins
