module

public import JanetCartan.Iteration.PhysicalSampling.OriginalAdmission

/-!
# The unchanged finite original sampling weights

Retain the original incidence/patch index and the literal squared carrier
cutoff at each row's selected radius. These radii may vary with the row and
are NOT identified with the common measurement radius. Only one enclosing
coordinate cube is chosen; no carrier weight, center, or source is reselected
(`app:ch_waves:thm:sampling`, `app:ch_waves:eq:sampling-prefix-normal`).

The scalar and measured common event consume these same unscaled weights.
The auxiliary `OriginalChoices.Cutoff.ψ` is a different outer plateau cutoff,
not the sampling mass.
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped BigOperators ContDiff
namespace JanetCartan.PhysicalSampling
open PhysicalSeed PhysicalNormalInverse ContinuumRow CanonicalConic Sampling SeparatedSampling

/-- Finitely many ORIGINAL carrier cutoffs, with independently selected radii,
fit one fixed sampling cube. The original mass bound remains exactly one. -/
theorem exists_finite_original_carrier_weight_bounds
    {A : Type*} [Fintype A] (z : A → Euclidean 3) {r : A → ℝ} (hr : ∀ i, 0 < r i) :
    ∃ B > (0 : ℝ), ∀ i, PatchBounds (originalConicCarrierWeight (z i) (hr i)) B 1 := by
  classical
  choose B hB hb using fun i ↦ exists_originalConicCarrierWeight_patchBounds (z i) (hr i)
  let Btotal := 1 + ∑ i, B i
  have hBtotal : 0 < Btotal := by
    dsimp [Btotal]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ ↦ (hB i).le)
  refine ⟨Btotal, hBtotal, ?_⟩
  intro i
  refine ⟨hBtotal.le, (hb i).nonneg, (hb i).le_bound, ?_⟩
  intro q hq c
  apply ((hb i).support q hq c).trans
  have hi : B i ≤ ∑ j, B j :=
    Finset.single_le_sum (fun j _ ↦ (hB j).le) (Finset.mem_univ i)
  dsimp [Btotal]
  linarith

namespace OriginalWeights

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
local notation "weights(" f ")" =>
  f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders margin extendedMargin
    hmargin hextendedMargin cap hcap incidenceCap hincidenceCap userExtra

/-- The exact once-capped original incidence/patch labels, not a new cover. -/
abbrev Index := (q : selected(SelectedBoundary.centers)) ×
  Fin ((OriginalBoundary.D hn).patchCount q.1.1.1)

/-- Literal original carrier mass on the original varying selected radius. -/
def φ (i : weights(Index)) : Point → ℝ :=
  originalConicCarrierWeight ((OriginalBoundary.D hn).roots i.1.1.1.1 i.2 i.1.1.1.2)
    (selected(SelectedBoundary.ha') i)

/-- One cube contains every original carrier support before any current phase,
frequency, or finite ceiling is supplied. No weight is normalized or replaced. -/
theorem exists_cube : ∃ B > (0 : ℝ), ∀ i, PatchBounds (weights(φ) i) B 1 :=
  exists_finite_original_carrier_weight_bounds
    (fun i : weights(Index) ↦ (OriginalBoundary.D hn).roots i.1.1.1.1 i.2 i.1.1.1.2)
    (selected(SelectedBoundary.ha'))

/-- The common fixed coordinate cube for these exact original weights. -/
def B : ℝ := (weights(exists_cube)).choose

/-- The chosen common cube has positive radius. -/
theorem hB : 0 < weights(B) := (weights(exists_cube)).choose_spec.1

/-- Every literal original weight has mass bound one in the SAME cube. -/
theorem patchBounds (i : weights(Index)) : PatchBounds (weights(φ) i) (weights(B)) 1 :=
  (weights(exists_cube)).choose_spec.2 i

/-- Original sampling weights have all derivatives without a square-root
regularity assumption or a new carrier cutoff. -/
theorem smooth (i : weights(Index)) : ContDiff ℝ ∞ (weights(φ) i) :=
  contDiff_originalConicCarrierWeight _ (selected(SelectedBoundary.ha') i)

/-- Original weights retain their literal compact carrier support. -/
theorem compact (i : weights(Index)) : HasCompactSupport (weights(φ) i) :=
  hasCompactSupport_originalConicCarrierWeight _ (selected(SelectedBoundary.ha') i)

end OriginalWeights
end JanetCartan.PhysicalSampling
