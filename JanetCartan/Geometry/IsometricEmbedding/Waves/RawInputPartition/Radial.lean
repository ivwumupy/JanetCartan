module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Scalar
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Spaces
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth Euclidean radial masks

These masks implement `app:ch_waves:thm:individual` on the actual initial
Euclidean space. The radial construction does not impose parity or smoothness
on the manuscript's independently given angular detector.
-/

@[expose] public noncomputable section

namespace JanetCartan.RawInputPartition

/-- Smooth Euclidean band before multiplication by the given detector and
high-pass (`app:ch_waves:thm:individual`). -/
def radialBand (n j : ℕ) (η : Euclidean (n - 1)) : ℝ := scalarBand j ‖η‖

/-- Euclidean low-pass for the unchanged prefix `j < J`
(`app:ch_background:defn:bg-mixed`). -/
def radialPrefix (n J : ℕ) (η : Euclidean (n - 1)) : ℝ := scalarPrefix J ‖η‖

/-- Radial bands are smooth even at zero, where they vanish on a neighborhood
(`app:ch_waves:thm:individual`). -/
theorem contDiff_radialBand (n j : ℕ) {r : ℕ∞} : ContDiff ℝ r (radialBand n j) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases hη : η = 0
  · subst η
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Euclidean (n - 1)) (dyadicScale_pos j)] with η hη
    exact scalarBand_eq_zero_of_le (le_of_lt (by simpa using hη))
  · exact contDiff_bandProfile.contDiffAt.comp η
      ((contDiffAt_id.norm ℝ hη).div_const (dyadicScale j))

/-- The prefix is smooth at zero because it is identically one nearby
(`app:ch_background:defn:bg-mixed`). -/
theorem contDiff_radialPrefix (n J : ℕ) {r : ℕ∞} : ContDiff ℝ r (radialPrefix n J) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases hη : η = 0
  · subst η
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Euclidean (n - 1)) (dyadicScale_pos J)] with η hη
    exact scalarPrefix_eq_one (le_of_lt (by simpa using hη))
  · exact contDiff_transitionAngle.contDiffAt.cos.comp η
      ((contDiffAt_id.norm ℝ hη).div_const (dyadicScale J))

/-- Measurability for the actual annular and carrier measures
(`app:ch_waves:thm:individual`). -/
theorem measurable_radialBand (n j : ℕ) : Measurable (radialBand n j) :=
  (contDiff_radialBand n j (r := 0)).continuous.measurable

/-- Measurability of the unchanged prefix (`app:ch_background:defn:bg-mixed`). -/
theorem measurable_radialPrefix (n J : ℕ) : Measurable (radialPrefix n J) :=
  (contDiff_radialPrefix n J (r := 0)).continuous.measurable

/-- The actual square partition includes every nonzero value of the given
floor-one high-pass (`app:ch_background:defn:bg-row`). -/
theorem sum_radialBand_sq_eq_prefix_sq {n : ℕ} (J : ℕ)
    (χ : Euclidean (n - 1) → ℝ) (hχ : ∀ η, ‖η‖ ≤ 1 → χ η = 0)
    {η : Euclidean (n - 1)} (hη : χ η ≠ 0) :
    ∑ j ∈ Finset.range J, radialBand n j η ^ 2 = radialPrefix n J η ^ 2 := by
  exact sum_scalarBand_sq_eq_prefix_sq J (le_of_lt (lt_of_not_ge (fun h ↦ hη (hχ η h))))

/-- At most two smooth bands meet at any frequency, uniformly in the ceiling
(`app:ch_waves:thm:individual`). -/
theorem radialBand_overlap_card_le {n : ℕ} (s : Finset ℕ) (η : Euclidean (n - 1)) :
    (s.filter (fun j ↦ radialBand n j η ≠ 0)).card ≤ 2 :=
  scalarBand_overlap_card_le s ‖η‖

end JanetCartan.RawInputPartition
