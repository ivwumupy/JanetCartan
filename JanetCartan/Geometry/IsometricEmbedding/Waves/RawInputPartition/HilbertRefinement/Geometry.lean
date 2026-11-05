module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.RefinementSpaces
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Geometry of the two sharp pieces

The measurable decomposition used by `bandRefinement` for
`app:ch_waves:thm:individual`. The common boundary has Lebesgue measure zero.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputPartition
open RawInputRealization

/-- The literal two sharp inputs of one smooth band
(`app:ch_waves:thm:individual`). -/
abbrev BandPair (n j : ℕ) :=
  PiLp 2 (fun b : Fin 2 ↦ AnnularL2 n ((2 : ℝ) ^ (j + b.val)))

/-- Membership in the lower sharp piece (`app:ch_waves:thm:individual`). -/
theorem mem_lowerAnnulus {n j : ℕ} {η : Euclidean (n - 1)} :
    η ∈ annulus n ((2 : ℝ) ^ (j + (0 : Fin 2).val)) ↔
      dyadicScale j ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * dyadicScale j := by
  simp only [annulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
    dist_zero_right, not_lt, Fin.val_zero, Nat.add_zero, dyadicScale]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Membership in the upper sharp piece (`app:ch_waves:thm:individual`). -/
theorem mem_upperAnnulus {n j : ℕ} {η : Euclidean (n - 1)} :
    η ∈ annulus n ((2 : ℝ) ^ (j + (1 : Fin 2).val)) ↔
      2 * dyadicScale j ≤ ‖η‖ ∧ ‖η‖ ≤ 4 * dyadicScale j := by
  simp only [annulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
    dist_zero_right, not_lt, Fin.val_one, pow_succ, dyadicScale]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The two literal annuli cover the wide band exactly
(`app:ch_waves:thm:individual`). -/
theorem wideBand_eq_union (n j : ℕ) :
    wideBand n j = annulus n ((2 : ℝ) ^ (j + (0 : Fin 2).val)) ∪
      annulus n ((2 : ℝ) ^ (j + (1 : Fin 2).val)) := by
  ext η
  simp only [Set.mem_union, mem_lowerAnnulus, mem_upperAnnulus, wideBand,
    Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, not_lt]
  have h := dyadicScale_pos j
  constructor
  · rintro ⟨hu, hl⟩
    by_cases hm : ‖η‖ ≤ 2 * dyadicScale j
    · exact Or.inl ⟨hl, hm⟩
    · exact Or.inr ⟨le_of_not_ge hm, hu⟩
  · rintro (⟨hl, hu⟩ | ⟨hl, hu⟩) <;> constructor <;> linarith

/-- Every refined component lies in its original wide band
(`app:ch_waves:thm:individual`). -/
theorem annulus_subset_wideBand (n j : ℕ) (b : Fin 2) :
    annulus n ((2 : ℝ) ^ (j + b.val)) ⊆ wideBand n j := by
  rw [wideBand_eq_union]
  fin_cases b
  · exact Set.subset_union_left
  · exact Set.subset_union_right

/-- All boundary spheres in positive input dimension are null
(`app:ch_waves:thm:individual`). -/
theorem volume_boundarySphere {n : ℕ} (hn : 2 ≤ n) (r : ℝ) :
    volume (Metric.sphere (0 : Euclidean (n - 1)) r) = 0 := by
  let : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  exact Measure.addHaar_sphere volume _ _

/-- Away from a null boundary, the sharp pieces do not overlap
(`app:ch_waves:thm:individual`). -/
theorem ae_not_mem_both_annuli (n j : ℕ) :
    ∀ᵐ η ∂(volume : Measure (Euclidean (n - 1))),
      ¬(η ∈ annulus n ((2 : ℝ) ^ (j + (0 : Fin 2).val)) ∧
        η ∈ annulus n ((2 : ℝ) ^ (j + (1 : Fin 2).val))) := by
  have hs : volume (Metric.sphere (0 : Euclidean (n - 1)) (2 * dyadicScale j)) = 0 :=
    Measure.addHaar_sphere_of_ne_zero volume _ (ne_of_gt (mul_pos (by norm_num) (dyadicScale_pos j)))
  filter_upwards [show ∀ᵐ η ∂volume,
    η ∉ Metric.sphere (0 : Euclidean (n - 1)) (2 * dyadicScale j) from
      (by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hs)] with η hη
  rw [mem_lowerAnnulus, mem_upperAnnulus]
  intro h
  apply hη
  simpa only [Metric.mem_sphere, dist_zero_right] using le_antisymm h.1.2 h.2.1

/-- The constructed smooth radial band is supported on the original wide band
(`app:ch_waves:thm:individual`). -/
theorem radialBand_eq_zero_off_wideBand {n j : ℕ} {η : Euclidean (n - 1)}
    (hη : η ∉ wideBand n j) : radialBand n j η = 0 := by
  simp only [wideBand, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
    dist_zero_right, not_and_or, not_le, not_not] at hη
  rcases hη with hη | hη
  · exact scalarBand_eq_zero_of_ge (le_of_lt hη)
  · exact scalarBand_eq_zero_of_le (le_of_lt hη)

end JanetCartan.RawInputPartition
