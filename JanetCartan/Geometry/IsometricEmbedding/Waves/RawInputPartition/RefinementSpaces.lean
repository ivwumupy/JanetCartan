module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Radial
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert

/-!
# Shared spaces for the two-shell refinement

The smooth band `[κⱼ,4κⱼ]` is split at `2κⱼ` into the shared sharp annuli
of radii `2κⱼ` and `4κⱼ`. The sharp interface is only a measurable Hilbert
decomposition. Smooth symbol calculus must be applied after reassembly.
All prefixes in `app:ch_waves:eq:sampling-prefix-normal` act on one full finite
input, and keep the two complex components of every original band together.
-/

@[expose] public noncomputable section

open MeasureTheory
namespace JanetCartan.RawInputPartition
open RawInputRealization RawInputHilbert

/-- Two sharp components per original band (`app:ch_waves:thm:individual`). -/
abbrev RefinedIndex (J : ℕ) := Fin J × Fin 2

/-- The literal radii of the two shared annuli: `2κⱼ`, `4κⱼ`
(`app:ch_waves:thm:individual`). -/
def refinedRadius {J : ℕ} (i : RefinedIndex J) : ℝ :=
  (2 : ℝ) ^ (i.1.val + i.2.val)

/-- The same full finite complex Hilbert input for every smaller prefix
(`app:ch_waves:eq:sampling-prefix-normal`). -/
abbrev RefinedInput (n J : ℕ) := Input n (refinedRadius (J := J))

/-- The original smooth wide band (`app:ch_waves:thm:individual`). -/
def wideBand (n j : ℕ) : Set (Euclidean (n - 1)) :=
  Metric.closedBall 0 (4 * dyadicScale j) \ Metric.ball 0 (dyadicScale j)

/-- Literal complex Lebesgue datum on one original wide band
(`app:ch_waves:thm:individual`). -/
abbrev WideBandL2 (n j : ℕ) := Lp ℂ 2 (volume.restrict (wideBand n j))

/-- Finite Hilbert sum of original wide-band data, prior to refinement
(`app:ch_waves:thm:individual`). -/
abbrev WideInput (n J : ℕ) := PiLp 2 (fun j : Fin J ↦ WideBandL2 n j.val)

/-- Measurability of the original wide band (`app:ch_waves:thm:individual`). -/
theorem measurableSet_wideBand (n j : ℕ) : MeasurableSet (wideBand n j) :=
  measurableSet_closedBall.diff measurableSet_ball

/-- The first refined radius is exactly `2κⱼ` (`app:ch_waves:thm:individual`). -/
theorem refinedRadius_zero {J : ℕ} (j : Fin J) :
    refinedRadius (j, (0 : Fin 2)) = 2 * dyadicScale j.val := by
  simp only [refinedRadius, Fin.val_zero, Nat.add_zero, dyadicScale]
  ring

/-- The second refined radius is exactly `4κⱼ` (`app:ch_waves:thm:individual`). -/
theorem refinedRadius_one {J : ℕ} (j : Fin J) :
    refinedRadius (j, (1 : Fin 2)) = 4 * dyadicScale j.val := by
  simp only [refinedRadius, Fin.val_one, dyadicScale, pow_succ]
  ring

/-- Grouped projection retaining precisely original labels `j < L`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def refinedPrefix (n J L : ℕ) : RefinedInput n J →L[ℂ] RefinedInput n J :=
  prefixProjection (fun i : RefinedIndex J ↦ i.1.val + 1) L

/-- Both components and quadratures have the same literal prefix action
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem refinedPrefix_apply (n J L : ℕ) (v : RefinedInput n J) (i : RefinedIndex J) :
    refinedPrefix n J L v i = if i.1.val < L then v i else 0 := by
  simp [refinedPrefix, prefixProjection, coordinateProjection_apply]

/-- Every grouped prefix is a contraction on the same full input
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_refinedPrefix_le (n J L : ℕ) : ‖refinedPrefix n J L‖ ≤ 1 :=
  norm_prefixProjection_le _ _

/-- Every grouped prefix is self-adjoint on the full complex Hilbert input
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_refinedPrefix (n J L : ℕ) :
    (refinedPrefix n J L).adjoint = refinedPrefix n J L := adjoint_prefixProjection _ _

end JanetCartan.RawInputPartition
