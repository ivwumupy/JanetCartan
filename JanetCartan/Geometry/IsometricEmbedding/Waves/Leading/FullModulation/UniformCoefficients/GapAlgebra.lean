module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Inputs

/-!
# Quantitative nonvanishing from the retained adapted denominator

The full neighborhood constructor for `app:ch_waves:thm:leading` derives its
denominator gap from the existing carrier-center bound. On the fixed compact
input range this also bounds the same column, row, and phase gradient away
from zero. No new minor is selected.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation.UniformCoefficients
open NullTransport NullTransport.CoefficientBounds

variable {n : ℕ}

/-- A nonzero adapted denominator forces its original cofactor column to be
nonzero (`app:ch_waves:thm:leading`). -/
theorem right_ne_zero_of_denominator {ν : Euclidean n} {r c : Fin n} {p : Input n}
    (hd : denominator ν r c p ≠ 0) : right c p ≠ 0 := by
  intro hk
  have hk' : rightNullvector (reducedSymbol p.1 p.2) c = 0 := by
    funext j
    exact congrArg (fun v : Euclidean n ↦ v j) hk
  apply hd
  simp [denominator, adaptedTimeCoefficient, transportField, hk']

/-- The same nonzero denominator retains the original cofactor row
(`app:ch_waves:thm:leading`). -/
theorem left_ne_zero_of_denominator {ν : Euclidean n} {r c : Fin n} {p : Input n}
    (hd : denominator ν r c p ≠ 0) : left r p ≠ 0 := by
  intro hl
  apply hd
  change leftNullvector (reducedSymbol p.1 p.2) r = 0 at hl
  simp [denominator, adaptedTimeCoefficient, transportField, hl]

/-- For dimension at least two, a nonzero adapted denominator excludes the
zero phase gradient (`app:ch_waves:thm:leading`). -/
theorem gradient_ne_zero_of_denominator (hn : 2 ≤ n)
    {ν : Euclidean n} {r c : Fin n} {p : Input n}
    (hd : denominator ν r c p ≠ 0) : p.2 ≠ 0 := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  intro hξ
  apply right_ne_zero_of_denominator hd
  have hM : reducedSymbol p.1 p.2 = 0 := by
    rw [hξ]
    exact map_zero (reducedSymbolLinearMap p.1)
  ext j
  change (reducedSymbol p.1 p.2).adjugate j c = 0
  rw [hM, Matrix.adjugate_zero]
  rfl

private theorem compact_positive_lower {E : Type*} [TopologicalSpace E]
    {s : Set E} (hs : IsCompact s) {f : E → ℝ} (hf : ContinuousOn f s)
    (hpos : ∀ x ∈ s, 0 < f x) : ∃ b > (0 : ℝ), ∀ x ∈ s, b ≤ f x := by
  by_cases hne : s.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hne hf
    exact ⟨f x, hpos x hx, hmin⟩
  · exact ⟨1, zero_lt_one, fun x hx ↦ (hne ⟨x, hx⟩).elim⟩

/-- On the low input range, the denominator gap yields quantitative column,
row, and gradient gaps before any current frame is chosen. This is consumed
by the full neighborhood construction (`app:ch_waves:thm:leading`). -/
theorem exists_admissible_input_gaps (hn : 2 ≤ n) (ν : Euclidean n) (r c : Fin n)
    (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ b > (0 : ℝ), ∀ p ∈ admissibleInputs ν r c L ε,
      b ≤ ‖right c p‖ ∧ b ≤ ‖left r p‖ ∧ b ≤ ‖p.2‖ := by
  have hs := compact_admissibleInputs ν r c L ε
  have hden (p) (hp : p ∈ admissibleInputs ν r c L ε) : denominator ν r c p ≠ 0 :=
    abs_pos.mp (hε.trans_le hp.2)
  obtain ⟨bk, hbk, hk⟩ := compact_positive_lower hs (smooth_right c).continuous.norm.continuousOn
    (fun p hp ↦ norm_pos_iff.mpr (right_ne_zero_of_denominator (hden p hp)))
  obtain ⟨bl, hbl, hl⟩ := compact_positive_lower hs (smooth_left r).continuous.norm.continuousOn
    (fun p hp ↦ norm_pos_iff.mpr (left_ne_zero_of_denominator (hden p hp)))
  obtain ⟨bξ, hbξ, hξ⟩ := compact_positive_lower hs continuous_snd.norm.continuousOn
    (fun p hp ↦ norm_pos_iff.mpr (gradient_ne_zero_of_denominator hn (hden p hp)))
  exact ⟨min bk (min bl bξ), lt_min hbk (lt_min hbl hbξ), fun p hp ↦
    ⟨(min_le_left _ _).trans (hk p hp),
      ((min_le_right _ _).trans (min_le_left _ _)).trans (hl p hp),
      ((min_le_right _ _).trans (min_le_right _ _)).trans (hξ p hp)⟩⟩

end JanetCartan.LeadingWave.FullModulation.UniformCoefficients
