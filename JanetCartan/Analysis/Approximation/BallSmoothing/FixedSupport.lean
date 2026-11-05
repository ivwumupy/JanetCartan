module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Affine

/-!
# One fixed compact output support inside the prescribed neighborhood

Compactness of the original closed ball gives a fixed positive collar
inside the arbitrary open set `V`. A threshold chosen from that collar
places every actual smoothing output in a single fixed compact subset of
`V`, before the derivative order, approximation order, and input vary.
This proves the support clause in
`app:ch_regular_base:lem:ball-extension`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Choose one compact output support and one geometric scale threshold
before all orders and input fields. This is an actual consequence of the
constructed thin cutoff and the original inclusion of the closed ball in
`V` (`app:ch_regular_base:lem:ball-extension`). -/
theorem exists_affineSmoothing_fixed_support (c : E) {a : ℝ} (ha : 0 < a)
    {V : Set E} (hV : IsOpen V) (hball : closedBall c a ⊆ V) :
    ∃ (K : Set E) (R₀ : ℝ), IsCompact K ∧ K ⊆ V ∧ 1 ≤ R₀ ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (m : ℕ) (f : E → F),
        tsupport (affineSmoothing c a R m f) ⊆ K := by
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_closedBall c a).exists_cthickening_subset_open hV hball
  refine ⟨closedBall c (a + δ), max 1 (a / (4 * δ)), isCompact_closedBall _ _, ?_,
    le_max_left _ _, ?_⟩
  · simpa only [cthickening_closedBall hδ.le ha.le, add_comm] using hδV
  · intro R hR m f
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    have hR0 : 0 < R := zero_lt_one.trans_le hR1
    have haR : a / (4 * δ) ≤ R := (le_max_right _ _).trans hR
    have haR' : a ≤ R * (4 * δ) := (div_le_iff₀ (by positivity)).mp haR
    have hsmall : a / (4 * R) ≤ δ := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    exact (affineSmoothing_tsupport_subset c ha hR1 m f).trans
      (closedBall_subset_closedBall (by linarith))

end JanetCartan.BallSmoothing
