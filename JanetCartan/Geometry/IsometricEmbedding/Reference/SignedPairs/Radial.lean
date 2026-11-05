module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Compact

/-! # Projected gaps for radially separated groups

Step 4 of `app:ch_seed:prop:seed-frozen-menu` and Step 2 of
`app:ch_seed:prop:seed-actual-menu`: radial domination reduces both signs to
the signed dominant carrier. No gap for the actual signed pair is assumed.
-/

@[expose] public noncomputable section

namespace JanetCartan.SignedPairs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Reflection does not change a projected angular gap
(`app:rem:exhaustive-signed-pairs`). -/
theorem norm_project_normalize_sign (P : E →L[ℝ] F) (y : E) {t : ℝ}
    (ht : |t| = 1) :
    ‖P (NormedSpace.normalize (t • y))‖ = ‖P (NormedSpace.normalize y)‖ := by
  rcases (abs_eq zero_le_one).mp ht with rfl | rfl <;> simp

/-- Closeness to a frozen direction transfers its projected angular gap
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem projected_gap_of_direction_close (P : E →L[ℝ] F)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) {u v : E} {α ε : ℝ}
    (hv : α ≤ ‖P v‖) (he : ‖u - v‖ ≤ ε) : α - ε ≤ ‖P u‖ := by
  have htriangle : ‖P v‖ ≤ ‖P u‖ + ‖u - v‖ := by
    calc
      _ ≤ ‖P u‖ + ‖P v - P u‖ := norm_le_insert' _ _
      _ ≤ _ := by
        rw [← map_sub]
        exact add_le_add_right ((hP (v - u)).trans_eq (norm_sub_rev v u)) _
  linarith

/-- Norms decompose into the radial size and the projected unit direction
(`app:ch_seed:prop:seed-actual-menu`, Step 2). This identity also holds at zero. -/
theorem norm_project_eq_mul_normalize (P : E →L[ℝ] F) (v : E) :
    ‖P v‖ = ‖v‖ * ‖P (NormedSpace.normalize v)‖ := by
  conv_lhs => rw [← NormedSpace.norm_smul_normalize v]
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_norm]

/-- Both signs of a cross-group pair retain lower/upper radial bounds and a
projected gap under low perturbations. The only angular hypothesis concerns
the frozen dominant carrier (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem radial_projected_pair (P : E →L[ℝ] F) (hP : ∀ v, ‖P v‖ ≤ ‖v‖)
    {a b η r R s t α : ℝ} {x y x' y' : E}
    (ha : 0 < a) (hb : 0 ≤ b) (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hα : 4 * η < α) (hr : 0 ≤ r) (hR : 0 < R) (hrR : r ≤ R)
    (hdom : r * (b + a) ≤ η * a * R)
    (hx : ‖x‖ ≤ b) (hy : a ≤ ‖y‖) (hyb : ‖y‖ ≤ b)
    (hx' : ‖x' - x‖ ≤ η * a) (hy' : ‖y' - y‖ ≤ η * a)
    (hs : |s| = 1) (ht : |t| = 1)
    (hgap : α ≤ ‖P (NormedSpace.normalize y)‖) :
    a / 2 * R ≤ ‖s • (r • x') + t • (R • y')‖ ∧
    ‖s • (r • x') + t • (R • y')‖ ≤ 2 * (b + a) * R ∧
    α - 4 * η ≤ ‖P (NormedSpace.normalize (s • (r • x') + t • (R • y')))‖ ∧
    (a / 2 * (α - 4 * η)) * R ≤ ‖P (s • (r • x') + t • (R • y'))‖ := by
  obtain ⟨hl, hu, hd⟩ := radial_pair_estimates ha hb hη hη' hr hR hrR hdom
    hx hy hyb hx' hy' hs ht
  have hg : α ≤ ‖P (NormedSpace.normalize (t • y))‖ := by
    rwa [norm_project_normalize_sign P y ht]
  have hp := projected_gap_of_direction_close P hP hg hd
  refine ⟨hl, hu, hp, ?_⟩
  rw [norm_project_eq_mul_normalize]
  nlinarith [mul_le_mul hl hp (by linarith : 0 ≤ α - 4 * η)
    (norm_nonneg (s • (r • x') + t • (R • y')))]

end JanetCartan.SignedPairs
