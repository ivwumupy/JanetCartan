module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.RadialSeparation
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Chord and sum estimates for frozen patches

The analytic estimates in Step 3 of `app:ch_seed:prop:seed-frozen-menu`.
Derivative closeness to a fixed linear map on a convex set controls the entire
chord, including its lower bound. The local patch construction must still supply
that derivative closeness and the projected linear lower bounds.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Subtracting the reference linear map inside the mean-value estimate gives
the chord error bound in `app:ch_seed:eq:seed-frozen-chord`. -/
theorem chord_error_le_of_derivative_close {S : Set E} (hS : Convex ℝ S)
    {f : E → F} {D : E → E →L[ℝ] F}
    (hf : ∀ x ∈ S, HasFDerivWithinAt f (D x) S x)
    (A : E →L[ℝ] F) {ε : ℝ} (hD : ∀ x ∈ S, ‖D x - A‖ ≤ ε)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖(f y - f x) - A (y - x)‖ ≤ ε * ‖y - x‖ := by
  have h := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz ↦ (hf z hz).sub A.hasFDerivAt.hasFDerivWithinAt) hD hx hy
  convert h using 1
  congr 1
  simp only [map_sub, Pi.sub_apply]
  abel

/-- Both chord inequalities follow from a linear lower bound and uniformly
small derivative error (`app:ch_seed:eq:seed-frozen-chord`). Applying this to
each projected patch proves the projected lower chord inequality. -/
theorem chord_bounds_of_derivative_close {S : Set E} (hS : Convex ℝ S)
    {f : E → F} {D : E → E →L[ℝ] F}
    (hf : ∀ x ∈ S, HasFDerivWithinAt f (D x) S x)
    (A : E →L[ℝ] F) {a ε : ℝ} (hA : ∀ v, a * ‖v‖ ≤ ‖A v‖)
    (hD : ∀ x ∈ S, ‖D x - A‖ ≤ ε)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    (a - ε) * ‖y - x‖ ≤ ‖f y - f x‖ ∧
    ‖f y - f x‖ ≤ (‖A‖ + ε) * ‖y - x‖ := by
  have herr := chord_error_le_of_derivative_close hS hf A hD hx hy
  have hlow := hA (y - x)
  have hupp := A.le_opNorm (y - x)
  have hrev := norm_sub_norm_le (A (y - x)) (f y - f x)
  rw [norm_sub_rev (A (y - x)) (f y - f x)] at hrev
  have hadd := norm_le_insert' (f y - f x) (A (y - x))
  constructor <;> nlinarith

/-- The half-singular-bound choice in Step 3 of
`app:ch_seed:prop:seed-frozen-menu` gives a positive lower chord bound. -/
theorem half_lower_chord_bound {S : Set E} (hS : Convex ℝ S)
    {f : E → F} {D : E → E →L[ℝ] F}
    (hf : ∀ x ∈ S, HasFDerivWithinAt f (D x) S x)
    (A : E →L[ℝ] F) {a : ℝ} (hA : ∀ v, a * ‖v‖ ≤ ‖A v‖)
    (hD : ∀ x ∈ S, ‖D x - A‖ ≤ a / 2)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    a / 2 * ‖y - x‖ ≤ ‖f y - f x‖ := by
  have h := (chord_bounds_of_derivative_close hS hf A hA hD hx hy).1
  convert h using 1
  ring

/-- Sums of two carriers near a fixed center are nonzero when the radius is
small, and their normalized directions stay close to the center direction
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem same_patch_sum_estimates {c x y : E} {δ : ℝ}
    (hx : ‖x - c‖ ≤ δ) (hy : ‖y - c‖ ≤ δ) :
    2 * ‖c‖ - 2 * δ ≤ ‖x + y‖ ∧
    ‖c‖ * ‖NormedSpace.normalize (x + y) - NormedSpace.normalize c‖ ≤ 2 * δ := by
  have heq : x + y - (2 : ℝ) • c = (x - c) + (y - c) := by
    rw [two_smul]; abel
  have herr : ‖x + y - (2 : ℝ) • c‖ ≤ 2 * δ := by
    rw [heq]
    linarith [norm_add_le (x - c) (y - c)]
  have hn : ‖(2 : ℝ) • c‖ = 2 * ‖c‖ := by simp [norm_smul]
  have hrev := norm_sub_norm_le ((2 : ℝ) • c) (x + y)
  rw [norm_sub_rev, hn] at hrev
  have hdir := norm_mul_normalize_sub_le (x + y) ((2 : ℝ) • c)
  rw [hn, NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 2)] at hdir
  constructor <;> nlinarith

/-- Normalized-direction errors decrease every projected bad-subspace gap
by at most that error (`app:ch_seed:prop:seed-frozen-menu`, Steps 3–4). -/
theorem BadDirectionGap.of_normalize_close {n : ℕ} {x y : Euclidean n}
    {δ ε : ℝ} (hy : BadDirectionGap δ y)
    (hxy : ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ ε) :
    BadDirectionGap (δ - ε) x := by
  intro L hL
  have h := norm_sub_norm_le (Lᗮ.orthogonalProjectionOnto (NormedSpace.normalize y))
    (Lᗮ.orthogonalProjectionOnto (NormedSpace.normalize x))
  rw [norm_sub_rev (Lᗮ.orthogonalProjectionOnto (NormedSpace.normalize y)),
    ← map_sub] at h
  have hb := Lᗮ.norm_orthogonalProjectionOnto_apply_le
    (NormedSpace.normalize x - NormedSpace.normalize y)
  linarith [hy L hL]

/-- The lower projected chord bound divided by the full upper chord bound
separates every nonzero difference direction from every bad subspace
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem badDirectionGap_of_chord_bounds {n : ℕ} {v : Euclidean n}
    {d a C : ℝ} (hd : 0 < d) (ha : 0 < a) (hC : 0 < C)
    (hlower : ∀ L ∈ cubeBadSubspaces n, a * d ≤ ‖Lᗮ.orthogonalProjectionOnto v‖)
    (hupper : ‖v‖ ≤ C * d) : BadDirectionGap (a / C) v := by
  intro L hL
  have hv : 0 < ‖v‖ :=
    (mul_pos ha hd).trans_le ((hlower L hL).trans
      (Lᗮ.norm_orthogonalProjectionOnto_apply_le v))
  have hnorm : ‖v‖ * ‖Lᗮ.orthogonalProjectionOnto (NormedSpace.normalize v)‖ =
      ‖Lᗮ.orthogonalProjectionOnto v‖ := by
    calc
      _ = ‖‖v‖ • Lᗮ.orthogonalProjectionOnto (NormedSpace.normalize v)‖ := by
        simp [norm_smul]
      _ = ‖Lᗮ.orthogonalProjectionOnto (‖v‖ • NormedSpace.normalize v)‖ := by
        rw [map_smul]
      _ = _ := by rw [NormedSpace.norm_smul_normalize]
  have hbound : a / C * ‖v‖ ≤ ‖Lᗮ.orthogonalProjectionOnto v‖ := by
    calc
      _ ≤ a / C * (C * d) := mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = a * d := by field_simp
      _ ≤ _ := hlower L hL
  rw [← hnorm] at hbound
  nlinarith

/-- The same-patch sum gap follows by shrinking around a regular center
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). The two explicit smallness
conditions control nonvanishing and the normalized-direction error. -/
theorem same_patch_sum_gap {n : ℕ} {c x y : Euclidean n} {δ γ : ℝ}
    (hc : c ≠ 0) (hgap : BadDirectionGap γ c)
    (hδ : δ < ‖c‖) (hsmall : 2 * δ ≤ ‖c‖ * (γ / 2))
    (hx : ‖x - c‖ ≤ δ) (hy : ‖y - c‖ ≤ δ) :
    x + y ≠ 0 ∧ BadDirectionGap (γ / 2) (x + y) := by
  obtain ⟨hsize, hdir⟩ := same_patch_sum_estimates hx hy
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hclose : ‖NormedSpace.normalize (x + y) - NormedSpace.normalize c‖ ≤ γ / 2 := by
    nlinarith
  refine ⟨norm_pos_iff.mp (by linarith), ?_⟩
  convert hgap.of_normalize_close hclose using 1
  ring

end JanetCartan.FrozenMenu
