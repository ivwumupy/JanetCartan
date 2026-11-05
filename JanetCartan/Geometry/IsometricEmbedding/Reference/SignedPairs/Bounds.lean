module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.RadialSeparation
public import Mathlib.Analysis.Calculus.MeanValue

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Quantitative stability of signed covectors

The segment and perturbation estimates of `app:ch_seed:prop:seed-actual-menu`,
Step 2. Derivative errors are integrated on the entire convex parameter cube;
thus their errors retain the length of even an arbitrarily short chord.
-/

@[expose] public noncomputable section

namespace JanetCartan.SignedPairs

variable {Z E F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The convex segment estimate for the gradient error in
`app:ch_seed:eq:seed-actual-chord`. Within-derivatives allow closed cubes. -/
theorem chord_error_of_derivative_error {S : Set Z} (hS : Convex ℝ S)
    {f g : Z → E} {f' g' : Z → Z →L[ℝ] E} {ε : ℝ}
    (hf : ∀ z ∈ S, HasFDerivWithinAt f (f' z) S z)
    (hg : ∀ z ∈ S, HasFDerivWithinAt g (g' z) S z)
    (he : ∀ z ∈ S, ‖g' z - f' z‖ ≤ ε)
    {z w : Z} (hz : z ∈ S) (hw : w ∈ S) :
    ‖(g z - g w) - (f z - f w)‖ ≤ ε * ‖z - w‖ := by
  have h := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz ↦ (hg z hz).sub (hf z hz)) he hw hz
  change ‖(g z - f z) - (g w - f w)‖ ≤ _ at h
  convert h using 2; abel

/-- Contractive projections preserve the frozen lower chord bound under a
relative error; the upper bound persists as well
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem projected_pair_perturbation (P : E →L[ℝ] F)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) {u v : E} {c C ε d : ℝ}
    (hl : c * d ≤ ‖P v‖) (hu : ‖v‖ ≤ C * d)
    (he : ‖u - v‖ ≤ ε * d) :
    (c - ε) * d ≤ ‖P u‖ ∧ ‖u‖ ≤ (C + ε) * d := by
  have hp : ‖P v‖ ≤ ‖P u‖ + ‖u - v‖ := by
    calc
      ‖P v‖ ≤ ‖P u‖ + ‖P v - P u‖ := norm_le_insert' _ _
      _ ≤ ‖P u‖ + ‖u - v‖ := by
        rw [← map_sub]
        exact add_le_add_right ((hP (v - u)).trans_eq (norm_sub_rev v u)) _
  constructor
  · nlinarith
  · have := norm_le_insert' u v
    nlinarith

/-- Persistence of the two displayed chord estimates on an entire convex
cube, including the equal-parameter case (`app:ch_seed:eq:seed-actual-chord`). -/
theorem projected_chord_stability {S : Set Z} (hS : Convex ℝ S)
    (P : E →L[ℝ] F) (hP : ∀ v, ‖P v‖ ≤ ‖v‖)
    {f g : Z → E} {f' g' : Z → Z →L[ℝ] E} {c C ε : ℝ}
    (hf : ∀ z ∈ S, HasFDerivWithinAt f (f' z) S z)
    (hg : ∀ z ∈ S, HasFDerivWithinAt g (g' z) S z)
    (he : ∀ z ∈ S, ‖g' z - f' z‖ ≤ ε)
    (hl : ∀ z ∈ S, ∀ w ∈ S, c * ‖z - w‖ ≤ ‖P (f z - f w)‖)
    (hu : ∀ z ∈ S, ∀ w ∈ S, ‖f z - f w‖ ≤ C * ‖z - w‖)
    {z w : Z} (hz : z ∈ S) (hw : w ∈ S) :
    (c - ε) * ‖z - w‖ ≤ ‖P (g z - g w)‖ ∧
      ‖g z - g w‖ ≤ (C + ε) * ‖z - w‖ :=
  projected_pair_perturbation P hP (hl z hz w hw) (hu z hz w hw)
    (chord_error_of_derivative_error hS hf hg he hz hw)

omit [NormedSpace ℝ E] in
/-- Uniform value errors control sums, including a repeated index, in
`app:rem:exhaustive-signed-pairs`. -/
theorem sum_error {u v u₀ v₀ : E} {ε : ℝ}
    (hu : ‖u - u₀‖ ≤ ε) (hv : ‖v - v₀‖ ≤ ε) :
    ‖(u + v) - (u₀ + v₀)‖ ≤ 2 * ε := by
  calc
    _ = ‖(u - u₀) + (v - v₀)‖ := by congr 1; abel
    _ ≤ ε + ε := norm_add_le_of_le hu hv
    _ = _ := by ring

/-- The error of both cross-group signs, with the fixed radial labels retained
(`app:rem:exhaustive-signed-pairs`). -/
theorem radial_signed_error {u v u₀ v₀ : E} {ε r R s t : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hs : |s| = 1) (ht : |t| = 1)
    (hu : ‖u - u₀‖ ≤ ε) (hv : ‖v - v₀‖ ≤ ε) :
    ‖(s • (r • u) + t • (R • v)) -
      (s • (r • u₀) + t • (R • v₀))‖ ≤ (r + R) * ε := by
  have hid : (s • (r • u) + t • (R • v)) -
      (s • (r • u₀) + t • (R • v₀)) =
      s • (r • (u - u₀)) + t • (R • (v - v₀)) := by
    simp only [smul_sub]; abel
  rw [hid]
  calc
    _ ≤ ‖s • (r • (u - u₀))‖ + ‖t • (R • (v - v₀))‖ := norm_add_le _ _
    _ = r * ‖u - u₀‖ + R * ‖v - v₀‖ := by
      simp [norm_smul, hs, ht, abs_of_nonneg hr, abs_of_nonneg hR]
    _ ≤ r * ε + R * ε := add_le_add
      (mul_le_mul_of_nonneg_left hu hr) (mul_le_mul_of_nonneg_left hv hR)
    _ = _ := by ring

/-- A projected lower bound and an upper norm bound give an angular gap,
uniform down to arbitrarily short nonzero chords
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem normalized_projection_lower (P : E →L[ℝ] F)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) {u : E} {c C d : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hd : 0 < d)
    (hl : c * d ≤ ‖P u‖) (hu : ‖u‖ ≤ C * d) :
    u ≠ 0 ∧ c / C ≤ ‖P (NormedSpace.normalize u)‖ := by
  have hpos : 0 < ‖u‖ := (mul_pos hc hd).trans_le (hl.trans (hP u))
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  rw [NormedSpace.normalize, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos)]
  have hm : c * ‖u‖ ≤ C * ‖P u‖ := by nlinarith
  apply (div_le_iff₀ hC).mpr
  calc
    c = (c * ‖u‖) * ‖u‖⁻¹ := by field_simp
    _ ≤ (C * ‖P u‖) * ‖u‖⁻¹ := mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr hpos.le)
    _ = _ := by ring

/-- Exact frequency comparison at the true beat. Taking `d = ‖z-w‖`
gives `lam‖z-w‖`, whereas sums and cross-group pairs use `d = 1`
(`app:rem:exhaustive-signed-pairs`). -/
theorem frequency_bounds {u : E} {c C d lam : ℝ} (hlam : 0 ≤ lam)
    (hl : c * d ≤ ‖u‖) (hu : ‖u‖ ≤ C * d) :
    c * (lam * d) ≤ ‖lam • u‖ ∧ ‖lam • u‖ ≤ C * (lam * d) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hl hlam]
  · nlinarith [mul_le_mul_of_nonneg_left hu hlam]

end JanetCartan.SignedPairs
