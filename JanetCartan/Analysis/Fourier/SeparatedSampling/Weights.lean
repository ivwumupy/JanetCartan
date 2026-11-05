module

public import JanetCartan.Analysis.Fourier.SeparatedSampling.Geometry

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The deterministic sampling weights

The window and patch hypotheses below are elementary inputs to the counting
argument of `app:ch_waves:thm:sampling`. In particular this module does not assert
that the convolution window has been constructed, or prove the probabilistic
and operator estimates of that theorem.
-/

@[expose] public noncomputable section

namespace JanetCartan.SeparatedSampling

/-- Elementary bounds on the window of `app:ch_waves:thm:sampling`.
The radius is precisely `p/2+1/4`, as for the manuscript's mollified convolution. -/
structure WindowBounds (p : ℕ) (w : ℝ → ℝ) (W : ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ w t
  le_bound : ∀ t, w t ≤ W
  support : ∀ t, w t ≠ 0 → |t| ≤ windowRadius p

/-- A bounded nonnegative patch weight supported in a fixed coordinate cube,
as in `app:ch_waves:thm:sampling`. -/
structure PatchBounds (ψ : Point → ℝ) (B P : ℝ) : Prop where
  radius_nonneg : 0 ≤ B
  nonneg : ∀ z, 0 ≤ ψ z
  le_bound : ∀ z, ψ z ≤ P
  support : ∀ z, ψ z ≠ 0 → ∀ i, |z i| ≤ B

/-- The tensor window `ρ_q` in `app:ch_waves:thm:sampling`. -/
def blockWeight (w : ℝ → ℝ) (h : ℝ) (q : Lattice) (z : Point) : ℝ :=
  ∏ i, w (z i / h - (q i : ℝ))

/-- The literal weight `μ_{q,m}` in `app:ch_waves:thm:sampling`. -/
def weight (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ) (U : Lattice → Point)
    (a : Sample) : ℝ :=
  h ^ 3 * ψ (node h U a) * blockWeight w h a.1 (node h U a)

variable {p : ℕ} {w : ℝ → ℝ} {W : ℝ} {ψ : Point → ℝ} {B P : ℝ}
  {h : ℝ} {U : Lattice → Point}

/-- Nonzero sample weights lie in the patch and in their block window
(`app:ch_waves:thm:sampling`). -/
theorem weight_ne_zero_factors {a : Sample} (ha : weight ψ w h U a ≠ 0) :
    ψ (node h U a) ≠ 0 ∧ ∀ i, w (node h U a i / h - (a.1 i : ℝ)) ≠ 0 := by
  have hf := mul_ne_zero_iff.mp ha
  exact ⟨(mul_ne_zero_iff.mp hf.1).2,
    fun i ↦ (Finset.prod_ne_zero_iff.mp hf.2) i (Finset.mem_univ i)⟩

/-- A nonzero sampled block is contained in its radius-`h(p/2+1/4)` cube. -/
theorem supported_node (hw : WindowBounds p w W) (hh : 0 < h) {a : Sample}
    (ha : weight ψ w h U a ≠ 0) (i : Fin 3) :
    |node h U a i - h * (a.1 i : ℝ)| ≤ h * windowRadius p := by
  have hs := hw.support _ ((weight_ne_zero_factors ha).2 i)
  have he : node h U a i - h * (a.1 i : ℝ) =
      h * (node h U a i / h - (a.1 i : ℝ)) := by field_simp
  rw [he, abs_mul, abs_of_pos hh]
  exact mul_le_mul_of_nonneg_left hs hh.le

/-- Nonnegative sampling weights (`app:ch_waves:thm:sampling`). -/
theorem weight_nonneg (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 ≤ h) (a : Sample) : 0 ≤ weight ψ w h U a := by
  exact mul_nonneg (mul_nonneg (pow_nonneg hh _) (hψ.nonneg _))
    (Finset.prod_nonneg fun _ _ ↦ hw.nonneg _)

/-- Each sample weighs at most `h³ P W³`, independent of accuracy
(`app:ch_waves:thm:sampling`). -/
theorem weight_le (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 ≤ h) (a : Sample) : weight ψ w h U a ≤ h ^ 3 * (P * W ^ 3) := by
  have hP : 0 ≤ P := (hψ.nonneg 0).trans (hψ.le_bound 0)
  have hρ : blockWeight w h a.1 (node h U a) ≤ W ^ 3 := by
    calc
      _ ≤ ∏ _ : Fin 3, W := Finset.prod_le_prod₀
        (fun _ _ ↦ hw.nonneg _) (fun _ _ ↦ hw.le_bound _)
      _ = _ := by simp
  calc
    _ ≤ (h ^ 3 * P) * W ^ 3 := mul_le_mul
      (mul_le_mul_of_nonneg_left (hψ.le_bound _) (pow_nonneg hh _)) hρ
      (Finset.prod_nonneg fun _ _ ↦ hw.nonneg _) (by positivity)
    _ = _ := by ring

/-- The same-color spacing assertion for the actual nonzero weights
of `app:ch_waves:thm:sampling`. -/
theorem nonzero_samples_separated (hw : WindowBounds p w W) (hh : 0 < h)
    {a b : Sample} (ha : weight ψ w h U a ≠ 0) (hb : weight ψ w h U b ≠ 0)
    (hab : a ≠ b) (hc : color p a.1 = color p b.1) :
    h / 2 ≤ ‖node h U a - node h U b‖ :=
  norm_node_sub_ge hh hab hc (supported_node hw hh ha) (supported_node hw hh hb)

/-- A supported node has a uniformly bounded integer offset in its block
(`app:ch_waves:thm:sampling`). -/
theorem offset_bound (hw : WindowBounds p w W) (hh : 0 < h)
    (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) {a : Sample}
    (ha : weight ψ w h U a ≠ 0) (i : Fin 3) :
    |a.2 i| ≤ (p : ℤ) + 2 := by
  have hs := abs_le.mp (supported_node hw hh ha i)
  have hu := hU a.1 i
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hm : |(a.2 i : ℝ)| ≤ (p : ℝ) + 2 := by
    apply abs_le.mpr
    dsimp [node, windowRadius] at hs
    constructor <;> nlinarith
  exact_mod_cast hm

/-- Block centers contributing nonzero weights remain in the enlarged bounded patch. -/
theorem block_coordinate_bound (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 < h) (hh₁ : h ≤ 1) {a : Sample} (ha : weight ψ w h U a ≠ 0)
    (i : Fin 3) : |(a.1 i : ℝ)| ≤ (B + (p : ℝ) + 2) / h := by
  have hs := abs_le.mp (supported_node hw hh ha i)
  have hz := abs_le.mp (hψ.support _ (weight_ne_zero_factors ha).1 i)
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  apply abs_le.mpr
  dsimp [windowRadius] at hs
  constructor
  · rw [neg_le, le_div_iff₀ hh]
    nlinarith
  · rw [le_div_iff₀ hh]
    nlinarith

/-- Euclidean version of same-color spacing for the actual nonzero samples
of `app:ch_waves:thm:sampling`. -/
theorem euclidean_nonzero_samples_separated (hw : WindowBounds p w W) (hh : 0 < h)
    {a b : Sample} (ha : weight ψ w h U a ≠ 0) (hb : weight ψ w h U b ≠ 0)
    (hab : a ≠ b) (hc : color p a.1 = color p b.1) :
    h / 2 ≤ ‖(WithLp.toLp 2 (node h U a) : EuclideanSpace ℝ (Fin 3)) -
      WithLp.toLp 2 (node h U b)‖ :=
  euclidean_node_sub_ge hh hab hc (supported_node hw hh ha) (supported_node hw hh hb)

end JanetCartan.SeparatedSampling
