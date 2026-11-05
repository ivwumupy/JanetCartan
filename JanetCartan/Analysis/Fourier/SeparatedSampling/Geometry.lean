module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Int.ModEq

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Geometry of the separated sampling blocks

The deterministic geometry in `app:ch_waves:thm:sampling`. Coordinates on the
three-parameter chart carry the sup norm. The coordinate separation proved here
also gives separation in the Euclidean norm. No probability assumptions are used.
-/

@[expose] public noncomputable section

namespace JanetCartan.SeparatedSampling

/-- Three local parameters `(s,v)` in `app:ch_waves:thm:sampling`. -/
abbrev Point := Fin 3 → ℝ

/-- Integer block labels and lattice offsets in `app:ch_waves:thm:sampling`. -/
abbrev Lattice := Fin 3 → ℤ

/-- Literal sample labels: the block and the lattice offset are both retained. -/
abbrev Sample := Lattice × Lattice

/-- `Z_{q,m} = hq + hm + U_q` in `app:ch_waves:thm:sampling`. -/
def node (h : ℝ) (U : Lattice → Point) (a : Sample) : Point :=
  fun i ↦ h * (a.1 i : ℝ) + h * (a.2 i : ℝ) + U a.1 i

/-- The radius of the convolution window in `app:ch_waves:thm:sampling`. -/
def windowRadius (p : ℕ) : ℝ := (p : ℝ) / 2 + 1 / 4

/-- A block's color, with `q_col = q_quad + 1`, independent of mesh and accuracy. -/
def color (p : ℕ) (q : Lattice) : Fin 3 → Fin (p + 1) := fun i ↦
  ⟨(q i % (p + 1 : ℕ)).toNat, by
    have hpos : (0 : ℤ) < (p + 1 : ℕ) := by positivity
    have hlo := Int.emod_nonneg (q i) (ne_of_gt hpos)
    have hhi := Int.emod_lt_of_pos (q i) hpos
    omega⟩

/-- The fixed number of colors in `app:ch_waves:thm:sampling` is `(p+1)^3`. -/
theorem card_colors (p : ℕ) : Fintype.card (Fin 3 → Fin (p + 1)) = (p + 1) ^ 3 := by
  simp

/-- Distinct integer coordinates of one color differ by at least the color modulus. -/
theorem color_coordinate_gap {p : ℕ} {q r : Lattice}
    (hc : color p q = color p r) {i : Fin 3} (hi : q i ≠ r i) :
    (p : ℝ) + 1 ≤ |(q i : ℝ) - (r i : ℝ)| := by
  have hc' := congrArg (fun c ↦ (c i).val) hc
  have he : q i % (p + 1 : ℕ) = r i % (p + 1 : ℕ) := by
    dsimp [color] at hc'
    norm_cast at hc' ⊢
    have hpos : (0 : ℤ) < (p + 1 : ℕ) := by positivity
    have hq := Int.emod_nonneg (q i) (ne_of_gt hpos)
    have hr := Int.emod_nonneg (r i) (ne_of_gt hpos)
    omega
  have hd : ((p + 1 : ℕ) : ℤ) ∣ q i - r i := by
    rwa [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  have hg := Int.le_abs_of_dvd (sub_ne_zero.mpr hi) hd
  exact_mod_cast hg

/-- The coordinate gap for two distinct supported literal samples of the same color.
This is the spacing assertion of `app:ch_waves:thm:sampling`, uniformly in all shifts. -/
theorem exists_coordinate_separation {p : ℕ} {h : ℝ} (hh : 0 < h)
    {U : Lattice → Point} {a b : Sample} (hab : a ≠ b)
    (hc : color p a.1 = color p b.1)
    (ha : ∀ i, |node h U a i - h * (a.1 i : ℝ)| ≤ h * windowRadius p)
    (hb : ∀ i, |node h U b i - h * (b.1 i : ℝ)| ≤ h * windowRadius p) :
    ∃ i, h / 2 ≤ |node h U a i - node h U b i| := by
  by_cases hq : a.1 = b.1
  · have hm : a.2 ≠ b.2 := fun hm ↦ hab (Prod.ext hq hm)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
    refine ⟨i, ?_⟩
    have hi' : (1 : ℝ) ≤ |(a.2 i : ℝ) - (b.2 i : ℝ)| := by
      have : (1 : ℤ) ≤ |a.2 i - b.2 i| := by
        have := abs_pos.mpr (sub_ne_zero.mpr hi)
        omega
      exact_mod_cast this
    have he : node h U a i - node h U b i = h * ((a.2 i : ℝ) - b.2 i) := by
      simp only [node, hq]
      ring
    rw [he, abs_mul, abs_of_pos hh]
    nlinarith
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hq
    refine ⟨i, ?_⟩
    have hg := color_coordinate_gap hc hi
    have ht : |h * (a.1 i : ℝ) - h * (b.1 i : ℝ)| ≤
        |node h U a i - h * (a.1 i : ℝ)| +
        |node h U a i - node h U b i| +
        |node h U b i - h * (b.1 i : ℝ)| := by
      calc
        _ = |-(node h U a i - h * (a.1 i : ℝ)) +
            (node h U a i - node h U b i) +
            (node h U b i - h * (b.1 i : ℝ))| := by congr 1; ring
        _ ≤ _ := by
          calc
            _ ≤ |-(node h U a i - h * (a.1 i : ℝ)) +
                (node h U a i - node h U b i)| +
                |node h U b i - h * (b.1 i : ℝ)| := abs_add_le _ _
            _ ≤ _ := by
              have ht' := abs_add_le (-(node h U a i - h * (a.1 i : ℝ)))
                (node h U a i - node h U b i)
              rw [abs_neg] at ht'
              linarith
    rw [← mul_sub, abs_mul, abs_of_pos hh] at ht
    have ha' := ha i
    have hb' := hb i
    dsimp [windowRadius] at ha' hb'
    nlinarith [mul_le_mul_of_nonneg_left hg hh.le]

/-- Sup-norm spacing of same-color nodes (`app:ch_waves:thm:sampling`). -/
theorem norm_node_sub_ge {p : ℕ} {h : ℝ} (hh : 0 < h)
    {U : Lattice → Point} {a b : Sample} (hab : a ≠ b)
    (hc : color p a.1 = color p b.1)
    (ha : ∀ i, |node h U a i - h * (a.1 i : ℝ)| ≤ h * windowRadius p)
    (hb : ∀ i, |node h U b i - h * (b.1 i : ℝ)| ≤ h * windowRadius p) :
    h / 2 ≤ ‖node h U a - node h U b‖ := by
  obtain ⟨i, hi⟩ := exists_coordinate_separation hh hab hc ha hb
  exact hi.trans (by simpa using norm_le_pi_norm (node h U a - node h U b) i)

/-- Euclidean spacing of same-color nodes in the parameter chart
(`app:ch_waves:thm:sampling`). -/
theorem euclidean_node_sub_ge {p : ℕ} {h : ℝ} (hh : 0 < h)
    {U : Lattice → Point} {a b : Sample} (hab : a ≠ b)
    (hc : color p a.1 = color p b.1)
    (ha : ∀ i, |node h U a i - h * (a.1 i : ℝ)| ≤ h * windowRadius p)
    (hb : ∀ i, |node h U b i - h * (b.1 i : ℝ)| ≤ h * windowRadius p) :
    h / 2 ≤ ‖(WithLp.toLp 2 (node h U a) : EuclideanSpace ℝ (Fin 3)) -
      WithLp.toLp 2 (node h U b)‖ := by
  obtain ⟨i, hi⟩ := exists_coordinate_separation hh hab hc ha hb
  exact hi.trans (by
    simpa using PiLp.norm_apply_le
      ((WithLp.toLp 2 (node h U a) : EuclideanSpace ℝ (Fin 3)) -
        WithLp.toLp 2 (node h U b)) i)

end JanetCartan.SeparatedSampling
