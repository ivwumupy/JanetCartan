module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableGeometry.Phase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Three-frequency gaps from primitive covector comparison

The consumer is base integration by parts for `app:ch_regular:eq:chain-tail`.
The parent supplies the homogeneous chart comparison; no gradient gap is an
input. Smaller frequencies may vanish.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.NoncomparableGeometry

private theorem chain_bounds {x y e o a b L : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e) (ho : 0 ≤ o)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 1 ≤ L)
    (hxy : x ≤ L*y) (hyx : y ≤ L*x)
    (hxe : x ≤ e+a) (hex : e ≤ x+a) (hyo : y ≤ o+b) (hoy : o ≤ y+b) :
    (x ≤ (L+1)*(e+(a+b)) ∧ e ≤ (L+1)*(x+(a+b))) ∧
    (y ≤ (L+1)*(e+(a+b)) ∧ e ≤ (L+1)*(y+(a+b))) ∧
    (o ≤ (L+1)*(e+(a+b)) ∧ e ≤ (L+1)*(o+(a+b))) := by
  have hL0 : 0 ≤ L := by linarith
  have hye := hyx.trans (mul_le_mul_of_nonneg_left hxe hL0)
  have hxo := hxy.trans (mul_le_mul_of_nonneg_left hyo hL0)
  have hLa := mul_nonneg (show 0 ≤ L-1 by linarith) ha
  have hLb := mul_nonneg (show 0 ≤ L-1 by linarith) hb
  have hLe := mul_nonneg hL0 he
  have hLx := mul_nonneg hL0 hx
  have hLy := mul_nonneg hL0 hy
  have hLo := mul_nonneg hL0 ho
  constructor
  · constructor <;> nlinarith
  constructor <;> constructor <;> nlinarith

private theorem outside_input_bound {v e s A : ℝ} (he : 0 ≤ e) (_hs : 0 ≤ s)
    (hA : 1 ≤ A) (hve : v ≤ A*(e+s)) (hev : e ≤ A*(v+s))
    (hsep : 2*A*v ≤ e ∨ 2*A*e ≤ v) : e ≤ 2*A*s := by
  rcases hsep with h | h
  · nlinarith
  · have := mul_nonneg (show 0 ≤ A-1 by linarith) he
    nlinarith

private theorem three_gap {i e o a b A : ℝ}
    (hi : 0 ≤ i) (he : 0 ≤ e) (_ho : 0 ≤ o) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 1 ≤ A)
    (hI : i ≤ A*(e+(a+b))) (hEi : e ≤ A*(i+(a+b)))
    (hO : o ≤ A*(e+(a+b))) (hEo : e ≤ A*(o+(a+b)))
    (hsep : (2*A*i ≤ e ∨ 2*A*e ≤ i) ∨ (2*A*o ≤ e ∨ 2*A*e ≤ o)) :
    (max i (max e o))^2 / (2*(A*(2*A+1))^2) ≤ a^2+b^2 := by
  have hA0 : 0 < A := by linarith
  have hs : 0 ≤ a+b := by positivity
  have hE : e ≤ 2*A*(a+b) := by
    rcases hsep with h | h
    · exact outside_input_bound he hs hA hI hEi h
    · exact outside_input_bound he hs hA hO hEo h
  have hK : 0 < A*(2*A+1) := by positivity
  have hbnd : max i (max e o) ≤ (A*(2*A+1))*(a+b) := by
    have ht := mul_le_mul_of_nonneg_left (add_le_add_right hE (a+b)) hA0.le
    have hp := mul_nonneg (show 0 ≤ A*(2*A+1)-2*A by nlinarith) hs
    exact max_le (by nlinarith) (max_le (by nlinarith) (by nlinarith))
  have hsq := pow_le_pow_left₀ (le_max_of_le_left hi) hbnd 2
  apply (div_le_iff₀ (by positivity : 0 < 2*(A*(2*A+1))^2)).mpr
  have hs2 : (a+b)^2 ≤ 2*(a^2+b^2) := by nlinarith [sq_nonneg (a-b)]
  have := mul_le_mul_of_nonneg_left hs2 (sq_nonneg (A*(2*A+1)))
  nlinarith

/-- A fixed enlargement determined solely by the primitive comparison constants
in `app:ch_regular:eq:chain-tail`. -/
def annulusFactor (c C : ℝ) : ℝ := max 1 (max c⁻¹ C) + 1

/-- The squared-gap coefficient for `app:ch_regular:eq:chain-tail`; independent
of all frequencies, shell radii, and integration orders. -/
def gapCoefficient (c C : ℝ) : ℝ :=
  (2 * (annulusFactor c C * (2 * annulusFactor c C + 1)) ^ 2)⁻¹

/-- The enlargement is always at least two (`app:ch_regular:eq:chain-tail`). -/
theorem two_le_annulusFactor (c C : ℝ) : 2 ≤ annulusFactor c C := by
  have := le_max_left (1 : ℝ) (max c⁻¹ C)
  unfold annulusFactor
  linarith

/-- The squared-gap constant is strictly positive
(`app:ch_regular:eq:chain-tail`). -/
theorem gapCoefficient_pos (c C : ℝ) : 0 < gapCoefficient c C := by
  have : 0 < annulusFactor c C := lt_of_lt_of_le (by norm_num) (two_le_annulusFactor c C)
  unfold gapCoefficient
  positivity

variable {E : Type*} [NormedAddCommGroup E]

/-- The largest of the three physical frequencies, including the input
(`app:ch_regular:eq:joint-kernel-phase`). -/
def largestFrequency (ξ η ζ : E) : ℝ := max ‖ξ‖ (max ‖η‖ ‖ζ‖)

/-- Exterior of enlarged comparable annuli relative to the input frequency.
The non-strict inequalities deliberately include their boundaries and permit
zero smaller frequencies (`app:ch_regular:eq:chain-tail`). -/
def OutsideInputAnnuli (c C : ℝ) (ξ η ζ : E) : Prop :=
  (2 * annulusFactor c C * ‖ξ‖ ≤ ‖η‖ ∨ 2 * annulusFactor c C * ‖η‖ ≤ ‖ξ‖) ∨
  (2 * annulusFactor c C * ‖ζ‖ ≤ ‖η‖ ∨ 2 * annulusFactor c C * ‖η‖ ≤ ‖ζ‖)

private theorem norm_le_norm_add_gap (v w : E) : ‖v‖ ≤ ‖w‖ + ‖v-w‖ := by
  linarith [norm_sub_norm_le v w]

private theorem primitive_comparison {c C : ℝ} (hc : 0 < c) (g ξ : E)
    (hlow : c * ‖ξ‖ ≤ ‖g‖) (hhigh : ‖g‖ ≤ C * ‖ξ‖) :
    ‖ξ‖ ≤ max 1 (max c⁻¹ C) * ‖g‖ ∧ ‖g‖ ≤ max 1 (max c⁻¹ C) * ‖ξ‖ := by
  constructor
  · have h := mul_le_mul_of_nonneg_left hlow (inv_pos.mpr hc).le
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg g))
  · exact hhigh.trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (norm_nonneg ξ))

/-- Primitive covector comparison gives a gap at the largest of all three
frequencies for the forward physical base covectors. This supplies the
noncomparable shell consumer in `app:ch_regular:eq:chain-tail`. -/
theorem forward_covector_squared_gap {c C : ℝ} (hc : 0 < c)
    (g ξ η ζ : E) (hlow : c * ‖ξ‖ ≤ ‖g‖) (hhigh : ‖g‖ ≤ C * ‖ξ‖)
    (hsep : OutsideInputAnnuli c C ξ η ζ) :
    gapCoefficient c C * largestFrequency ξ η ζ ^ 2 ≤ ‖g-ζ‖^2 + ‖η-ξ‖^2 := by
  obtain ⟨hξg, hgξ⟩ := primitive_comparison hc g ξ hlow hhigh
  have h := chain_bounds (norm_nonneg ξ) (norm_nonneg g) (norm_nonneg η) (norm_nonneg ζ)
    (norm_nonneg (η-ξ)) (norm_nonneg (g-ζ)) (le_max_left 1 _) hξg hgξ
    (by simpa only [norm_sub_rev ξ η] using norm_le_norm_add_gap ξ η)
    (norm_le_norm_add_gap η ξ) (norm_le_norm_add_gap g ζ)
    (by simpa only [norm_sub_rev ζ g] using norm_le_norm_add_gap ζ g)
  have hg := three_gap (norm_nonneg ξ) (norm_nonneg η) (norm_nonneg ζ)
    (norm_nonneg (η-ξ)) (norm_nonneg (g-ζ))
    (show 1 ≤ annulusFactor c C from le_trans (by norm_num) (two_le_annulusFactor c C))
    h.1.1 h.1.2 h.2.2.1 h.2.2.2 hsep
  simpa only [gapCoefficient, largestFrequency, div_eq_mul_inv, mul_comm, add_comm] using hg

/-- The inverse orientation retains its distinct base covectors, with the same
constant and annuli (`app:ch_regular:eq:chain-tail`). -/
theorem reverse_covector_squared_gap {c C : ℝ} (hc : 0 < c)
    (g ξ η ζ : E) (hlow : c * ‖ξ‖ ≤ ‖g‖) (hhigh : ‖g‖ ≤ C * ‖ξ‖)
    (hsep : OutsideInputAnnuli c C ξ η ζ) :
    gapCoefficient c C * largestFrequency ξ η ζ ^ 2 ≤ ‖η-g‖^2 + ‖ξ-ζ‖^2 := by
  obtain ⟨hξg, hgξ⟩ := primitive_comparison hc g ξ hlow hhigh
  have h := chain_bounds (norm_nonneg g) (norm_nonneg ξ) (norm_nonneg η) (norm_nonneg ζ)
    (norm_nonneg (η-g)) (norm_nonneg (ξ-ζ)) (le_max_left 1 _) hgξ hξg
    (by simpa only [norm_sub_rev g η] using norm_le_norm_add_gap g η)
    (norm_le_norm_add_gap η g) (norm_le_norm_add_gap ξ ζ)
    (by simpa only [norm_sub_rev ζ ξ] using norm_le_norm_add_gap ζ ξ)
  have hg := three_gap (norm_nonneg ξ) (norm_nonneg η) (norm_nonneg ζ)
    (norm_nonneg (η-g)) (norm_nonneg (ξ-ζ))
    (show 1 ≤ annulusFactor c C from le_trans (by norm_num) (two_le_annulusFactor c C))
    h.2.1.1 h.2.1.2 h.2.2.1 h.2.2.2 hsep
  simpa only [gapCoefficient, largestFrequency, div_eq_mul_inv, mul_comm] using hg

end JanetCartan.FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
