module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic
import Mathlib.Tactic.Linarith

/-!
# Larger-frequency bounds for graph factors

The noncomparable-frequency part of `app:ch_regular:lem:finite-chain`. All
bounds concern actual partial derivatives. The parent must supply covector
comparability on the homogeneous phase's actual conic domain, with constants
uniform in its low geometry; no kernel estimate is an input here.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Graph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
private theorem separated_norm_gap (a b : E)
    (h : 2 * ‖a‖ ≤ ‖b‖ ∨ 2 * ‖b‖ ≤ ‖a‖) :
    max ‖a‖ ‖b‖ / 2 ≤ ‖a-b‖ := by
  rcases h with h | h
  · rw [max_eq_right (by linarith [norm_nonneg a])]
    have hg := norm_sub_norm_le b a
    rw [norm_sub_rev b a] at hg
    linarith
  · rw [max_eq_left (by linarith [norm_nonneg b])]
    linarith [norm_sub_norm_le a b]

private theorem comparable_covector_gap (D : E →L[ℝ] ℝ) (ξ ζ : E)
    {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C)
    (hlow : c * ‖ξ‖ ≤ ‖D‖) (hhigh : ‖D‖ ≤ C * ‖ξ‖)
    (hsep : 2 * C * ‖ξ‖ ≤ ‖ζ‖ ∨ 2 * ‖ζ‖ ≤ c * ‖ξ‖) :
    c * max ‖ξ‖ ‖ζ‖ / 2 ≤ ‖D - innerSL ℝ ζ‖ := by
  have h1 := norm_sub_norm_le D (innerSL ℝ ζ)
  have h2 := norm_sub_norm_le (innerSL ℝ ζ) D
  rw [norm_sub_rev (innerSL ℝ ζ) D] at h2
  simp only [innerSL_apply_norm] at h1 h2
  rcases hsep with hsep | hsep
  · rw [max_eq_right (by nlinarith [norm_nonneg ξ])]
    nlinarith [norm_nonneg ζ]
  · rw [max_eq_left (by nlinarith [norm_nonneg ξ])]
    linarith

/-- The actual forward `z` derivative controls the larger input/graph frequency
outside their comparable annulus (`app:ch_regular:lem:finite-chain`). -/
theorem forward_input_frequency_gap (φ : E → E → ℝ) (x y u z ξ η ζ : E)
    (hsep : 2 * ‖η‖ ≤ ‖ξ‖ ∨ 2 * ‖ξ‖ ≤ ‖η‖) :
    max ‖η‖ ‖ξ‖ / 2 ≤
      ‖fderiv ℝ (fun v => forwardPhase φ x y u v ξ η ζ) z‖ := by
  rw [fderiv_forwardPhase_z, innerSL_apply_norm]
  exact separated_norm_gap η ξ hsep

/-- Explicit covector comparability gives the larger-frequency gap for the
actual forward `u` derivative (`app:ch_regular:lem:finite-chain`). The constants
are low geometric inputs from the parent's homogeneous inverse chart. -/
theorem forward_output_frequency_gap (φ : E → E → ℝ) (x y u z ξ η ζ : E)
    (hφ : DifferentiableAt ℝ (fun v => φ v ξ) u)
    {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C)
    (hlow : c * ‖ξ‖ ≤ ‖fderiv ℝ (fun v => φ v ξ) u‖)
    (hhigh : ‖fderiv ℝ (fun v => φ v ξ) u‖ ≤ C * ‖ξ‖)
    (hsep : 2 * C * ‖ξ‖ ≤ ‖ζ‖ ∨ 2 * ‖ζ‖ ≤ c * ‖ξ‖) :
    c * max ‖ξ‖ ‖ζ‖ / 2 ≤
      ‖fderiv ℝ (fun v => forwardPhase φ x y v z ξ η ζ) u‖ := by
  rw [fderiv_forwardPhase_u φ x y u z ξ η ζ hφ]
  exact comparable_covector_gap _ ξ ζ hc hc1 hC hlow hhigh hsep

/-- The actual reverse `z` derivative controls the larger output/graph frequency
(`app:ch_regular:lem:finite-chain`). -/
theorem reverse_output_frequency_gap (φ : E → E → ℝ) (x y u z ξ η ζ : E)
    (hsep : 2 * ‖ζ‖ ≤ ‖ξ‖ ∨ 2 * ‖ξ‖ ≤ ‖ζ‖) :
    max ‖ζ‖ ‖ξ‖ / 2 ≤
      ‖fderiv ℝ (fun v => reversePhase φ x y u v ξ η ζ) z‖ := by
  simp only [reversePhase_eq_neg_swap, fderiv_fun_neg, norm_neg]
  exact forward_input_frequency_gap φ y x u z ξ ζ η hsep

/-- The actual reverse `u` derivative controls the larger input/graph frequency
using the same uniform covector comparability (`app:ch_regular:lem:finite-chain`). -/
theorem reverse_input_frequency_gap (φ : E → E → ℝ) (x y u z ξ η ζ : E)
    (hφ : DifferentiableAt ℝ (fun v => φ v ξ) u)
    {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 ≤ C)
    (hlow : c * ‖ξ‖ ≤ ‖fderiv ℝ (fun v => φ v ξ) u‖)
    (hhigh : ‖fderiv ℝ (fun v => φ v ξ) u‖ ≤ C * ‖ξ‖)
    (hsep : 2 * C * ‖ξ‖ ≤ ‖η‖ ∨ 2 * ‖η‖ ≤ c * ‖ξ‖) :
    c * max ‖ξ‖ ‖η‖ / 2 ≤
      ‖fderiv ℝ (fun v => reversePhase φ x y v z ξ η ζ) u‖ := by
  simp only [reversePhase_eq_neg_swap, fderiv_fun_neg, norm_neg]
  exact forward_output_frequency_gap φ y x u z ξ ζ η hφ hc hc1 hC hlow hhigh hsep

end JanetCartan.FiniteChain.Graph
