module

public import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Banach-valued carrier Taylor remainder

The Taylor estimate used in `app:ch_waves:eq:background-quadrature`.
The derivative hypothesis bounds the actual iterated Fréchet derivative.
-/

@[expose] public noncomputable section

namespace JanetCartan.Sampling.BackgroundQuadrature

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The Taylor polynomial through degree `p-1` from the background quadrature
proof of `app:ch_waves:thm:sampling`, evaluated at displacement `y`. -/
def carrierTaylor (f : E → V) (p : ℕ) (x y : E) : V :=
  ∑ k ∈ Finset.range p, (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ y)

/-- Banach-valued Taylor remainder controlled by the genuine `p`-th derivative
on the segment. This is the analytic remainder step in
`app:ch_waves:eq:background-quadrature`; no cancellation is assumed. -/
theorem norm_sub_carrierTaylor_le {f : E → V} {p : ℕ} (hp : 0 < p)
    {x y : E} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ p f (x + t • y))
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ p f (x + t • y)‖ ≤ A) :
    ‖f (x + y) - carrierTaylor f p x y‖ ≤ A * ‖y‖ ^ p := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have he := map_add_eq_sum_add_integral_iteratedFDeriv hf
  rw [carrierTaylor, he, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (n.factorial : ℝ)⁻¹)]
  have hi : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n •
      iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y)‖ ≤ A * ‖y‖ ^ (n + 1) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := A * ‖y‖ ^ (n + 1)) ?_).trans_eq (by simp)
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have ht1 : 1 - t ≤ 1 := by linarith [ht.1]
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ht0 _)]
    have hd := (iteratedFDeriv ℝ (n + 1) f (x + t • y)).le_opNorm (fun _ ↦ y)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hd
    calc
      _ ≤ 1 * (A * ‖y‖ ^ (n + 1)) := mul_le_mul
        (pow_le_one₀ ht0 ht1) (hd.trans (mul_le_mul_of_nonneg_right (hD t ht')
          (by positivity))) (norm_nonneg _) (by positivity)
      _ = _ := one_mul _
  have hfact : (n.factorial : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast Nat.factorial_pos n
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * (A * ‖y‖ ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ 1 * (A * ‖y‖ ^ (n + 1)) :=
      mul_le_mul_of_nonneg_right hfact (by positivity)
    _ = _ := one_mul _

end JanetCartan.Sampling.BackgroundQuadrature
