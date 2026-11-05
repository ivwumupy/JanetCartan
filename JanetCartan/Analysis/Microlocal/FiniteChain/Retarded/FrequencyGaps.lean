module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Phase
public import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic.Linarith

/-!
# Noncomparable retarded frequency gaps

The larger-frequency gap from `app:ch_regular:lem:finite-chain` is a tangential
one: its components are exactly `τ - κ` and `η - ζ`. No division by `τ` occurs.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E]

/-- The covector size is the genuine Euclidean product norm
(`app:ch_regular:lem:finite-chain`). -/
theorem frequencySize_eq_norm (τ : ℝ) (η : E) :
    frequencySize τ η = ‖WithLp.toLp 2 (τ,η)‖ := by
  simp [frequencySize, WithLp.prod_norm_eq_of_L2, Real.norm_eq_abs, sq_abs]

/-- A pair of noncomparable annuli has a gap controlled by its larger
frequency (`app:ch_regular:lem:finite-chain`). Both differences are tangential. -/
theorem noncomparable_frequency_gap (τ κ : ℝ) (η ζ : E)
    (h : 2 * frequencySize τ η ≤ frequencySize κ ζ ∨
      2 * frequencySize κ ζ ≤ frequencySize τ η) :
    max (frequencySize τ η) (frequencySize κ ζ) / 2 ≤
      frequencySize (τ-κ) (η-ζ) := by
  simp only [frequencySize_eq_norm] at h ⊢
  have he : WithLp.toLp 2 (τ-κ,η-ζ) =
      WithLp.toLp 2 (τ,η) - WithLp.toLp 2 (κ,ζ) := rfl
  rw [he]
  have h₁ := norm_sub_norm_le (WithLp.toLp 2 (τ,η)) (WithLp.toLp 2 (κ,ζ))
  have h₂ := norm_sub_norm_le (WithLp.toLp 2 (κ,ζ)) (WithLp.toLp 2 (τ,η))
  rw [norm_sub_rev] at h₂
  rcases h with h | h
  · rw [max_eq_right (by linarith [norm_nonneg (WithLp.toLp 2 (τ,η))])]
    linarith
  · rw [max_eq_left (by linarith [norm_nonneg (WithLp.toLp 2 (κ,ζ))])]
    linarith

/-- The characteristic branch preserves the full radial annulus
(`app:ch_regular:lem:finite-chain`); in particular its output cannot be zero. -/
theorem frequencySize_eq_of_forward {xi xo : ℝ × E} {κ τ : ℝ} {ζ η : E}
    (h : ForwardRelation xi xo τ η κ ζ) : frequencySize κ ζ = frequencySize τ η := by
  rw [h.2.2.1, h.2.2.2.1, h.2.2.2.2]

end JanetCartan.FiniteChain.Retarded
