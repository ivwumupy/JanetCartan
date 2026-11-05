module

public import JanetCartan.Analysis.Operator.GradedInverse.Neumann
public import JanetCartan.Analysis.Operator.GradedInverse.Scale

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One Neumann inverse at every order

This is the inverse/regularity argument of `app:ch_regular:thm:exact-correction`,
including `app:ch_regular:eq:inverse-tame` with the original shift `β_* = b`.
The contraction bound and `app:ch_regular:eq:one-gain-tame` are inputs; this
module does not construct the localized residual or prove its analytic estimates.

All orders use `neumannInverse K`, formed on the complete base space. Higher
norms need not make `K` a contraction. The constants depend only on the base
contraction bound and the one-gain constants, not on the coefficient profile.
Thus they also apply uniformly to the coefficient families in
`app:ch_regular:thm:fixed-high` once the corresponding input bounds are supplied.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace GradedScale

/-- The exact input estimate `app:ch_regular:eq:one-gain-tame`, including its
regularity assertion. Here `a r` represents the coefficient norm at order `r`,
and `b` is the fixed derivative shift. This asserts properties of `K`, not of
its inverse. -/
structure HasOneGain (G : GradedScale E) (K : E →L[ℝ] E)
    (C a : ℕ → ℝ) (b : ℕ) : Prop where
  regularity : ∀ s x, x ∈ G.level s → K x ∈ G.level (s + 1)
  bound : ∀ s x, x ∈ G.level s →
    G.gradeNorm (s + 1) (K x) ≤
      C (s + 1) * (G.gradeNorm s x + (1 + a (s + 1 + b)) * ‖x‖)

variable [CompleteSpace E] (G : GradedScale E) (K : E →L[ℝ] E)

/-- The finite regularity bootstrap in `app:ch_regular:thm:exact-correction`:
the same base-space Neumann inverse preserves every level. -/
theorem neumannInverse_mem (hK : ‖K‖ < 1)
    (hgain : ∀ s x, x ∈ G.level s → K x ∈ G.level (s + 1))
    (s : ℕ) {f : E} (hf : f ∈ G.level s) : neumannInverse K f ∈ G.level s := by
  induction s with
  | zero => exact G.mem_zero _
  | succ s ih =>
    have hz := ih (G.antitone_level (Nat.le_succ s) hf)
    have hKz := hgain s (neumannInverse K f) hz
    rw [neumannInverse_eq_sub K hK f]
    exact (G.level (s + 1)).sub_mem hf hKz

/-- Preservation of all levels by one operator
(`app:ch_regular:thm:exact-correction`). -/
theorem isSmooth_neumannInverse (hK : ‖K‖ < 1)
    (hgain : ∀ s x, x ∈ G.level s → K x ∈ G.level (s + 1))
    {f : E} (hf : G.IsSmooth f) : G.IsSmooth (neumannInverse K f) :=
  fun s ↦ G.neumannInverse_mem K hK hgain s (hf s)

end GradedScale

/-- Explicit constants for `app:ch_regular:eq:inverse-tame`; these are independent
of the coefficient norms and retain the fixed shift in the one-gain estimate. -/
def inverseTameConstant (θ : ℝ) (C : ℕ → ℝ) : ℕ → ℝ
  | 0 => (1 - θ)⁻¹
  | s + 1 => 1 + C (s + 1) * (inverseTameConstant θ C s + (1 - θ)⁻¹)

theorem inverseTameConstant_pos {θ : ℝ} (hθ : θ < 1) {C : ℕ → ℝ}
    (hC : ∀ s, 0 ≤ C s) (s : ℕ) : 0 < inverseTameConstant θ C s := by
  induction s with
  | zero => exact inv_pos.mpr (sub_pos.mpr hθ)
  | succ s ih =>
    dsimp [inverseTameConstant]
    have := hC (s + 1)
    have := inv_pos.mpr (sub_pos.mpr hθ)
    positivity

namespace GradedScale

variable [CompleteSpace E] (G : GradedScale E) (K : E →L[ℝ] E)

/-- `app:ch_regular:eq:inverse-tame` with `β_* = b`. Only the original
one-gain estimates and the base contraction are assumed. In particular, the
high coefficient norm occurs additively, with no products of coefficient norms. -/
theorem neumannInverse_gradeNorm_le {θ : ℝ} (hK : ‖K‖ ≤ θ) (hθ : θ < 1)
    {C a : ℕ → ℝ} {b : ℕ} (hC : ∀ s, 0 ≤ C s) (ha : ∀ s, 0 ≤ a s)
    (ha_mono : Monotone a) (hgain : G.HasOneGain K C a b)
    (s : ℕ) {f : E} (hf : f ∈ G.level s) :
    G.gradeNorm s (neumannInverse K f) ≤
      inverseTameConstant θ C s * (G.gradeNorm s f + (1 + a (s + b)) * ‖f‖) := by
  have hB : 0 ≤ (1 - θ)⁻¹ := (inv_pos.mpr (sub_pos.mpr hθ)).le
  have hbase := norm_neumannInverse_apply_le K hK hθ f
  induction s with
  | zero =>
    simp only [gradeNorm_zero, inverseTameConstant]
    refine hbase.trans ?_
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg (by linarith [ha (0 + b)]) (norm_nonneg f))) hB
  | succ s ih =>
    have hCs := hC (s + 1)
    have hfprev := G.antitone_level (Nat.le_succ s) hf
    have hzprev := G.neumannInverse_mem K (hK.trans_lt hθ) hgain.regularity s hfprev
    have hstep := G.gradeNorm_sub_le hf (hgain.regularity s _ hzprev)
    rw [← neumannInverse_eq_sub K (hK.trans_lt hθ) f] at hstep
    have hestimate := hgain.bound s (neumannInverse K f) hzprev
    have hprev := ih hfprev
    have hnormmono := G.gradeNorm_mono (Nat.le_succ s) hf
    have hcoeffmono := ha_mono (Nat.add_le_add_right (Nat.le_succ s) b)
    have hA : 0 ≤ 1 + a (s + 1 + b) := by linarith [ha (s + 1 + b)]
    have hD := (inverseTameConstant_pos hθ hC s).le
    have hprev' : G.gradeNorm s (neumannInverse K f) ≤
        inverseTameConstant θ C s *
          (G.gradeNorm (s + 1) f + (1 + a (s + 1 + b)) * ‖f‖) := by
      refine hprev.trans ?_
      gcongr
    calc
      G.gradeNorm (s + 1) (neumannInverse K f)
          ≤ G.gradeNorm (s + 1) f + C (s + 1) *
            (G.gradeNorm s (neumannInverse K f) +
              (1 + a (s + 1 + b)) * ‖neumannInverse K f‖) := by linarith
      _ ≤ G.gradeNorm (s + 1) f + C (s + 1) *
            (inverseTameConstant θ C s *
                (G.gradeNorm (s + 1) f + (1 + a (s + 1 + b)) * ‖f‖) +
              (1 + a (s + 1 + b)) * ((1 - θ)⁻¹ * ‖f‖)) := by
        gcongr
      _ ≤ inverseTameConstant θ C (s + 1) *
            (G.gradeNorm (s + 1) f + (1 + a (s + 1 + b)) * ‖f‖) := by
        dsimp [inverseTameConstant]
        have hF := G.gradeNorm_nonneg (s + 1) f
        have hN := norm_nonneg f
        have hpos : 0 ≤ (1 + a (s + 1 + b)) * ‖f‖ +
            C (s + 1) * (1 - θ)⁻¹ * G.gradeNorm (s + 1) f := by positivity
        nlinarith

/-- Uniform version of `app:ch_regular:eq:inverse-tame`, applicable to the common
families of `app:ch_regular:thm:fixed-high`: choose `D` before the operator, its
coefficient norms, and the derivative shift. All conclusions concern the single
base-space Neumann inverse. -/
theorem exists_uniform_inverse_tame_constants {θ : ℝ} (hθ : θ < 1)
    {C : ℕ → ℝ} (hC : ∀ s, 0 ≤ C s) :
    ∃ D : ℕ → ℝ, (∀ s, 0 < D s) ∧
      ∀ (K : E →L[ℝ] E) (a : ℕ → ℝ) (b : ℕ),
        ‖K‖ ≤ θ → (∀ s, 0 ≤ a s) → Monotone a → G.HasOneGain K C a b →
        ∀ (s : ℕ) (f : E), f ∈ G.level s →
          neumannInverse K f ∈ G.level s ∧
          G.gradeNorm s (neumannInverse K f) ≤
            D s * (G.gradeNorm s f + (1 + a (s + b)) * ‖f‖) := by
  refine ⟨inverseTameConstant θ C, inverseTameConstant_pos hθ hC, ?_⟩
  intro K a b hK ha ha_mono hgain s f hf
  exact ⟨G.neumannInverse_mem K (hK.trans_lt hθ) hgain.regularity s hf,
    G.neumannInverse_gradeNorm_le K hK hθ hC ha ha_mono hgain s hf⟩

end GradedScale
end JanetCartan
