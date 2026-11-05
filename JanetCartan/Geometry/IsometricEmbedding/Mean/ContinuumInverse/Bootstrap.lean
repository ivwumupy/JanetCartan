module

public import JanetCartan.Analysis.Operator.CoerciveInverse
public import JanetCartan.Analysis.Operator.GradedInverse.Scale

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quantitative bootstrap for one coercive inverse

The induction in `app:ch_background:prop:bg-inverse`, separated from its analytic
inputs. All levels are subspaces of one Hilbert space, and every conclusion uses
Mathlib's single `E.inverse` on that space. The coefficient shift stays fixed.

The one-step elliptic regularity and a priori estimate are explicit hypotheses.
For the continuum normal they must still be proved from the actual PDO
commutator, difference quotients, and uniqueness in `H⁻¹`. In particular, this
module does not assert those analytic facts for the continuum normal.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumInverse

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Constants for the induction in `app:ch_background:prop:bg-inverse`. They
depend on the gap and the elliptic constants, not on the high coefficient norms
or on their derivative shift. -/
def bootstrapConstant (c : ℝ) (C : ℕ → ℝ) : ℕ → ℝ
  | 0 => c⁻¹
  | s + 1 => C (s + 1) * (1 + bootstrapConstant c C s + c⁻¹)

/-- Nonnegativity of the constants used in `app:ch_background:eq:bg-r-inverse`. -/
theorem bootstrapConstant_nonneg {c : ℝ} (hc : 0 < c) {C : ℕ → ℝ}
    (hC : ∀ s, 0 ≤ C s) (s : ℕ) : 0 ≤ bootstrapConstant c C s := by
  induction s with
  | zero => exact inv_nonneg.mpr hc.le
  | succ s ih =>
    dsimp [bootstrapConstant]
    have := hC (s + 1)
    have := inv_nonneg.mpr hc.le
    positivity

/-- The regularity induction of `app:ch_background:prop:bg-inverse`, conditional
on the one-step elliptic regularity implication for `E`, rather than regularity
of a separately constructed inverse at each order. -/
theorem inverse_mem (G : GradedScale H) (E : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪E v, v⟫_ℝ)
    (hreg : ∀ s v, v ∈ G.level s → E v ∈ G.level (s + 1) →
      v ∈ G.level (s + 1))
    (s : ℕ) {e : H} (he : e ∈ G.level s) : E.inverse e ∈ G.level s := by
  induction s with
  | zero => exact G.mem_zero _
  | succ s ih =>
    apply hreg s _ (ih (G.antitone_level (Nat.le_succ s) he))
    simpa only [CoerciveInverse.apply_inverse E hc hgap] using he

/-- Preservation of all levels by the same inverse, conditional on elliptic
regularity (`app:ch_background:prop:bg-inverse`). Classical smoothness still
requires identifying the chosen scale with the actual Sobolev spaces. -/
theorem isSmooth_inverse (G : GradedScale H) (E : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪E v, v⟫_ℝ)
    (hreg : ∀ s v, v ∈ G.level s → E v ∈ G.level (s + 1) →
      v ∈ G.level (s + 1))
    {e : H} (he : G.IsSmooth e) : G.IsSmooth (E.inverse e) :=
  fun s => inverse_mem G E hc hgap hreg s (he s)

/-- The quantitative induction for `app:ch_background:eq:bg-r-inverse`.
`hstep` is the a priori estimate to be obtained from the derivative commutator
and coercivity; `hreg` supplies its domain justification. Neither is asserted
for the actual continuum operator here. The conclusion has one high coefficient
norm, the original shift `b`, and the same base-space inverse at every order. -/
theorem inverse_gradeNorm_le (G : GradedScale H) (E : H →L[ℝ] H)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪E v, v⟫_ℝ)
    {C a : ℕ → ℝ} {b : ℕ} (hC : ∀ s, 0 ≤ C s) (ha : ∀ s, 0 ≤ a s)
    (ha_mono : Monotone a)
    (hreg : ∀ s v, v ∈ G.level s → E v ∈ G.level (s + 1) →
      v ∈ G.level (s + 1))
    (hstep : ∀ s v, v ∈ G.level (s + 1) → E v ∈ G.level (s + 1) →
      G.gradeNorm (s + 1) v ≤ C (s + 1) *
        (G.gradeNorm (s + 1) (E v) + G.gradeNorm s v +
          (1 + a (s + 1 + b)) * ‖v‖))
    (s : ℕ) {e : H} (he : e ∈ G.level s) :
    G.gradeNorm s (E.inverse e) ≤
      bootstrapConstant c C s * (G.gradeNorm s e + (1 + a (s + b)) * ‖e‖) := by
  have hbase := CoerciveInverse.norm_inverse_apply_le E hc hgap e
  have hcinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  induction s with
  | zero =>
    simp only [GradedScale.gradeNorm_zero, bootstrapConstant]
    refine hbase.trans ?_
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg (by linarith [ha (0 + b)]) (norm_nonneg e)))
      hcinv
  | succ s ih =>
    have hCs := hC (s + 1)
    have hD := bootstrapConstant_nonneg hc hC s
    have hA : 0 ≤ 1 + a (s + 1 + b) := by linarith [ha (s + 1 + b)]
    have hnormmono := G.gradeNorm_mono (Nat.le_succ s) he
    have hcoeffmono := ha_mono (Nat.add_le_add_right (Nat.le_succ s) b)
    have hprev := ih (G.antitone_level (Nat.le_succ s) he)
    have hprev' : G.gradeNorm s (E.inverse e) ≤ bootstrapConstant c C s *
        (G.gradeNorm (s + 1) e + (1 + a (s + 1 + b)) * ‖e‖) := by
      refine hprev.trans ?_
      gcongr
    have hstep' := hstep s (E.inverse e) (inverse_mem G E hc hgap hreg (s + 1) he)
      (by simpa only [CoerciveInverse.apply_inverse E hc hgap] using he)
    rw [CoerciveInverse.apply_inverse E hc hgap] at hstep'
    calc
      G.gradeNorm (s + 1) (E.inverse e) ≤ C (s + 1) *
          (G.gradeNorm (s + 1) e + G.gradeNorm s (E.inverse e) +
            (1 + a (s + 1 + b)) * ‖E.inverse e‖) := hstep'
      _ ≤ C (s + 1) * (G.gradeNorm (s + 1) e + bootstrapConstant c C s *
          (G.gradeNorm (s + 1) e + (1 + a (s + 1 + b)) * ‖e‖) +
            (1 + a (s + 1 + b)) * (c⁻¹ * ‖e‖)) := by gcongr
      _ ≤ bootstrapConstant c C (s + 1) *
          (G.gradeNorm (s + 1) e + (1 + a (s + 1 + b)) * ‖e‖) := by
        dsimp [bootstrapConstant]
        have hF := G.gradeNorm_nonneg (s + 1) e
        have hN := norm_nonneg e
        have hpos : 0 ≤ C (s + 1) *
            ((1 + a (s + 1 + b)) * ‖e‖ + c⁻¹ * G.gradeNorm (s + 1) e) := by
          positivity
        nlinarith

end JanetCartan.ContinuumInverse
