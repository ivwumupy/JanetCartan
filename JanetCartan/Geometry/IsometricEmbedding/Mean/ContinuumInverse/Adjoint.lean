module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.Bootstrap

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Composition with the raw adjoint and the density map

Conditional assembly of `app:ch_background:eq:bg-r-inverse` and
`app:ch_background:eq:bg-density-adjoint`. The analytic raw-adjoint estimate and
the fixed density multiplier bound are explicit inputs, not conclusions of this
file. The estimates use the base-space inverse constructed by `CoerciveInverse`.
The high coefficient occurs only once; spending one input derivative increases
the fixed coefficient shift by one.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumInverse

variable {H X : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- Transfer a supplied raw-adjoint bound through the one common inverse,
as in `app:ch_background:prop:bg-adjoint`. The inverse estimate at this order is
an explicit input, supplied by `inverse_gradeNorm_le` after elliptic regularity
has been proved. Using only the inverse's base norm in the coefficient term
avoids multiplying two high coefficient norms. -/
theorem rightInverse_gradeNorm_le (G : GradedScale H) (R : GradedScale X)
    (A : X →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2)
    {s : ℕ} {e : H} {d k m : ℝ} (hk : 0 ≤ k) (hm : 0 ≤ m)
    (hmem : (CoerciveInverse.normalOperator A).inverse e ∈ G.level s)
    (hinv : G.gradeNorm s ((CoerciveInverse.normalOperator A).inverse e) ≤
      d * (G.gradeNorm s e + m * ‖e‖))
    (hraw : ∀ v, v ∈ G.level s →
      R.gradeNorm s (A.adjoint v) ≤ k * (G.gradeNorm s v + m * ‖v‖)) :
    R.gradeNorm s (CoerciveInverse.rightInverse A e) ≤
      k * (d + c⁻¹) * (G.gradeNorm s e + m * ‖e‖) := by
  have hbase := CoerciveInverse.norm_inverse_apply_le (CoerciveInverse.normalOperator A)
    hc (CoerciveInverse.normalOperator_gap A hgap) e
  have hcinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  change R.gradeNorm s (A.adjoint ((CoerciveInverse.normalOperator A).inverse e)) ≤ _
  calc
    _ ≤ k * (G.gradeNorm s ((CoerciveInverse.normalOperator A).inverse e) +
        m * ‖(CoerciveInverse.normalOperator A).inverse e‖) := hraw _ hmem
    _ ≤ k * (d * (G.gradeNorm s e + m * ‖e‖) + m * (c⁻¹ * ‖e‖)) := by gcongr
    _ ≤ k * (d + c⁻¹) * (G.gradeNorm s e + m * ‖e‖) := by
      have hpos : 0 ≤ k * c⁻¹ * G.gradeNorm s e := by
        exact mul_nonneg (mul_nonneg hk hcinv) (G.gradeNorm_nonneg s e)
      nlinarith

/-- The two terms in `app:ch_background:eq:bg-r-inverse`, assembled from the
inverse estimate and the raw adjoint estimate at a fixed order. Both estimates
refer to the same inverse and the same single high coefficient size `m`. -/
theorem inverse_add_rightInverse_gradeNorm_le (G : GradedScale H) (R : GradedScale X)
    (A : X →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ‖A.adjoint v‖ ^ 2)
    {s : ℕ} {e : H} {d k m : ℝ} (hk : 0 ≤ k) (hm : 0 ≤ m)
    (hmem : (CoerciveInverse.normalOperator A).inverse e ∈ G.level s)
    (hinv : G.gradeNorm s ((CoerciveInverse.normalOperator A).inverse e) ≤
      d * (G.gradeNorm s e + m * ‖e‖))
    (hraw : ∀ v, v ∈ G.level s →
      R.gradeNorm s (A.adjoint v) ≤ k * (G.gradeNorm s v + m * ‖v‖)) :
    G.gradeNorm s ((CoerciveInverse.normalOperator A).inverse e) +
      R.gradeNorm s (CoerciveInverse.rightInverse A e) ≤
        (d + k * (d + c⁻¹)) * (G.gradeNorm s e + m * ‖e‖) := by
  have h := rightInverse_gradeNorm_le G R A hc hgap hk hm hmem hinv hraw
  nlinarith

/-- Domain justification for the raw estimate in
`app:ch_background:prop:bg-adjoint`. Both regularity inputs remain explicit. -/
theorem rightInverse_mem (G : GradedScale H) (R : GradedScale X)
    (A : X →L[ℝ] H) {s : ℕ} {e : H}
    (hinv : (CoerciveInverse.normalOperator A).inverse e ∈ G.level s)
    (hraw : ∀ v, v ∈ G.level s → A.adjoint v ∈ R.level s) :
    CoerciveInverse.rightInverse A e ∈ R.level s := hraw _ hinv

/-- The one-derivative density trade in `app:ch_background:eq:bg-density-adjoint`,
conditional on the actual multiplier estimate `htrade`. The size `densitySize`
may be the sum of the carrier density Sobolev norms, either before or after the
physical cutoff. The shift changes from `b` to `b + 1` exactly once. -/
theorem density_rightInverse_le (G : GradedScale H) (R : GradedScale X)
    (A : X →L[ℝ] H) (densitySize : ℕ → X → ℝ)
    {s b : ℕ} {e : H} {C a : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hmem : CoerciveInverse.rightInverse A e ∈ R.level (s + 1))
    (hraw : R.gradeNorm (s + 1) (CoerciveInverse.rightInverse A e) ≤
      C (s + 1) * (G.gradeNorm (s + 1) e + (1 + a (s + 1 + b)) * ‖e‖))
    (htrade : ∀ u, u ∈ R.level (s + 1) →
      densitySize s u ≤ L * R.gradeNorm (s + 1) u) :
    densitySize s (CoerciveInverse.rightInverse A e) ≤
      (L * C (s + 1)) *
        (G.gradeNorm (s + 1) e + (1 + a (s + (b + 1))) * ‖e‖) := by
  calc
    _ ≤ L * R.gradeNorm (s + 1) (CoerciveInverse.rightInverse A e) := htrade _ hmem
    _ ≤ L * (C (s + 1) *
        (G.gradeNorm (s + 1) e + (1 + a (s + 1 + b)) * ‖e‖)) :=
      mul_le_mul_of_nonneg_left hraw hL
    _ = _ := by rw [Nat.add_right_comm s 1 b, Nat.add_assoc, mul_assoc]

end JanetCartan.ContinuumInverse
