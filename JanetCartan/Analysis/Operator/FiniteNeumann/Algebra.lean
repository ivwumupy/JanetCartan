module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Algebra.Ring.GeomSum

/-!
# The finite inverse identity

The algebraic identity `app:ch_regular:eq:finite-neumann-identity` uses no
convergence or smallness hypothesis. Multiplication of endomorphisms is composition.
-/

@[expose] public noncomputable section

namespace JanetCartan

open Finset

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Operator form of `app:ch_regular:eq:finite-neumann-identity`, also at depth
zero. A left inverse suffices; the remainder has `T` on the left of the power. -/
theorem finite_neumann_operator_identity (K T : E →L[ℝ] E)
    (hT : T * (1 + K) = 1) (d : ℕ) :
    T = ∑ j ∈ range d, (-K) ^ j + T * (-K) ^ d := by
  have hg := congrArg (fun S : E →L[ℝ] E ↦ T * S) (mul_neg_geom_sum (-K) d)
  simp only [sub_neg_eq_add, ← mul_assoc, hT, one_mul, mul_sub, mul_one] at hg
  exact sub_eq_iff_eq_add.mp hg.symm

/-- The signed power in `app:ch_regular:eq:finite-neumann-identity`. -/
theorem neg_operator_pow (K : E →L[ℝ] E) (d : ℕ) :
    (-K) ^ d = ((-1 : ℝ) ^ d) • K ^ d := by
  rw [← smul_pow, neg_one_smul]

/-- `app:ch_regular:eq:finite-neumann-identity` for an actual datum and every
natural depth, including zero. No commutation of arbitrary operators is used. -/
theorem finite_neumann_identity (K T : E →L[ℝ] E)
    (hT : T * (1 + K) = 1) (d : ℕ) (h : E) :
    T h = (∑ j ∈ range d, ((-K) ^ j) h) +
      ((-1 : ℝ) ^ d) • T ((K ^ d) h) := by
  have hid := congrArg (fun S : E →L[ℝ] E ↦ S h)
    (finite_neumann_operator_identity K T hT d)
  simpa only [add_apply, _root_.sum_apply,
    mul_apply_eq_comp, neg_operator_pow K d,
    smul_apply, map_smul] using hid

/-- Exact observed remainder underlying `app:ch_regular:eq:finite-observation`.
The observation need only be linear; its quantitative bounds are separate inputs. -/
theorem finite_neumann_observation_identity (K T : E →L[ℝ] E)
    (hT : T * (1 + K) = 1) (B : E →ₗ[ℝ] F) (d : ℕ) (h : E) :
    B (T h) - (∑ j ∈ range d, ((-1 : ℝ) ^ j) • B ((K ^ j) h)) =
      ((-1 : ℝ) ^ d) • B (T ((K ^ d) h)) := by
  have hid := congrArg B (finite_neumann_identity K T hT d h)
  simp only [map_add, map_sum, neg_operator_pow, smul_apply,
    map_smul] at hid
  exact sub_eq_iff_eq_add'.mpr hid

end JanetCartan
