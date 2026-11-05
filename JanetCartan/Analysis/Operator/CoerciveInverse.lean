module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The bounded inverse of a coercive Hilbert operator

This is the Hilbert-space inversion step of `app:ch_background:prop:bg-frame`
and the right-inverse identity in `app:ch_background:prop:bg-inverse` of `paper.tex`.
All spaces are complete real Hilbert spaces, with no dimension restriction.

The positive quadratic-form gap is an input. Lax–Milgram supplies invertibility;
Cauchy–Schwarz gives the quantitative bound. We use Mathlib's `E.inverse`, so
the inverse depends only on the operator, not on a choice of gap constant.
For a row `A`, the resulting right inverse is `A.adjoint ∘L (A ∘L A.adjoint).inverse`.
The microlocal gap, Sobolev regularity, and support properties are separate inputs.
-/

@[expose] public noncomputable section

namespace JanetCartan.CoerciveInverse

open ContinuousLinearMap
open scoped InnerProductSpace

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Lax–Milgram gives a bounded two-sided inverse from the global gap in
`app:ch_background:prop:bg-frame`. Symmetry is not needed for this step. -/
theorem isInvertible_of_gap (E : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪E x, x⟫_ℝ) : E.IsInvertible := by
  let B : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp E
  have hB : IsCoercive B := by
    refine ⟨c, hc, fun x => ?_⟩
    simpa [B, pow_two, mul_assoc] using hgap x
  refine ⟨hB.continuousLinearEquivOfBilin, ?_⟩
  ext x
  apply ext_inner_right ℝ
  intro y
  exact hB.continuousLinearEquivOfBilin_apply x y

omit [CompleteSpace H] in
/-- Cauchy–Schwarz converts the quadratic gap of
`app:ch_background:prop:bg-frame` into a lower operator bound. -/
theorem mul_norm_le_norm_apply (E : H →L[ℝ] H) {c : ℝ}
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪E x, x⟫_ℝ) (x : H) :
    c * ‖x‖ ≤ ‖E x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    apply (mul_le_mul_iff_left₀ hnorm).mp
    calc
      c * ‖x‖ * ‖x‖ = c * ‖x‖ ^ 2 := by rw [pow_two, mul_assoc]
      _ ≤ ⟪E x, x⟫_ℝ := hgap x
      _ ≤ ‖E x‖ * ‖x‖ := real_inner_le_norm _ _

/-- The right inverse identity on the entire Hilbert space, as in
`app:ch_background:prop:bg-frame`. -/
theorem apply_inverse (E : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪E x, x⟫_ℝ) (x : H) :
    E (E.inverse x) = x :=
  (isInvertible_of_gap E hc hgap).self_apply_inverse x

/-- The left inverse identity on the entire Hilbert space, as in
`app:ch_background:prop:bg-frame`. -/
theorem inverse_apply (E : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪E x, x⟫_ℝ) (x : H) :
    E.inverse (E x) = x :=
  (isInvertible_of_gap E hc hgap).inverse_apply_self x

/-- The base-space estimate for the single inverse in
`app:ch_background:prop:bg-inverse`. -/
theorem norm_inverse_apply_le (E : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪E x, x⟫_ℝ) (x : H) :
    ‖E.inverse x‖ ≤ c⁻¹ * ‖x‖ := by
  have h := mul_norm_le_norm_apply E hgap (E.inverse x)
  rw [apply_inverse E hc hgap] at h
  exact (le_inv_mul_iff₀ hc).mpr h

/-- The inverse has operator norm at most `1 / c`, quantifying the bounded
inverse assertion of `app:ch_background:prop:bg-frame`. -/
theorem norm_inverse_le (E : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪E x, x⟫_ℝ) : ‖E.inverse‖ ≤ c⁻¹ :=
  E.inverse.opNorm_le_bound (inv_nonneg.mpr hc.le) (norm_inverse_apply_le E hc hgap)

/-- The inverse of the self-adjoint operator in
`app:ch_background:prop:bg-frame` is itself self-adjoint. -/
theorem inverse_isSelfAdjoint (E : H →L[ℝ] H) (hE : IsSelfAdjoint E)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪E x, x⟫_ℝ) :
    IsSelfAdjoint E.inverse := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have h := hE.isSymmetric (E.inverse x) (E.inverse y)
  simpa only [ContinuousLinearMap.coe_coe, apply_inverse E hc hgap] using h.symm

/-- Any bounded right inverse is this same inverse. This makes the uniqueness
assertion in `app:ch_background:prop:bg-inverse` independent of estimates. -/
theorem eq_inverse_of_rightInverse (E R : H →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪E x, x⟫_ℝ)
    (hR : E ∘L R = ContinuousLinearMap.id ℝ H) : R = E.inverse := by
  ext x
  apply (isInvertible_of_gap E hc hgap).injective
  have hx := congrArg (fun T : H →L[ℝ] H => T x) hR
  simpa only [comp_apply, id_apply, apply_inverse E hc hgap] using hx

/-- Abstract Hilbert-space conclusion of `app:ch_background:prop:bg-frame`:
a coercive bounded self-adjoint operator has a bounded self-adjoint inverse
with the stated quantitative bound. The continuum gap remains a hypothesis. -/
theorem exists_selfAdjoint_inverse (E : H →L[ℝ] H) (hE : IsSelfAdjoint E)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪E x, x⟫_ℝ) :
    ∃ Q : H →L[ℝ] H, IsSelfAdjoint Q ∧
      E ∘L Q = ContinuousLinearMap.id ℝ H ∧
      Q ∘L E = ContinuousLinearMap.id ℝ H ∧ ‖Q‖ ≤ c⁻¹ :=
  ⟨E.inverse, inverse_isSelfAdjoint E hE hc hgap,
    (isInvertible_of_gap E hc hgap).self_comp_inverse,
    (isInvertible_of_gap E hc hgap).inverse_comp_self, norm_inverse_le E hc hgap⟩

/-- The row normal operator `AA*` of `app:ch_background:prop:bg-inverse`. -/
def normalOperator (A : H →L[ℝ] K) : K →L[ℝ] K := A ∘L A.adjoint

/-- Self-adjointness of the row normal operator in
`app:ch_background:prop:bg-frame`. -/
theorem normalOperator_isSelfAdjoint (A : H →L[ℝ] K) :
    IsSelfAdjoint (normalOperator A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [normalOperator, adjoint_comp, adjoint_adjoint]

/-- The normal quadratic form is the squared adjoint norm, relating the two
gap formulations in `app:ch_background:prop:bg-frame`. -/
theorem inner_normalOperator (A : H →L[ℝ] K) (x : K) :
    ⟪normalOperator A x, x⟫_ℝ = ‖A.adjoint x‖ ^ 2 := by
  change ⟪A (A.adjoint x), x⟫_ℝ = _
  rw [← adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- The row lower bound gives the exact coercivity hypothesis used to invert
`AA*` in `app:ch_background:prop:bg-frame`. -/
theorem normalOperator_gap (A : H →L[ℝ] K) {c : ℝ}
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ‖A.adjoint x‖ ^ 2) :
    ∀ x, c * ‖x‖ ^ 2 ≤ ⟪normalOperator A x, x⟫_ℝ := by
  simpa only [inner_normalOperator] using hgap

/-- The canonical `A*(AA*)⁻¹` in `app:ch_background:prop:bg-inverse`.
It is a right inverse whenever the adjoint row has a positive gap. -/
def rightInverse (A : H →L[ℝ] K) : K →L[ℝ] H :=
  A.adjoint ∘L (normalOperator A).inverse

/-- The identity `AA*(AA*)⁻¹ = I` from
`app:ch_background:prop:bg-inverse`, pointwise on the full output space. -/
theorem apply_rightInverse (A : H →L[ℝ] K) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ‖A.adjoint x‖ ^ 2) (x : K) :
    A (rightInverse A x) = x :=
  apply_inverse (normalOperator A) hc (normalOperator_gap A hgap) x

/-- The bounded-operator right inverse identity from
`app:ch_background:prop:bg-inverse`. -/
theorem comp_rightInverse (A : H →L[ℝ] K) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ‖A.adjoint x‖ ^ 2) :
    A ∘L rightInverse A = ContinuousLinearMap.id ℝ K := by
  ext x
  exact apply_rightInverse A hc hgap x

/-- A base-space operator norm bound for the right inverse of
`app:ch_background:prop:bg-inverse`. -/
theorem norm_rightInverse_le (A : H →L[ℝ] K) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ ‖A.adjoint x‖ ^ 2) :
    ‖rightInverse A‖ ≤ ‖A‖ * c⁻¹ := by
  calc
    ‖rightInverse A‖ ≤ ‖A.adjoint‖ * ‖(normalOperator A).inverse‖ :=
      opNorm_comp_le _ _
    _ ≤ ‖A.adjoint‖ * c⁻¹ := mul_le_mul_of_nonneg_left
      (norm_inverse_le (normalOperator A) hc (normalOperator_gap A hgap)) (norm_nonneg _)
    _ = ‖A‖ * c⁻¹ := by rw [adjoint.norm_map]

end JanetCartan.CoerciveInverse
