module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Resolvent identities and uniform inverse stability

The bounded-operator part of `app:ch_background:prop:bg-inverse` and
`app:ch_background:prop:bg-normalized` in `paper.tex`. We use Mathlib's
`Ring.inverse` on the algebra of bounded endomorphisms; this agrees with
`ContinuousLinearMap.inverse` by `ContinuousLinearMap.ringInverse_eq_inverse`.

An invertible reference operator with inverse norm at most `M` stays invertible
when `M * ‖B - A‖ ≤ θ < 1`. Its inverse has norm at most `M / (1 - θ)`, and
its difference from the reference inverse has norm at most
`M ^ 2 / (1 - θ) * ‖B - A‖`. The half-size neighborhood gives constants `2 * M`
and `2 * M ^ 2`, and two operators in it satisfy a `4 * M ^ 2` Lipschitz bound.
Inversion preserves every `ContDiff` order, including smoothness, on invertible
families; its derivative is `H ↦ -A⁻¹ H A⁻¹`.

The sigma-family specialization assumes invertibility at zero and the operator
norm estimate `‖A σ - A 0‖ ≤ L * σ`, with `M * L * σ₀ ≤ 1 / 2`. These are
explicit analytic inputs. This module does not prove geometric convergence of
the normalized normal operators, coercivity, Sobolev regularity, or the raw and
density adjoint estimates. In particular, it does not assume or infer norm
continuity of the individual graph operators, which the source avoids.
-/

@[expose] public noncomputable section

namespace JanetCartan.OperatorInverse

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The left-factored resolvent identity for the inverse in
`app:ch_background:prop:bg-inverse`; multiplication is operator composition. -/
theorem inverse_resolvent (A B : E →L[𝕜] E) (hA : IsUnit A) (hB : IsUnit B) :
    Ring.inverse B - Ring.inverse A =
      Ring.inverse A * (A - B) * Ring.inverse B := by
  rw [mul_sub, sub_mul, Ring.inverse_mul_cancel A hA, one_mul,
    mul_assoc, Ring.mul_inverse_cancel B hB, mul_one]

/-- The right-factored resolvent identity for
`app:ch_background:prop:bg-inverse`, with the same operator order as in the
noncommutative inverse algebra. -/
theorem inverse_resolvent_right (A B : E →L[𝕜] E) (hA : IsUnit A) (hB : IsUnit B) :
    Ring.inverse B - Ring.inverse A =
      Ring.inverse B * (A - B) * Ring.inverse A := by
  rw [mul_sub, sub_mul, mul_assoc, Ring.mul_inverse_cancel A hA, mul_one,
    Ring.inverse_mul_cancel B hB, one_mul]

/-- The right inverse identity on the entire base space, as used in
`app:ch_background:prop:bg-inverse`. -/
theorem apply_inverse (A : E →L[𝕜] E) (hA : IsUnit A) (f : E) :
    A (Ring.inverse A f) = f :=
  congrArg (fun T : E →L[𝕜] E ↦ T f) (Ring.mul_inverse_cancel A hA)

/-- The left inverse identity on the entire base space, as used in
`app:ch_background:prop:bg-inverse`. -/
theorem inverse_apply (A : E →L[𝕜] E) (hA : IsUnit A) (f : E) :
    Ring.inverse A (A f) = f :=
  congrArg (fun T : E →L[𝕜] E ↦ T f) (Ring.inverse_mul_cancel A hA)

/-- The operator norm form of the resolvent identity, for stability in
`app:ch_background:prop:bg-normalized`. -/
theorem norm_inverse_sub_le (A B : E →L[𝕜] E) (hA : IsUnit A) (hB : IsUnit B) :
    ‖Ring.inverse B - Ring.inverse A‖ ≤
      ‖Ring.inverse A‖ * ‖B - A‖ * ‖Ring.inverse B‖ := by
  rw [inverse_resolvent A B hA hB]
  calc
    _ ≤ (‖Ring.inverse A‖ * ‖A - B‖) * ‖Ring.inverse B‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))
    _ = _ := by rw [norm_sub_rev A B]

variable [CompleteSpace E]

/-- A norm-small perturbation of an invertible bounded operator is invertible.
This is a conditional operator tool for `app:ch_background:prop:bg-normalized`;
the smallness of the normal-operator perturbation remains an input. -/
theorem isUnit_of_norm_perturbation_lt (A B : E →L[𝕜] E) (hA : IsUnit A)
    (hsmall : ‖Ring.inverse A‖ * ‖B - A‖ < 1) : IsUnit B := by
  have hnorm : ‖-(Ring.inverse A * (B - A))‖ < 1 := by
    rw [norm_neg]
    exact (norm_mul_le _ _).trans_lt hsmall
  have hunit := hA.mul (isUnit_one_sub_of_norm_lt_one hnorm)
  convert hunit using 1
  rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc,
    Ring.mul_inverse_cancel A hA, one_mul, add_sub_cancel]

/-- Explicit uniform inverse constant `M / (1 - θ)` for the base-space estimate
in `app:ch_background:eq:bg-uniform-normalized`, conditional on the stated
operator-norm perturbation bound. -/
theorem norm_inverse_le_of_perturbation (A B : E →L[𝕜] E) (hA : IsUnit A)
    {M θ : ℝ} (hM : ‖Ring.inverse A‖ ≤ M)
    (hsmall : M * ‖B - A‖ ≤ θ) (hθ : θ < 1) :
    ‖Ring.inverse B‖ ≤ M / (1 - θ) := by
  have hB := isUnit_of_norm_perturbation_lt A B hA
    ((mul_le_mul_of_nonneg_right hM (norm_nonneg _)).trans_lt (hsmall.trans_lt hθ))
  have hdiff : ‖Ring.inverse B - Ring.inverse A‖ ≤ θ * ‖Ring.inverse B‖ := by
    refine (norm_inverse_sub_le A B hA hB).trans ?_
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hM (norm_nonneg _)).trans hsmall) (norm_nonneg _)
  have hbound : ‖Ring.inverse B‖ ≤ M + θ * ‖Ring.inverse B‖ := by
    calc
      _ ≤ ‖Ring.inverse B - Ring.inverse A‖ + ‖Ring.inverse A‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (Ring.inverse B - Ring.inverse A) (Ring.inverse A)
      _ ≤ _ := by linarith
  apply (le_div_iff₀ (sub_pos.mpr hθ)).mpr
  nlinarith

/-- Quantitative continuity of the inverse, with constant `M² / (1 - θ)`,
for `app:ch_background:prop:bg-normalized`. -/
theorem norm_inverse_sub_le_of_perturbation (A B : E →L[𝕜] E) (hA : IsUnit A)
    {M θ : ℝ} (hM : ‖Ring.inverse A‖ ≤ M)
    (hsmall : M * ‖B - A‖ ≤ θ) (hθ : θ < 1) :
    ‖Ring.inverse B - Ring.inverse A‖ ≤ M ^ 2 / (1 - θ) * ‖B - A‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hB := isUnit_of_norm_perturbation_lt A B hA
    ((mul_le_mul_of_nonneg_right hM (norm_nonneg _)).trans_lt (hsmall.trans_lt hθ))
  calc
    _ ≤ ‖Ring.inverse A‖ * ‖B - A‖ * ‖Ring.inverse B‖ :=
      norm_inverse_sub_le A B hA hB
    _ ≤ (M * ‖B - A‖) * (M / (1 - θ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
        (norm_inverse_le_of_perturbation A B hA hM hsmall hθ)
        (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _))
    _ = _ := by ring

/-- Invertibility and the constants `2M`, `2M²` on a half-size perturbation
neighborhood, sufficient for the base-space inverse part of
`app:ch_background:eq:bg-uniform-normalized` once the input bounds are proved. -/
theorem inverse_stability_half (A B : E →L[𝕜] E) (hA : IsUnit A)
    {M : ℝ} (hM : ‖Ring.inverse A‖ ≤ M) (hsmall : M * ‖B - A‖ ≤ 1 / 2) :
    IsUnit B ∧ ‖Ring.inverse B‖ ≤ 2 * M ∧
      ‖Ring.inverse B - Ring.inverse A‖ ≤ 2 * M ^ 2 * ‖B - A‖ := by
  refine ⟨isUnit_of_norm_perturbation_lt A B hA
    ((mul_le_mul_of_nonneg_right hM (norm_nonneg _)).trans_lt
      (hsmall.trans_lt (by norm_num))), ?_, ?_⟩
  · convert norm_inverse_le_of_perturbation A B hA hM hsmall (by norm_num) using 1
    ring
  · convert norm_inverse_sub_le_of_perturbation A B hA hM hsmall (by norm_num) using 1
    ring

/-- The inverse is Lipschitz with constant `4M²` between any two operators in
the half-size neighborhood of a common reference. This is the uniform
operator stability tool for `app:ch_background:prop:bg-normalized`. -/
theorem norm_inverse_sub_le_of_nearby (A₀ A B : E →L[𝕜] E) (hA₀ : IsUnit A₀)
    {M : ℝ} (hM : ‖Ring.inverse A₀‖ ≤ M)
    (hA : M * ‖A - A₀‖ ≤ 1 / 2) (hB : M * ‖B - A₀‖ ≤ 1 / 2) :
    ‖Ring.inverse B - Ring.inverse A‖ ≤ 4 * M ^ 2 * ‖B - A‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  obtain ⟨huA, hnA, _⟩ := inverse_stability_half A₀ A hA₀ hM hA
  obtain ⟨huB, hnB, _⟩ := inverse_stability_half A₀ B hA₀ hM hB
  calc
    _ ≤ ‖Ring.inverse A‖ * ‖B - A‖ * ‖Ring.inverse B‖ :=
      norm_inverse_sub_le A B huA huB
    _ ≤ (2 * M * ‖B - A‖) * (2 * M) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hnA (norm_nonneg _)) hnB
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The vector estimate supplied by the uniform inverse constant, corresponding
to the base-space inverse term of `app:ch_background:eq:bg-uniform-normalized`. -/
theorem norm_inverse_apply_le_of_perturbation (A B : E →L[𝕜] E) (hA : IsUnit A)
    {M θ : ℝ} (hM : ‖Ring.inverse A‖ ≤ M)
    (hsmall : M * ‖B - A‖ ≤ θ) (hθ : θ < 1) (f : E) :
    ‖Ring.inverse B f‖ ≤ M / (1 - θ) * ‖f‖ :=
  (Ring.inverse B).le_opNorm f |>.trans
    (mul_le_mul_of_nonneg_right
      (norm_inverse_le_of_perturbation A B hA hM hsmall hθ) (norm_nonneg f))

/-- Uniform inverse bounds and an `O(σ)` inverse difference on `0 ≤ σ ≤ σ₀`,
for `app:ch_background:prop:bg-normalized`. The input `happrox` is precisely a
normal-operator convergence estimate; no geometric proof of it is claimed here. -/
theorem normalized_family_inverse_bounds (A : ℝ → E →L[𝕜] E)
    (hA₀ : IsUnit (A 0)) {M L σ₀ : ℝ}
    (hM : ‖Ring.inverse (A 0)‖ ≤ M) (hL : 0 ≤ L)
    (hsmall : M * L * σ₀ ≤ 1 / 2)
    (happrox : ∀ σ ∈ Set.Icc 0 σ₀, ‖A σ - A 0‖ ≤ L * σ) :
    ∀ σ ∈ Set.Icc 0 σ₀,
      IsUnit (A σ) ∧ ‖Ring.inverse (A σ)‖ ≤ 2 * M ∧
        ‖Ring.inverse (A σ) - Ring.inverse (A 0)‖ ≤ 2 * M ^ 2 * L * σ := by
  intro σ hσ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hnear : M * ‖A σ - A 0‖ ≤ 1 / 2 := calc
    _ ≤ M * (L * σ) := mul_le_mul_of_nonneg_left (happrox σ hσ) hM0
    _ ≤ M * L * σ₀ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hσ.2 (mul_nonneg hM0 hL)
    _ ≤ _ := hsmall
  obtain ⟨hu, hb, hd⟩ := inverse_stability_half (A 0) (A σ) hA₀ hM hnear
  refine ⟨hu, hb, hd.trans ?_⟩
  calc
    _ ≤ 2 * M ^ 2 * (L * σ) :=
      mul_le_mul_of_nonneg_left (happrox σ hσ) (by positivity)
    _ = _ := by ring

section Smooth

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {n : WithTop ℕ∞} {A : P → E →L[𝕜] E} {s : Set P} {p : P}

/-- Inversion preserves the regularity of a family at an invertible value,
including at a boundary point. Operator smoothness is an explicit input for
`app:ch_background:prop:bg-normalized`. -/
theorem contDiffWithinAt_inverse (hA : ContDiffWithinAt 𝕜 n A s p)
    (hu : IsUnit (A p)) :
    ContDiffWithinAt 𝕜 n (fun q ↦ Ring.inverse (A q)) s p := by
  have hi := contDiffAt_ringInverse (n := n) 𝕜 hu.unit
  rw [hu.unit_spec] at hi
  exact hi.comp_contDiffWithinAt p hA

/-- Smooth dependence of the inverse on a set of invertible operators, for
`app:ch_background:prop:bg-normalized`. This holds at every `ContDiff` order. -/
theorem contDiffOn_inverse (hA : ContDiffOn 𝕜 n A s)
    (hu : ∀ p ∈ s, IsUnit (A p)) :
    ContDiffOn 𝕜 n (fun q ↦ Ring.inverse (A q)) s :=
  fun p hp ↦ contDiffWithinAt_inverse (hA p hp) (hu p hp)

/-- Smooth inverse dependence from a small-perturbation hypothesis alone;
invertibility throughout the set is proved, not assumed. This is a conditional
operator result for `app:ch_background:prop:bg-normalized`. -/
theorem contDiffOn_inverse_of_perturbation (hA : ContDiffOn 𝕜 n A s)
    (A₀ : E →L[𝕜] E) (hu₀ : IsUnit A₀)
    (hnear : ∀ p ∈ s, ‖Ring.inverse A₀‖ * ‖A p - A₀‖ < 1) :
    ContDiffOn 𝕜 n (fun q ↦ Ring.inverse (A q)) s :=
  contDiffOn_inverse hA fun p hp ↦
    isUnit_of_norm_perturbation_lt A₀ (A p) hu₀ (hnear p hp)

/-- Smooth extension of the inverse through an invertible limiting value,
for the operator step in `app:ch_background:prop:bg-normalized`. -/
theorem contDiffAt_inverse (hA : ContDiffAt 𝕜 n A p) (hu : IsUnit (A p)) :
    ContDiffAt 𝕜 n (fun q ↦ Ring.inverse (A q)) p := by
  have hi := contDiffAt_ringInverse (n := n) 𝕜 hu.unit
  rw [hu.unit_spec] at hi
  exact hi.comp p hA

/-- Global smooth dependence of the inverse along an invertible smooth family,
for `app:ch_background:prop:bg-normalized`. -/
theorem contDiff_inverse (hA : ContDiff 𝕜 n A) (hu : ∀ p, IsUnit (A p)) :
    ContDiff 𝕜 n (fun q ↦ Ring.inverse (A q)) :=
  contDiff_iff_contDiffAt.mpr fun p ↦ contDiffAt_inverse (hA.contDiffAt) (hu p)

/-- The derivative of a family of inverses is `H ↦ -A⁻¹ H A⁻¹`, the first
variation underlying inverse stability in `app:ch_background:prop:bg-normalized`. -/
theorem hasFDerivAt_inverse {A' : P →L[𝕜] (E →L[𝕜] E)}
    (hA : HasFDerivAt A A' p) (hu : IsUnit (A p)) :
    HasFDerivAt (fun q ↦ Ring.inverse (A q))
      ((-ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E)
        (Ring.inverse (A p)) (Ring.inverse (A p))).comp A') p := by
  have hi := hasFDerivAt_ringInverse (𝕜 := 𝕜) hu.unit
  rw [hu.unit_spec, ← Ring.inverse_of_isUnit hu] at hi
  exact hi.comp p hA

/-- The directional form of the inverse derivative, for
`app:ch_background:prop:bg-normalized`. -/
theorem fderiv_inverse_apply {A' : P →L[𝕜] (E →L[𝕜] E)}
    (hA : HasFDerivAt A A' p) (hu : IsUnit (A p)) (v : P) :
    fderiv 𝕜 (fun q ↦ Ring.inverse (A q)) p v =
      -(Ring.inverse (A p) * A' v * Ring.inverse (A p)) := by
  rw [(hasFDerivAt_inverse hA hu).fderiv]
  rfl

/-- The inverse derivative has norm at most `M² * ‖A'‖` when the inverse norm
is at most `M`. In the half-size neighborhood this gives `4M² * ‖A'‖`,
for `app:ch_background:prop:bg-normalized`. -/
theorem norm_fderiv_inverse_le {A' : P →L[𝕜] (E →L[𝕜] E)}
    (hA : HasFDerivAt A A' p) (hu : IsUnit (A p))
    {M : ℝ} (hM : ‖Ring.inverse (A p)‖ ≤ M) :
    ‖fderiv 𝕜 (fun q ↦ Ring.inverse (A q)) p‖ ≤ M ^ 2 * ‖A'‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  rw [(hasFDerivAt_inverse hA hu).fderiv]
  calc
    _ ≤ ‖-ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E)
        (Ring.inverse (A p)) (Ring.inverse (A p))‖ * ‖A'‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖Ring.inverse (A p)‖ * ‖Ring.inverse (A p)‖) * ‖A'‖ := by
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le _ _ _ _) (norm_nonneg _)
    _ ≤ (M * M) * ‖A'‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul hM hM (norm_nonneg _) hM0) (norm_nonneg _)
    _ = _ := by ring

end Smooth
end JanetCartan.OperatorInverse
