module

public import JanetCartan.Analysis.Operator.NormalAugmentation.Localization
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2

import Mathlib.Tactic.Positivity

/-!
# From a local normal gap to an augmented global gap

Step 4 of `app:ch_background:prop:bg-frame`, with the quantitative conclusion
`app:ch_background:eq:bg-global-bound`. The physical row is a bounded operator
`A : P →L[ℝ] H`. The real self-adjoint cutoff `χ` maps into a subspace `S` on
which `app:ch_background:eq:bg-local-bound` is assumed. In the application,
`H` is the real torus L² space, `S` consists of fields supported in `B_r`, and
`χ` is multiplication by `ψ`. The augmented input has the Hilbert product norm.

This module proves the localization and exterior completion, not the analytic
local gap or the construction of the cutoff. The independent coercive-inverse
component can use the positive global gap proved here. No Fourier or matrix
normalization is changed by these abstract Hilbert-space arguments.
-/

@[expose] public noncomputable section

open scoped InnerProduct

namespace JanetCartan.NormalAugmentation

variable {H P : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- The bounded augmented row `(A_phys, 1-ψ)` from `app:ch_background:defn:bg-row`,
on the Hilbert direct sum of physical and exterior inputs. -/
def augmentedRow (A : P →L[ℝ] H) (χ : H →L[ℝ] H) : WithLp 2 (P × H) →L[ℝ] H :=
  A.comp (WithLp.fstL 2 ℝ P H) + (exterior χ).comp (WithLp.sndL 2 ℝ P H)

/-- Action of the augmented row in `app:ch_background:defn:bg-row`. -/
@[simp] theorem augmentedRow_apply (A : P →L[ℝ] H) (χ : H →L[ℝ] H)
    (u : WithLp 2 (P × H)) : augmentedRow A χ u = A u.fst + exterior χ u.snd := rfl

variable [CompleteSpace H] [CompleteSpace P]

/-- The literal Hilbert adjoint of the augmented row in
`app:ch_background:defn:bg-row`. -/
theorem adjoint_augmentedRow_apply (A : P →L[ℝ] H) (χ : H →L[ℝ] H) (f : H) :
    (augmentedRow A χ).adjoint f = WithLp.toLp 2 (A.adjoint f, (exterior χ).adjoint f) := by
  apply ext_inner_right ℝ
  intro u
  simp [ContinuousLinearMap.adjoint_inner_left, inner_add_right,
    WithLp.prod_inner_apply]

/-- A real self-adjoint cutoff has self-adjoint complement
(`app:ch_background:defn:bg-row`). -/
theorem exterior_adjoint (χ : H →L[ℝ] H) (hχ : IsSelfAdjoint χ) :
    (exterior χ).adjoint = exterior χ := by
  simp [exterior, map_sub, ContinuousLinearMap.adjoint_one, hχ.adjoint_eq]

/-- The augmented row's adjoint energy is exactly the sum of the physical and
exterior energies (`app:ch_background:prop:bg-frame`, Step 4). -/
theorem norm_adjoint_augmentedRow_sq (A : P →L[ℝ] H) (χ : H →L[ℝ] H)
    (hχ : IsSelfAdjoint χ) (f : H) :
    ‖(augmentedRow A χ).adjoint f‖ ^ 2 = ‖A.adjoint f‖ ^ 2 + ‖exterior χ f‖ ^ 2 := by
  rw [adjoint_augmentedRow_apply, WithLp.prod_norm_sq_eq_of_L2, exterior_adjoint χ hχ]
  rfl

/-- The actual normal `E_aug = A_aug A_aug*` of `app:ch_background:defn:bg-row`. -/
def augmentedNormal (A : P →L[ℝ] H) (χ : H →L[ℝ] H) : H →L[ℝ] H :=
  (augmentedRow A χ).comp (augmentedRow A χ).adjoint

/-- The normal is the sum of the two channel normals
(`app:ch_background:defn:bg-row`). -/
theorem augmentedNormal_apply (A : P →L[ℝ] H) (χ : H →L[ℝ] H) (f : H) :
    augmentedNormal A χ f = A (A.adjoint f) + exterior χ ((exterior χ).adjoint f) := by
  simp [augmentedNormal, adjoint_augmentedRow_apply]

/-- Self-adjointness of the actual augmented normal in
`app:ch_background:prop:bg-frame`. -/
theorem augmentedNormal_isSelfAdjoint (A : P →L[ℝ] H) (χ : H →L[ℝ] H) :
    IsSelfAdjoint (augmentedNormal A χ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [augmentedNormal]

/-- The quadratic form of `E_aug` in `app:ch_background:eq:bg-global-bound`. -/
theorem inner_augmentedNormal (A : P →L[ℝ] H) (χ : H →L[ℝ] H)
    (hχ : IsSelfAdjoint χ) (f : H) :
    inner ℝ (augmentedNormal A χ f) f = ‖A.adjoint f‖ ^ 2 + ‖exterior χ f‖ ^ 2 := by
  have h := (augmentedRow A χ).adjoint.apply_norm_sq_eq_inner_adjoint_left f
  simpa only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real,
    augmentedNormal, norm_adjoint_augmentedRow_sq A χ hχ f] using h.symm

/-- An explicit uniform gap constant for `app:ch_background:eq:bg-global-bound`.
Here `c` is the squared local gap and `M` bounds the physical row norm. -/
def globalGap (c M : ℝ) : ℝ :=
  ((Real.sqrt c)⁻¹ ^ 2 + (1 + (Real.sqrt c)⁻¹ * M) ^ 2)⁻¹

/-- Positivity of the exterior-completion constant in
`app:ch_background:eq:bg-global-bound`. -/
theorem globalGap_pos {c M : ℝ} (hc : 0 < c) : 0 < globalGap c M := by
  unfold globalGap
  have hs : 0 < (Real.sqrt c)⁻¹ := inv_pos.mpr (Real.sqrt_pos.2 hc)
  positivity

/-- A common upper bound for the row norms yields a common lower gap in
`app:ch_background:eq:bg-global-bound`. -/
theorem globalGap_antitone_norm_bound {c M N : ℝ} (hc : 0 < c)
    (hM : 0 ≤ M) (hMN : M ≤ N) : globalGap c N ≤ globalGap c M := by
  have hs : 0 < (Real.sqrt c)⁻¹ := inv_pos.mpr (Real.sqrt_pos.2 hc)
  unfold globalGap
  apply inv_anti₀ (by positivity)
  apply add_le_add le_rfl
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hMN hs.le)

/-- The intermediate unsquared inequality of `app:ch_background:prop:bg-frame`.
The support condition is `χ(H) ⊆ S`; the local gap is required only on `S`. -/
theorem norm_le_of_local_coercivity (A : P →L[ℝ] H) (χ : H →L[ℝ] H)
    (S : Submodule ℝ H) {c : ℝ} (hc : 0 < c)
    (hcutoff : ∀ f, χ f ∈ S)
    (hlocal : ∀ g ∈ S, c * ‖g‖ ^ 2 ≤ ‖A.adjoint g‖ ^ 2) (f : H) :
    ‖f‖ ≤ (Real.sqrt c)⁻¹ * ‖A.adjoint f‖ +
      (1 + (Real.sqrt c)⁻¹ * ‖A‖) * ‖exterior χ f‖ := by
  have h := norm_le_of_localized_estimate A.adjoint χ
    (inv_nonneg.mpr (Real.sqrt_nonneg c))
    (fun g ↦ norm_le_of_local_gap A.adjoint hc (hlocal _ (hcutoff g))) f
  simpa using h

/-- Exterior completion of the local normal bound: the adjoint of the actual
augmented row has a positive global squared gap
(`app:ch_background:eq:bg-local-bound` → `app:ch_background:eq:bg-global-bound`). -/
theorem augmentedRow_gap_of_local_coercivity (A : P →L[ℝ] H) (χ : H →L[ℝ] H)
    (hχ : IsSelfAdjoint χ) (S : Submodule ℝ H) {c : ℝ} (hc : 0 < c)
    (hcutoff : ∀ f, χ f ∈ S)
    (hlocal : ∀ g ∈ S, c * ‖g‖ ^ 2 ≤ ‖A.adjoint g‖ ^ 2) (f : H) :
    globalGap c ‖A‖ * ‖f‖ ^ 2 ≤ ‖(augmentedRow A χ).adjoint f‖ ^ 2 := by
  have h := norm_sq_le_of_localized_estimate A.adjoint χ
    (inv_nonneg.mpr (Real.sqrt_nonneg c))
    (fun g ↦ norm_le_of_local_gap A.adjoint hc (hlocal _ (hcutoff g))) f
  have hmul := mul_le_mul_of_nonneg_left h (globalGap_pos (M := ‖A‖) hc).le
  have hd : (Real.sqrt c)⁻¹ ^ 2 + (1 + (Real.sqrt c)⁻¹ * ‖A‖) ^ 2 ≠ 0 := by
    have hs : 0 < (Real.sqrt c)⁻¹ := inv_pos.mpr (Real.sqrt_pos.2 hc)
    positivity
  rw [norm_adjoint_augmentedRow_sq A χ hχ]
  simpa only [LinearIsometryEquiv.norm_map, globalGap, ← mul_assoc,
    inv_mul_cancel₀ hd, one_mul] using hmul

/-- `app:ch_background:eq:bg-global-bound` for the actual normal operator, conditional
only on boundedness, a self-adjoint supported cutoff, and the stated local gap. -/
theorem augmentedNormal_gap_of_local_coercivity (A : P →L[ℝ] H) (χ : H →L[ℝ] H)
    (hχ : IsSelfAdjoint χ) (S : Submodule ℝ H) {c : ℝ} (hc : 0 < c)
    (hcutoff : ∀ f, χ f ∈ S)
    (hlocal : ∀ g ∈ S, c * ‖g‖ ^ 2 ≤ ‖A.adjoint g‖ ^ 2) (f : H) :
    globalGap c ‖A‖ * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal A χ f) f := by
  rw [inner_augmentedNormal A χ hχ, ← norm_adjoint_augmentedRow_sq A χ hχ]
  exact augmentedRow_gap_of_local_coercivity A χ hχ S hc hcutoff hlocal f

/-- Uniform exterior completion in `app:ch_background:prop:bg-frame`: the constant
depends only on the local gap `c` and the common row bound `M`, not on the cutoff
norm or the individual row. This can be applied to every row in the fixed neighborhood. -/
theorem augmentedNormal_uniform_gap_of_local_coercivity
    (A : P →L[ℝ] H) (χ : H →L[ℝ] H) (hχ : IsSelfAdjoint χ)
    (S : Submodule ℝ H) {c M : ℝ} (hc : 0 < c) (hA : ‖A‖ ≤ M)
    (hcutoff : ∀ f, χ f ∈ S)
    (hlocal : ∀ g ∈ S, c * ‖g‖ ^ 2 ≤ ‖A.adjoint g‖ ^ 2) (f : H) :
    globalGap c M * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal A χ f) f := by
  exact (mul_le_mul_of_nonneg_right
    (globalGap_antitone_norm_bound hc (norm_nonneg A) hA) (sq_nonneg ‖f‖)).trans
      (augmentedNormal_gap_of_local_coercivity A χ hχ S hc hcutoff hlocal f)

/-- Controlled local errors with size `ε < c` still give the global gap in
`app:ch_background:prop:bg-frame`, combining error absorption with exterior completion. -/
theorem augmentedNormal_gap_of_remainder_bound
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : P →L[ℝ] H) (χ : H →L[ℝ] H) (hχ : IsSelfAdjoint χ)
    (R : H →L[ℝ] Z) (S : Submodule ℝ H) {c ε : ℝ} (hε : ε < c)
    (hcutoff : ∀ f, χ f ∈ S)
    (hcore : ∀ g ∈ S, c * ‖g‖ ^ 2 ≤ ‖A.adjoint g‖ ^ 2 + ‖R g‖ * ‖g‖)
    (herror : ∀ g ∈ S, ‖R g‖ ≤ ε * ‖g‖) (f : H) :
    globalGap (c - ε) ‖A‖ * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal A χ f) f := by
  exact augmentedNormal_gap_of_local_coercivity A χ hχ S (sub_pos.mpr hε) hcutoff
    (fun _ hg ↦ local_gap_of_remainder_bound A.adjoint R S hcore herror hg) f

end JanetCartan.NormalAugmentation
