module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Complete
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Density
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The negative-order periodic Sobolev dual

For `app:ch_background:prop:bg-inverse`, define H⁻¹ as the continuous real dual
of the actual Fourier H¹ space. The L² inner product gives a bounded, injective
inclusion. Transposition of bounded H¹ operators gives bounded operators on
H⁻¹; self-adjointness makes these agree with compatible L² operators.

The inverse and uniqueness results below are functional analytic: bounded H¹
restrictions are explicit hypotheses. No elliptic preservation theorem is
assumed or asserted here. All dimensions, including zero, and all finite
dimensional real Hilbert codomains are allowed.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- The actual H⁻¹ space, with its dual operator norm
(`app:ch_background:prop:bg-inverse`). -/
abbrev PeriodicSobolevNegativeOne (n : ℕ) (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :=
  StrongDual ℝ (PeriodicSobolevSpace n F 1)

namespace PeriodicSobolevNegativeOne

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The continuous evaluation pairing H⁻¹ × H¹ → ℝ
(`app:ch_background:prop:bg-inverse`). -/
def pairing : PeriodicSobolevNegativeOne n F →L[ℝ]
    PeriodicSobolevSpace n F 1 →L[ℝ] ℝ :=
  ContinuousLinearMap.id ℝ _

/-- The dual pairing is evaluation (`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem pairing_apply (u : PeriodicSobolevNegativeOne n F)
    (v : PeriodicSobolevSpace n F 1) : pairing u v = u v := rfl

/-- The duality estimate (`app:ch_background:prop:bg-inverse`). -/
theorem norm_pairing_le (u : PeriodicSobolevNegativeOne n F)
    (v : PeriodicSobolevSpace n F 1) : ‖pairing u v‖ ≤ ‖u‖ * ‖v‖ :=
  u.le_opNorm v

/-- The L² inner-product inclusion into H⁻¹
(`app:ch_background:prop:bg-inverse`). -/
def ofL2 : PeriodicL2 n F →L[ℝ] PeriodicSobolevNegativeOne n F :=
  ((ContinuousLinearMap.compL ℝ (PeriodicSobolevSpace n F 1) (PeriodicL2 n F) ℝ).flip
    (PeriodicSobolevSpace.toL2 1)).comp (innerSL ℝ)

/-- The inclusion pairs by the original L² inner product
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem ofL2_apply (u : PeriodicL2 n F) (v : PeriodicSobolevSpace n F 1) :
    ofL2 u v = inner ℝ u (PeriodicSobolevSpace.toL2 1 v) := rfl

/-- L² dominates the negative Sobolev norm
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_ofL2_le (u : PeriodicL2 n F) : ‖ofL2 u‖ ≤ ‖u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  calc
    ‖ofL2 u v‖ ≤ ‖u‖ * ‖PeriodicSobolevSpace.toL2 1 v‖ :=
      norm_inner_le_norm (𝕜 := ℝ) u (PeriodicSobolevSpace.toL2 1 v)
    _ ≤ ‖u‖ * ‖v‖ := mul_le_mul_of_nonneg_left
      (PeriodicSobolevSpace.norm_toL2_le 1 v) (norm_nonneg _)

/-- The inclusion has operator norm at most one
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_ofL2_operator_le : ‖ofL2 (n := n) (F := F)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
    intro u
    simpa only [one_mul] using norm_ofL2_le u)

/-- Density of H¹ in L² makes the dual inclusion injective
(`app:ch_background:prop:bg-inverse`). -/
theorem ofL2_injective : Function.Injective (ofL2 (n := n) (F := F)) := by
  intro u v h
  apply (PeriodicSobolevSpace.denseRange_toL2 1).eq_of_inner_left ℝ
  intro w
  exact DFunLike.congr_fun h w

/-- The bounded transpose of an H¹ operator
(`app:ch_background:prop:bg-inverse`). -/
def transpose (A : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1) :
    PeriodicSobolevNegativeOne n F →L[ℝ] PeriodicSobolevNegativeOne n F :=
  (ContinuousLinearMap.compL ℝ (PeriodicSobolevSpace n F 1)
    (PeriodicSobolevSpace n F 1) ℝ).flip A

/-- Transposition acts by precomposition in the evaluation pairing
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem transpose_apply
    (A : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (u : PeriodicSobolevNegativeOne n F) (v : PeriodicSobolevSpace n F 1) :
    transpose A u v = u (A v) := rfl

/-- The negative-space transpose obeys the H¹ operator bound
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_transpose_apply_le
    (A : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (u : PeriodicSobolevNegativeOne n F) : ‖transpose A u‖ ≤ ‖A‖ * ‖u‖ := by
  change ‖u.comp A‖ ≤ ‖A‖ * ‖u‖
  simpa only [mul_comm] using u.opNorm_comp_le A

/-- Transposition is bounded by the original operator norm
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_transpose_le
    (A : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1) :
    ‖transpose A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_transpose_apply_le A)

/-- Transposition preserves the identity (`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem transpose_id :
    transpose (ContinuousLinearMap.id ℝ (PeriodicSobolevSpace n F 1)) =
      ContinuousLinearMap.id ℝ (PeriodicSobolevNegativeOne n F) := by
  ext u v
  rfl

/-- Transposition reverses composition (`app:ch_background:prop:bg-inverse`). -/
theorem transpose_comp
    (A B : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1) :
    transpose (A.comp B) = (transpose B).comp (transpose A) := by
  ext u v
  rfl

/-- A self-adjoint L² operator and a compatible bounded H¹ restriction induce
the same operator on embedded L² data (`app:ch_background:prop:bg-inverse`). -/
theorem transpose_ofL2
    (A₀ : PeriodicL2 n F →L[ℝ] PeriodicL2 n F)
    (A₁ : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hself : IsSelfAdjoint A₀)
    (hcompat : ∀ v, PeriodicSobolevSpace.toL2 1 (A₁ v) =
      A₀ (PeriodicSobolevSpace.toL2 1 v)) (u : PeriodicL2 n F) :
    transpose A₁ (ofL2 u) = ofL2 (A₀ u) := by
  ext v
  change inner ℝ u (PeriodicSobolevSpace.toL2 1 (A₁ v)) =
    inner ℝ (A₀ u) (PeriodicSobolevSpace.toL2 1 v)
  rw [hcompat]
  exact (hself.isSymmetric u (PeriodicSobolevSpace.toL2 1 v)).symm

/-- The self-adjoint extension commutes with the bounded L² inclusion as maps
(`app:ch_background:prop:bg-inverse`). -/
theorem transpose_comp_ofL2
    (A₀ : PeriodicL2 n F →L[ℝ] PeriodicL2 n F)
    (A₁ : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hself : IsSelfAdjoint A₀)
    (hcompat : ∀ v, PeriodicSobolevSpace.toL2 1 (A₁ v) =
      A₀ (PeriodicSobolevSpace.toL2 1 v)) :
    (transpose A₁).comp ofL2 = ofL2.comp A₀ := by
  ext u v
  exact DFunLike.congr_fun (transpose_ofL2 A₀ A₁ hself hcompat u) v

/-- A right inverse on H¹ becomes a left inverse on H⁻¹
(`app:ch_background:prop:bg-inverse`). -/
theorem transpose_comp_eq_id
    (A B : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ _) :
    (transpose A).comp (transpose B) = ContinuousLinearMap.id ℝ _ := by
  rw [← transpose_comp, hBA, transpose_id]

/-- Mutually inverse H¹ operators have mutually inverse bounded H⁻¹ transposes
(`app:ch_background:prop:bg-inverse`). -/
theorem transpose_mutual_inverse
    (A B : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ _)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ _) :
    (transpose A).comp (transpose B) = ContinuousLinearMap.id ℝ _ ∧
      (transpose B).comp (transpose A) = ContinuousLinearMap.id ℝ _ :=
  ⟨transpose_comp_eq_id A B hBA, transpose_comp_eq_id B A hAB⟩

/-- Solving the negative-order equation is equivalent to applying the transpose
inverse (`app:ch_background:prop:bg-inverse`). -/
theorem transpose_eq_iff
    (A B : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ _)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ _)
    (u f : PeriodicSobolevNegativeOne n F) :
    transpose A u = f ↔ u = transpose B f := by
  obtain ⟨h₁, h₂⟩ := transpose_mutual_inverse A B hAB hBA
  constructor
  · intro h
    have hu := DFunLike.congr_fun h₂ u
    change transpose B (transpose A u) = u at hu
    rw [h] at hu
    exact hu.symm
  · rintro rfl
    exact DFunLike.congr_fun h₁ f

/-- Every H⁻¹ datum has a unique H⁻¹ solution for a pair of inverse H¹
operators (`app:ch_background:prop:bg-inverse`). -/
theorem existsUnique_transpose_solution
    (A B : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ _)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ _)
    (f : PeriodicSobolevNegativeOne n F) :
    ∃! u, transpose A u = f := by
  refine ⟨transpose B f, (transpose_eq_iff A B hAB hBA _ _).mpr rfl, ?_⟩
  intro u hu
  exact (transpose_eq_iff A B hAB hBA u f).mp hu

/-- The H⁻¹ solution satisfies the bound of the H¹ inverse
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_transpose_solution_le
    (A B : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ _)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ _)
    (u f : PeriodicSobolevNegativeOne n F) (hu : transpose A u = f) :
    ‖u‖ ≤ ‖B‖ * ‖f‖ := by
  rw [(transpose_eq_iff A B hAB hBA u f).mp hu]
  exact norm_transpose_apply_le B f

/-- Compatible bounded H¹ restrictions inherit an L² inverse identity, by
injectivity of H¹ → L² (`app:ch_background:prop:bg-inverse`). -/
theorem restriction_comp_eq_id
    (A₀ B₀ : PeriodicL2 n F →L[ℝ] PeriodicL2 n F)
    (A₁ B₁ : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hA : ∀ v, PeriodicSobolevSpace.toL2 1 (A₁ v) =
      A₀ (PeriodicSobolevSpace.toL2 1 v))
    (hB : ∀ v, PeriodicSobolevSpace.toL2 1 (B₁ v) =
      B₀ (PeriodicSobolevSpace.toL2 1 v))
    (hAB : A₀.comp B₀ = ContinuousLinearMap.id ℝ _) :
    A₁.comp B₁ = ContinuousLinearMap.id ℝ _ := by
  ext v
  apply PeriodicSobolevSpace.toL2_injective 1
  change PeriodicSobolevSpace.toL2 1 (A₁ (B₁ v)) = PeriodicSobolevSpace.toL2 1 v
  rw [hA, hB]
  exact DFunLike.congr_fun hAB (PeriodicSobolevSpace.toL2 1 v)

/-- L² inverse identities and compatible bounded H¹ restrictions suffice for
mutual inverse identities on H⁻¹ (`app:ch_background:prop:bg-inverse`). -/
theorem transpose_mutual_inverse_of_compatible
    (A₀ B₀ : PeriodicL2 n F →L[ℝ] PeriodicL2 n F)
    (A₁ B₁ : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hA : ∀ v, PeriodicSobolevSpace.toL2 1 (A₁ v) =
      A₀ (PeriodicSobolevSpace.toL2 1 v))
    (hB : ∀ v, PeriodicSobolevSpace.toL2 1 (B₁ v) =
      B₀ (PeriodicSobolevSpace.toL2 1 v))
    (hAB : A₀.comp B₀ = ContinuousLinearMap.id ℝ _)
    (hBA : B₀.comp A₀ = ContinuousLinearMap.id ℝ _) :
    (transpose A₁).comp (transpose B₁) = ContinuousLinearMap.id ℝ _ ∧
      (transpose B₁).comp (transpose A₁) = ContinuousLinearMap.id ℝ _ :=
  transpose_mutual_inverse A₁ B₁
    (restriction_comp_eq_id A₀ B₀ A₁ B₁ hA hB hAB)
    (restriction_comp_eq_id B₀ A₀ B₁ A₁ hB hA hBA)

/-- Uniqueness in H⁻¹ identifies a solution with the original L² inverse when
the datum is in L². This is the uniqueness step used in the regularity induction
of `app:ch_background:prop:bg-inverse`; H¹ preservation is an explicit premise. -/
theorem transpose_eq_ofL2_iff
    (A₀ B₀ : PeriodicL2 n F →L[ℝ] PeriodicL2 n F)
    (A₁ B₁ : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
    (hBself : IsSelfAdjoint B₀)
    (hA : ∀ v, PeriodicSobolevSpace.toL2 1 (A₁ v) =
      A₀ (PeriodicSobolevSpace.toL2 1 v))
    (hB : ∀ v, PeriodicSobolevSpace.toL2 1 (B₁ v) =
      B₀ (PeriodicSobolevSpace.toL2 1 v))
    (hAB : A₀.comp B₀ = ContinuousLinearMap.id ℝ _)
    (hBA : B₀.comp A₀ = ContinuousLinearMap.id ℝ _)
    (u : PeriodicSobolevNegativeOne n F) (f : PeriodicL2 n F) :
    transpose A₁ u = ofL2 f ↔ u = ofL2 (B₀ f) := by
  rw [transpose_eq_iff A₁ B₁
    (restriction_comp_eq_id A₀ B₀ A₁ B₁ hA hB hAB)
    (restriction_comp_eq_id B₀ A₀ B₁ A₁ hB hA hBA),
    transpose_ofL2 B₀ B₁ hBself hB]

end PeriodicSobolevNegativeOne
end JanetCartan
