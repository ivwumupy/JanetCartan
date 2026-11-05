module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Adjugate
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul

import Mathlib.Tactic.Ring

/-!
# Scalar reduction of the actual reduced stress operator

Definitions and the product identity from `app:ch_waves:eq:reduced-symbol` and
`app:ch_waves:thm:leading`. The zero-order term uses the induced Christoffel
coefficients through `symmCovariantDeriv`; it is not discarded. The frame is a
parameter here, so these identities apply to the projected frame once constructed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport

variable {n N : ℕ}

/-- The actual reduced operator `P_G` of `app:ch_waves:eq:reduced-symbol`. -/
def reducedOperator (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (u : Euclidean n → Euclidean n)
    (x : Euclidean n) : Fin n → ℝ :=
  fun i ↦ tensorPairing (Q x i) (symmCovariantDeriv F u x)

/-- The principal coefficient `C_a` in `app:ch_waves:thm:leading`. -/
def principalCoefficient (Q : Fin n → MetricTensor n) (a : Fin n) : MetricTensor n :=
  fun i j ↦ Q i a j

/-- The symbol with rows `(Q_i ξ)ᵀ` in `app:ch_waves:eq:reduced-symbol`. -/
def reducedSymbol (Q : Fin n → MetricTensor n) (ξ : Euclidean n) : MetricTensor n :=
  fun i j ↦ ∑ a, Q i j a * ξ a

/-- The principal symbol agrees with the coefficient pencil for a symmetric
stress frame (`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedSymbol_eq_sum (Q : Fin n → MetricTensor n)
    (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n) :
    reducedSymbol Q ξ = ∑ a, ξ a • principalCoefficient Q a := by
  ext i j
  simp only [reducedSymbol, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    principalCoefficient]
  apply Finset.sum_congr rfl
  intro a _
  rw [(hQ i).apply j a]
  ring

/-- The covector pencil as a continuous linear map with the Frobenius target
norm (`app:ch_waves:eq:reduced-symbol`). -/
def reducedSymbolLinearMap (Q : Fin n → MetricTensor n) :
    Euclidean n →L[ℝ] MetricTensor n :=
  LinearMap.toContinuousLinearMap {
    toFun := reducedSymbol Q
    map_add' := by
      intro ξ η
      ext i j
      simp [reducedSymbol, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a ξ
      ext i j
      simp [reducedSymbol, ← Finset.mul_sum, mul_left_comm] }

/-- The determinant symbol `p_G` in `app:ch_waves:eq:reduced-symbol`. -/
def reducedDeterminant (Q : Fin n → MetricTensor n) (ξ : Euclidean n) : ℝ :=
  (reducedSymbol Q ξ).det

/-- The `ξ_a` derivative of the actual determinant symbol is the determinant
differential in direction `C_a` (`app:ch_waves:thm:leading`). -/
theorem partialDeriv_reducedDeterminant (Q : Fin n → MetricTensor n)
    (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n) (a : Fin n) :
    partialDeriv (reducedDeterminant Q) ξ a =
      fderiv ℝ Matrix.det (reducedSymbol Q ξ) (principalCoefficient Q a) := by
  have hd := (Matrix.differentiable_det (reducedSymbol Q ξ)).hasFDerivAt.comp ξ
    ((reducedSymbolLinearMap Q).hasFDerivAt (x := ξ))
  change HasFDerivAt (reducedDeterminant Q) _ ξ at hd
  rw [partialDeriv, hd.fderiv, ContinuousLinearMap.comp_apply]
  congr 1
  change reducedSymbol Q (EuclideanSpace.single a 1) = _
  rw [reducedSymbol_eq_sum Q hQ]
  simp

/-- Product rule for the actual covariant derivative, retaining the connection
term (`app:ch_waves:thm:leading`). -/
theorem symmCovariantDeriv_smul (F : Euclidean n → Euclidean N)
    {α : Euclidean n → ℝ} {k : Euclidean n → Euclidean n} {x : Euclidean n}
    (hα : DifferentiableAt ℝ α x)
    (hk : ∀ j, DifferentiableAt ℝ (fun y ↦ k y j) x) (a b : Fin n) :
    symmCovariantDeriv F (fun y ↦ α y • k y) x a b =
      (partialDeriv α x a * k x b + partialDeriv α x b * k x a) / 2 +
        α x * symmCovariantDeriv F k x a b := by
  have hp (i j : Fin n) :
      partialDeriv (fun y ↦ α y * k y j) x i =
        partialDeriv α x i * k x j + α x * partialDeriv (fun y ↦ k y j) x i := by
    change fderiv ℝ (α * fun y ↦ k y j) x _ = _
    rw [fderiv_mul hα (hk j)]
    simp [partialDeriv, mul_comm, add_comm]
  simp only [symmCovariantDeriv, PiLp.smul_apply, smul_eq_mul, hp]
  have hs : (∑ j, christoffel F x a b j * (α x * k x j)) =
      α x * ∑ j, christoffel F x a b j * k x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

/-- The exact vector product rule for `P_G(αk)` in
`app:ch_waves:thm:leading`, including all zero-order terms. -/
theorem reducedOperator_smul (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {α : Euclidean n → ℝ} {k : Euclidean n → Euclidean n} {x : Euclidean n}
    (hQ : ∀ i, (Q x i).IsSymm) (hα : DifferentiableAt ℝ α x)
    (hk : ∀ j, DifferentiableAt ℝ (fun y ↦ k y j) x) (i : Fin n) :
    reducedOperator F Q (fun y ↦ α y • k y) x i =
      (∑ a, (principalCoefficient (Q x) a *ᵥ (fun j ↦ k x j)) i *
        partialDeriv α x a) + α x * reducedOperator F Q k x i := by
  simp only [reducedOperator, tensorPairing, symmCovariantDeriv_smul F hα hk,
    mul_add, Finset.sum_add_distrib]
  have hs : (∑ a, ∑ b, Q x i a b *
      ((partialDeriv α x a * k x b + partialDeriv α x b * k x a) / 2)) =
      ∑ a, (principalCoefficient (Q x) a *ᵥ (fun j ↦ k x j)) i *
        partialDeriv α x a := by
    have he : (∑ a, ∑ b, Q x i a b * (partialDeriv α x b * k x a)) =
        ∑ a, ∑ b, Q x i a b * (partialDeriv α x a * k x b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [(hQ i).apply b a]
    calc
      _ = ((∑ a, ∑ b, Q x i a b * (partialDeriv α x a * k x b)) +
          ∑ a, ∑ b, Q x i a b * (partialDeriv α x b * k x a)) / 2 := by
        simp only [← mul_div_assoc, mul_add, Finset.sum_add_distrib, ← Finset.sum_div]
      _ = ∑ a, ∑ b, Q x i a b * (partialDeriv α x a * k x b) := by rw [he]; ring
      _ = _ := by
        simp only [Matrix.mulVec, dotProduct, principalCoefficient, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
  rw [hs]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The principal scalar transport field `lᵀ C_a k` of
`app:ch_waves:thm:leading`. -/
def transportField (Q : Fin n → MetricTensor n) (l k : Fin n → ℝ) : Fin n → ℝ :=
  fun a ↦ l ⬝ᵥ (principalCoefficient Q a *ᵥ k)

/-- The exact scalar reduction `lᵀP_G(αk) = V·dα + (lᵀP_Gk)α`
in `app:ch_waves:thm:leading`. -/
theorem scalar_reduction (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {α : Euclidean n → ℝ} {k : Euclidean n → Euclidean n} {x : Euclidean n}
    (hQ : ∀ i, (Q x i).IsSymm) (hα : DifferentiableAt ℝ α x)
    (hk : ∀ j, DifferentiableAt ℝ (fun y ↦ k y j) x) (l : Fin n → ℝ) :
    l ⬝ᵥ reducedOperator F Q (fun y ↦ α y • k y) x =
      (∑ a, transportField (Q x) l (fun j ↦ k x j) a * partialDeriv α x a) +
        (l ⬝ᵥ reducedOperator F Q k x) * α x := by
  simp only [dotProduct, reducedOperator_smul F Q hQ hα hk, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, transportField, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- After dividing by a nonzero time coefficient, the actual reduced equation
is exactly the normalized scalar equation (`app:ch_waves:thm:leading`). This
equivalence does not posit a solution of either equation. -/
theorem scalar_reduction_normalized_iff (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {α : Euclidean n → ℝ} {k : Euclidean n → Euclidean n} {x : Euclidean n}
    (hQ : ∀ i, (Q x i).IsSymm) (hα : DifferentiableAt ℝ α x)
    (hk : ∀ j, DifferentiableAt ℝ (fun y ↦ k y j) x) (l : Fin n → ℝ)
    (t : Fin n) (ht : transportField (Q x) l (fun j ↦ k x j) t ≠ 0) :
    l ⬝ᵥ reducedOperator F Q (fun y ↦ α y • k y) x = 0 ↔
      (∑ a, (transportField (Q x) l (fun j ↦ k x j) a /
        transportField (Q x) l (fun j ↦ k x j) t) * partialDeriv α x a) +
        ((l ⬝ᵥ reducedOperator F Q k x) /
          transportField (Q x) l (fun j ↦ k x j) t) * α x = 0 := by
  rw [scalar_reduction F Q hQ hα hk l]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← add_div]
  exact (div_eq_zero_iff.trans (or_iff_left ht)).symm

/-- The principal transport field is the determinant's covector gradient times
the selected minor (`app:ch_waves:thm:leading`). -/
theorem transportField_eq_minor_mul_partialDeriv (Q : Fin n → MetricTensor n)
    (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : reducedDeterminant Q ξ = 0) {r c : Fin n}
    (hminor : (reducedSymbol Q ξ).adjugate r c ≠ 0) (a : Fin n) :
    transportField Q (leftNullvector (reducedSymbol Q ξ) r)
      (rightNullvector (reducedSymbol Q ξ) c) a =
        (reducedSymbol Q ξ).adjugate r c * partialDeriv (reducedDeterminant Q) ξ a := by
  rw [partialDeriv_reducedDeterminant Q hQ]
  exact (minor_mul_fderiv_det hchar hminor _).symm

/-- Uniform minor and root gaps give the denominator gap for the time-normalized
transport field on an actual characteristic covector (`app:ch_waves:thm:leading`). -/
theorem transportField_time_gap (Q : Fin n → MetricTensor n)
    (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : reducedDeterminant Q ξ = 0) {r c t : Fin n}
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hminor : δ ≤ |(reducedSymbol Q ξ).adjugate r c|)
    (hroot : ε ≤ |partialDeriv (reducedDeterminant Q) ξ t|) :
    δ * ε ≤ |transportField Q (leftNullvector (reducedSymbol Q ξ) r)
      (rightNullvector (reducedSymbol Q ξ) c) t| := by
  rw [partialDeriv_reducedDeterminant Q hQ] at hroot
  exact transportCoefficient_gap hchar hδ hε hminor hroot

/-- The simple root makes the actual time coefficient nonzero
(`app:ch_waves:thm:leading`). -/
theorem transportField_time_ne_zero (Q : Fin n → MetricTensor n)
    (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : reducedDeterminant Q ξ = 0) {r c t : Fin n}
    (hminor : (reducedSymbol Q ξ).adjugate r c ≠ 0)
    (hroot : partialDeriv (reducedDeterminant Q) ξ t ≠ 0) :
    transportField Q (leftNullvector (reducedSymbol Q ξ) r)
      (rightNullvector (reducedSymbol Q ξ) c) t ≠ 0 := by
  rw [transportField_eq_minor_mul_partialDeriv Q hQ ξ hchar hminor]
  exact mul_ne_zero hminor hroot

/-- Time normalization cancels the selected minor: the spatial transport
directions are the ratios of the determinant's covector derivatives. This is
the link to the characteristic flow in `app:ch_waves:thm:leading`. -/
theorem transportField_ratio (Q : Fin n → MetricTensor n)
    (hQ : ∀ i, (Q i).IsSymm) (ξ : Euclidean n)
    (hchar : reducedDeterminant Q ξ = 0) {r c : Fin n}
    (hminor : (reducedSymbol Q ξ).adjugate r c ≠ 0) (a t : Fin n) :
    transportField Q (leftNullvector (reducedSymbol Q ξ) r)
        (rightNullvector (reducedSymbol Q ξ) c) a /
      transportField Q (leftNullvector (reducedSymbol Q ξ) r)
        (rightNullvector (reducedSymbol Q ξ) c) t =
      partialDeriv (reducedDeterminant Q) ξ a / partialDeriv (reducedDeterminant Q) ξ t := by
  rw [transportField_eq_minor_mul_partialDeriv Q hQ ξ hchar hminor,
    transportField_eq_minor_mul_partialDeriv Q hQ ξ hchar hminor]
  exact mul_div_mul_left _ _ hminor

end JanetCartan.NullTransport
