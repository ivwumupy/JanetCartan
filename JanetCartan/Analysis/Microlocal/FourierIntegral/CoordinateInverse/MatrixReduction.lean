module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.CoordinateInverse.Reduction
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Diagonal
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Basic

/-!
# Matrix diagonal reduction for the weighted coordinate inverse

For `app:ch_regular_base:eq:actual-right-inverse`, the shared matrix PDO is
reduced entry by entry, retaining every entry of the Taylor/divergence error.
The weighted cross-normal diagonal uses the actual phase Jacobian, both
transport positions, and physical covector `2πξ`. The smoothness and integral
bounds below are inputs of the finite PDO calculus, not inverse identities.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff FourierTransform

namespace JanetCartan.FourierIntegral.CoordinateInverse

variable {n r : ℕ}

/-- Entrywise full Taylor remainder, consumed by the `Rdiag` ledger term in
`app:ch_regular_base:eq:actual-right-inverse`. Both positions remain independent. -/
def matrixDiagonalRemainder (b : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (c : FullAmplitude n r) (β : Euclidean n → ℝ) : FullAmplitude n r :=
  fun x y ξ i j ↦ Pseudodifferential.diagonalRemainderAmplitude b
    (fun x y ξ ↦ c x y ξ i j) β x y ξ

/-- The shared matrix PDO for a scalar multiple of the identity acts
componentwise. Consumer: the principal cancellation in
`app:ch_regular_base:eq:actual-right-inverse`. -/
theorem matrixSourceIndependentOperator_scalar_identity
    (a : Euclidean n → Euclidean n → ℂ)
    (u : Fin r → 𝓢(Euclidean n, ℂ)) (x : Euclidean n) (i : Fin r) :
    Pseudodifferential.matrixSourceIndependentOperator
      (fun x ξ ↦ a x ξ • (1 : Matrix (Fin r) (Fin r) ℂ)) u x i =
        Pseudodifferential.sourceIndependentOperator a (u i) x := by
  classical
  unfold Pseudodifferential.matrixSourceIndependentOperator
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Matrix.one_apply_ne (Ne.symm hji), Pseudodifferential.sourceIndependentOperator,
      Real.fourierInv_eq]
  · simp

/-- The actual matrix principal PDO cancels on the inner physical/Fourier
plateau. No global plateau in the output variable is required.
Source: `app:ch_regular_base:eq:actual-right-inverse`. -/
theorem matrix_principalOperator_inner_plateau
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (χg χe : Euclidean n → ℝ) (q : Euclidean n → ℂ)
    (hq : q.HasTemperateGrowth)
    (hplateau : ∀ x ξ, χe x ≠ 0 → q ξ ≠ 0 →
      χg (η x x ((2 * Real.pi) • ξ)) = 1)
    (u : Fin r → 𝓢(Euclidean n, ℂ)) (x : Euclidean n) :
    (χe x : ℂ) • Pseudodifferential.matrixSourceIndependentOperator
      (fun x ξ ↦ principalSymbol η χg x ξ • (1 : Matrix (Fin r) (Fin r) ℂ))
      (fun i ↦ Pseudodifferential.schwartzFrequencyMultiplier q (u i)) x =
        (χe x : ℂ) • (fun i ↦ Pseudodifferential.schwartzFrequencyMultiplier q (u i) x) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, matrixSourceIndependentOperator_scalar_identity]
  exact weighted_principalOperator_inner_plateau η χg χe q hq hplateau (u i) x

/-- The exact matrix reduction before principal cancellation. This connects
the scalar PDO theorem to the finite matrix cross-normal, with an explicit
Taylor remainder rather than a new abstract error.
Source: `app:ch_regular_base:eq:actual-right-inverse`. -/
theorem matrix_diagonal_reduction
    (b : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (c : FullAmplitude n r) (β : Euclidean n → ℝ)
    (u : Fin r → 𝓢(Euclidean n, ℂ)) (x : Euclidean n)
    (hc : ∀ i j, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      c p.1 p.2.1 p.2.2 i j)) (hβ : ContDiff ℝ ∞ β)
    (hβc : ∀ i j ξ z, c x z ξ i j ≠ 0 → β z = 1)
    (hβu : ∀ j y, u j y ≠ 0 → β y = 1)
    (huc : ∀ j, HasCompactSupport (u j : Euclidean n → ℂ))
    (hi : ∀ i j, Integrable (Pseudodifferential.sourceAmplitudeTransform
      (fun x y ξ ↦ c x y ξ i j) (u j) x))
    (hid : ∀ i j, Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.diagonalAmplitude (fun x y ξ ↦ c x y ξ i j) β) (u j) x))
    (hir : ∀ i j, Integrable (Pseudodifferential.sourceAmplitudeTransform
      (fun x y ξ ↦ matrixDiagonalRemainder b c β x y ξ i j) (u j) x))
    (hiB : ∀ i j, Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.fullTaylorCoefficient (fun x y ξ ↦ c x y ξ i j) β) (u j) x)) :
    Pseudodifferential.matrixFullAmplitudeOperator c (fun y j ↦ u j y) x =
      Pseudodifferential.matrixSourceIndependentOperator (fun x ξ ↦ c x x ξ) u x +
        Pseudodifferential.matrixFullAmplitudeOperator (matrixDiagonalRemainder b c β)
          (fun y j ↦ u j y) x := by
  funext i
  simp only [Pseudodifferential.matrixFullAmplitudeOperator,
    Pseudodifferential.matrixSourceIndependentOperator, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pseudodifferential.fullAmplitudeOperator_eq_diagonal_add_remainder b
    (fun x y ξ ↦ c x y ξ i j) β (u j) x (hc i j) hβ (hβc i j)
    (u j).continuous (huc j) (hi i j) (hid i j) (hir i j) (hiB i j),
    diagonalAmplitude_inner_input _ β (u j) (hβu j)]
  rfl

/-- The weighted cross-normal in unit Fourier coordinates, with its actual
inverse-Jacobian amplitude. Its two transport positions are not identified.
Consumer: the exact cross-normal input of `app:ch_regular_base:eq:actual-right-inverse`. -/
def unitWeightedCrossNormal
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg : Euclidean n → ℝ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n) : FullAmplitude n r :=
  fun x y ξ ↦ crossNormalAmplitude (fun x u ↦ (χg u : ℂ) • U x u)
    (fun x u ↦ (χg u : ℂ) • weightedForwardAmplitude (phaseJacobian S x u) (U x u))
    η (fun x y u ↦ fderiv ℝ (NormalComparison.averagedGradient S x y) u)
    x y ((2 * Real.pi) • ξ)

/-- The actual weighted matrix diagonal in unit frequencies, derived from
phase and matrix gaps. Source: `app:ch_regular_base:eq:actual-matrix-inverse`.
For a zero-extended chart the consumer must additionally verify chart membership. -/
theorem unitWeightedCrossNormal_diagonal
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg : Euclidean n → ℝ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (x ξ : Euclidean n)
    (hgrad : DifferentiableAt ℝ (fun u ↦ gradient (fun z ↦ S z u) x)
      (η x x ((2 * Real.pi) • ξ)))
    (hgap : phaseJacobian S x (η x x ((2 * Real.pi) • ξ)) ≠ 0)
    (hU : IsUnit (U x (η x x ((2 * Real.pi) • ξ))).det) :
    unitWeightedCrossNormal S U χg η x x ξ =
      principalSymbol η χg x ξ • (1 : Matrix (Fin r) (Fin r) ℂ) :=
  weighted_crossNormalAmplitude_diagonal S U χg η x ((2 * Real.pi) • ξ) hgrad hgap hU

/-- Identification of the diagonal PDO of the actual weighted cross-normal.
Only phase and inverse gaps at the output position are used; this supplies
the principal operator to the physical commutator step in
`app:ch_regular_base:eq:actual-right-inverse`. -/
theorem unitWeightedCrossNormal_principalOperator
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg : Euclidean n → ℝ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (u : Fin r → 𝓢(Euclidean n, ℂ)) (x : Euclidean n)
    (hgrad : ∀ ξ, DifferentiableAt ℝ (fun u ↦ gradient (fun z ↦ S z u) x)
      (η x x ((2 * Real.pi) • ξ)))
    (hgap : ∀ ξ, phaseJacobian S x (η x x ((2 * Real.pi) • ξ)) ≠ 0)
    (hU : ∀ ξ, IsUnit (U x (η x x ((2 * Real.pi) • ξ))).det) :
    Pseudodifferential.matrixSourceIndependentOperator
      (fun x ξ ↦ unitWeightedCrossNormal S U χg η x x ξ) u x =
        Pseudodifferential.matrixSourceIndependentOperator
          (fun x ξ ↦ principalSymbol η χg x ξ • (1 : Matrix (Fin r) (Fin r) ℂ)) u x := by
  funext i
  simp only [Pseudodifferential.matrixSourceIndependentOperator,
    Pseudodifferential.sourceIndependentOperator]
  simp_rw [unitWeightedCrossNormal_diagonal S U χg η x _ (hgrad _) (hgap _) (hU _)]

/-- Exact weighted matrix reduction, including the complete entrywise Taylor
remainder and both independent physical positions. Phase and matrix gaps give
the principal term; the analytic inputs are the PDO smoothness and convergence
hypotheses, not a hypothesized inverse defect. The source mask drops only on
the specified compact inner input. Consumer: `Rdiag` in the coordinate inverse
ledger (`app:ch_regular_base:eq:actual-right-inverse`). -/
theorem weighted_matrix_diagonal_reduction
    (b : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χg β : Euclidean n → ℝ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (u : Fin r → 𝓢(Euclidean n, ℂ)) (x : Euclidean n)
    (hgrad : ∀ ξ, DifferentiableAt ℝ (fun u ↦ gradient (fun z ↦ S z u) x)
      (η x x ((2 * Real.pi) • ξ)))
    (hgap : ∀ ξ, phaseJacobian S x (η x x ((2 * Real.pi) • ξ)) ≠ 0)
    (hU : ∀ ξ, IsUnit (U x (η x x ((2 * Real.pi) • ξ))).det)
    (hc : ∀ i j, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      unitWeightedCrossNormal S U χg η p.1 p.2.1 p.2.2 i j))
    (hβ : ContDiff ℝ ∞ β)
    (hβc : ∀ i j ξ z, unitWeightedCrossNormal S U χg η x z ξ i j ≠ 0 → β z = 1)
    (hβu : ∀ j y, u j y ≠ 0 → β y = 1)
    (huc : ∀ j, HasCompactSupport (u j : Euclidean n → ℂ))
    (hi : ∀ i j, Integrable (Pseudodifferential.sourceAmplitudeTransform
      (fun x y ξ ↦ unitWeightedCrossNormal S U χg η x y ξ i j) (u j) x))
    (hid : ∀ i j, Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.diagonalAmplitude
        (fun x y ξ ↦ unitWeightedCrossNormal S U χg η x y ξ i j) β) (u j) x))
    (hir : ∀ i j, Integrable (Pseudodifferential.sourceAmplitudeTransform
      (fun x y ξ ↦ matrixDiagonalRemainder b (unitWeightedCrossNormal S U χg η) β
        x y ξ i j) (u j) x))
    (hiB : ∀ i j, Integrable (Pseudodifferential.sourceAmplitudeTransform
      (Pseudodifferential.fullTaylorCoefficient
        (fun x y ξ ↦ unitWeightedCrossNormal S U χg η x y ξ i j) β) (u j) x)) :
    Pseudodifferential.matrixFullAmplitudeOperator (unitWeightedCrossNormal S U χg η)
        (fun y j ↦ u j y) x -
      Pseudodifferential.matrixSourceIndependentOperator
        (fun x ξ ↦ principalSymbol η χg x ξ • (1 : Matrix (Fin r) (Fin r) ℂ)) u x =
      Pseudodifferential.matrixFullAmplitudeOperator
        (matrixDiagonalRemainder b (unitWeightedCrossNormal S U χg η) β)
        (fun y j ↦ u j y) x := by
  rw [matrix_diagonal_reduction b (unitWeightedCrossNormal S U χg η) β u x
    hc hβ hβc hβu huc hi hid hir hiB,
    unitWeightedCrossNormal_principalOperator S U χg η u x hgrad hgap hU]
  exact add_sub_cancel_left _ _

end JanetCartan.FourierIntegral.CoordinateInverse
