module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.DirectAmplitude

/-!
# Scalar transport implies compatibility with the left nullvector

The transport step of `paper-v2.tex`,
`app:ch_regular_base:lem:characteristic-kernel`, uses the physical operator
`WKB.firstOrderApply`, including its zeroth-order term. Its product rule gives
`lᵀ P(α k) = dα(v) + α lᵀPk` when `lᵀ A_j k = v_j`. Thus the scalar
transport equation supplies the projection-zero premise of
`firstOrder_directCorrection_identity`, column by column.

The actual normalized nullvectors and the identification
`v = (1, -h_η)` remain geometric obligations. `RowTransport` constructs the
signed solution on the same supplied flow; no matrix transport solution or
complete residual estimate is an input to these identities.
-/

@[expose] public noncomputable section

open JanetCartan.WKB

namespace JanetCartan.RegularSector.Characteristic

variable {n : ℕ} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- The product rule for the physical operator on one column of `W₀ = ka`,
retaining its zeroth-order term
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem firstOrderApply_smul
    (C : Euclidean n → Fin n → F →ₗ[ℂ] F) (D : Euclidean n → F →ₗ[ℂ] F)
    {α : Euclidean n → ℂ} {k : Euclidean n → F} {x : Euclidean n}
    (hα : DifferentiableAt ℝ α x) (hk : DifferentiableAt ℝ k x) :
    firstOrderApply C D (fun y ↦ α y • k y) x =
      (∑ i, partialDeriv α x i • C x i (k x)) + α x • firstOrderApply C D k x := by
  have hd (i : Fin n) : partialDeriv (fun y ↦ α y • k y) x i =
      partialDeriv α x i • k x + α x • partialDeriv k x i := by
    change fderiv ℝ (α • k) x (EuclideanSpace.single i 1) = _
    rw [(hα.hasFDerivAt.smul hk.hasFDerivAt).fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, partialDeriv, add_comm]
  simp only [firstOrderApply, hd, map_add, map_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum, smul_add, add_assoc]

/-- Left contraction reduces the physical matrix equation to the derivative
along the normalized real transport field. This is the exact scalar equation
used in `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem firstOrder_left_smul
    (C : Euclidean n → Fin n → F →ₗ[ℂ] F) (D : Euclidean n → F →ₗ[ℂ] F)
    {α : Euclidean n → ℂ} {k : Euclidean n → F} {x : Euclidean n}
    (hα : DifferentiableAt ℝ α x) (hk : DifferentiableAt ℝ k x)
    (l : F →ₗ[ℂ] ℂ) (v : Euclidean n)
    (hv : ∀ i, l (C x i (k x)) = (v i : ℂ)) :
    l (firstOrderApply C D (fun y ↦ α y • k y) x) =
      fderiv ℝ α x v + α x * l (firstOrderApply C D k x) := by
  rw [firstOrderApply_smul C D hα hk, map_add, map_sum, map_smul]
  have hsum : ∑ j, v j • partialDeriv α x j = fderiv ℝ α x v := by
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, partialDeriv] using
      congrArg (fderiv ℝ α x) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)
  simp only [map_smul, hv, smul_eq_mul]
  congr 1
  simpa only [Complex.real_smul, mul_comm] using hsum

/-- The scalar transport equation kills the oblique projection of `P W₀`.
For the direct sector `z = A_t k`, so the projection is exactly `(A_t k) lᵀ`.
This discharges the algebraic compatibility used by
`firstOrder_directCorrection_identity` once the actual row transport and
normalized coefficients are instantiated
(`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem projected_firstOrder_eq_zero_of_transport
    (C : Euclidean n → Fin n → F →ₗ[ℂ] F) (D : Euclidean n → F →ₗ[ℂ] F)
    {α : Euclidean n → ℂ} {k : Euclidean n → F} {x : Euclidean n}
    (hα : DifferentiableAt ℝ α x) (hk : DifferentiableAt ℝ k x)
    (l : F →ₗ[ℂ] ℂ) (v : Euclidean n) (z : F)
    (hv : ∀ i, l (C x i (k x)) = (v i : ℂ))
    (htransport : fderiv ℝ α x v = -l (firstOrderApply C D k x) * α x) :
    (l.smulRight z) (firstOrderApply C D (fun y ↦ α y • k y) x) = 0 := by
  change l (firstOrderApply C D (fun y ↦ α y • k y) x) • z = 0
  rw [firstOrder_left_smul C D hα hk l v hv, htransport]
  have he : -l (firstOrderApply C D k x) * α x +
      α x * l (firstOrderApply C D k x) = 0 := by ring
  rw [he, zero_smul]

end JanetCartan.RegularSector.Characteristic
