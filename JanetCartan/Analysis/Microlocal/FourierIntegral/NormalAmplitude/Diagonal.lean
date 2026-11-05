module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Basic

/-!
# The weighted cross-normal diagonal

The diagonal in Step 4 of `app:ch_regular_base:thm:actual-calculus`, including
the identification of the actual averaged-gradient Jacobian and both copies
of the real graph cutoff. The input matrix inverse gap remains conditional.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
open NormalComparison

private lemma gradient_coordinate_eq_partialDeriv {n : ℕ} (f : Euclidean n → ℝ) (x : Euclidean n) (i : Fin n) :
    (gradient f x) i = partialDeriv f x i := by
  have h : inner ℝ (EuclideanSpace.single i 1) (gradient f x) = partialDeriv f x i := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using h
/-- The actual diagonal averaged-gradient Jacobian is the mixed phase matrix,
with no determinant identity assumed. Source:
`app:ch_regular_base:eq:actual-matrix-inverse`, Step 4. -/
theorem averagedGradient_diagonal_det {n : ℕ} (S : Euclidean n → Euclidean n → ℝ) (x u : Euclidean n)
    (h : DifferentiableAt ℝ (fun η ↦ gradient (fun z ↦ S z η) x) u) :
    (fderiv ℝ (averagedGradient S x x) u).det = (mixedPhaseMatrix S x u).det := by
  have he : averagedGradient S x x = fun η ↦ gradient (fun z ↦ S z η) x := by
    funext η
    simp [averagedGradient, averagedPhaseDifferential, gradient]
  rw [he]
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  change (fderiv ℝ (fun η ↦ gradient (fun z ↦ S z η) x) u).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix b]
  congr 1
  ext i j
  have hi : (fun η ↦ partialDeriv (fun z ↦ S z η) x i) =
      fun η ↦ (gradient (fun z ↦ S z η) x) i :=
    funext fun η ↦ (gradient_coordinate_eq_partialDeriv _ _ _).symm
  rw [LinearMap.toMatrix_apply]
  change (b.repr ((fderiv ℝ (fun η ↦ gradient (fun z ↦ S z η) x) u) (b j))) i =
    (fderiv ℝ (fun η ↦ partialDeriv (fun z ↦ S z η) x i) u) (EuclideanSpace.single j 1)
  rw [hi]
  have hd := ((EuclideanSpace.proj i).hasFDerivAt.comp u h.hasFDerivAt).fderiv
  simp only [EuclideanSpace.coe_proj, Function.comp_def] at hd
  rw [hd]
  simp [b, EuclideanSpace.basisFun_apply, OrthonormalBasis.coe_toBasis_repr_apply]

/-- Both real frequency cutoffs survive the weighted cancellation. This
uses `weighted_principal_amplitude` for the inverse algebra, as required in
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem weighted_cutoff_principal_amplitude {r : ℕ} (c j : ℝ) (hj : j ≠ 0)
    (U : Matrix (Fin r) (Fin r) ℂ) (hU : IsUnit U.det) :
    j⁻¹ • (((c : ℂ) • U) *
      ((c : ℂ) • weightedForwardAmplitude j U).conjTranspose) =
      (c ^ 2 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  rw [Matrix.conjTranspose_smul, weightedForwardAmplitude_conjTranspose]
  simp only [Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  have he : j⁻¹ • (((c : ℂ) * c) • (U * reverseWeight j U)) =
      ((c : ℂ) * c) • ((j : ℂ)⁻¹ • (U * reverseWeight j U)) := by
    rw [smul_comm]
    congr 1
    ext i k
    simp [Complex.real_smul]
  rw [he, weighted_principal_amplitude j hj U hU, pow_two]

/-- The full weighted cross-normal has diagonal `χ_g(η)² I`, evaluated at
its actual inverse covector (`app:ch_regular_base:eq:actual-matrix-inverse`).
The phase derivative, Jacobian gap, and matrix inverse gap are primitive inputs;
no normal amplitude estimate is assumed. -/
theorem weighted_crossNormalAmplitude_diagonal {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χ : Euclidean n → ℝ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (x ξ : Euclidean n)
    (hgrad : DifferentiableAt ℝ (fun u ↦ gradient (fun z ↦ S z u) x) (η x x ξ))
    (hgap : phaseJacobian S x (η x x ξ) ≠ 0)
    (hU : IsUnit (U x (η x x ξ)).det) :
    crossNormalAmplitude (fun x u ↦ (χ u : ℂ) • U x u)
      (fun x u ↦ (χ u : ℂ) • weightedForwardAmplitude (phaseJacobian S x u) (U x u))
      η (fun x y u ↦ fderiv ℝ (averagedGradient S x y) u) x x ξ =
        (χ (η x x ξ) : ℂ)^2 • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  unfold crossNormalAmplitude crossNormalNumerator
  rw [averagedGradient_diagonal_det S x (η x x ξ) hgrad]
  exact weighted_cutoff_principal_amplitude _ _ hgap _ hU

/-- The weighted identity holds for the literal extension on its chart,
where the buffered construction places the inner frequency plateau.
Source: `app:ch_regular_base:eq:actual-matrix-inverse`, Step 4. -/
theorem weighted_extendedCrossNormalAmplitude_diagonal {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χ : Euclidean n → ℝ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (Ω : Set (NormalVariables n)) (x ξ : Euclidean n) (hΩ : (x, (x, ξ)) ∈ Ω)
    (hgrad : DifferentiableAt ℝ (fun u ↦ gradient (fun z ↦ S z u) x) (η x x ξ))
    (hgap : phaseJacobian S x (η x x ξ) ≠ 0)
    (hU : IsUnit (U x (η x x ξ)).det) :
    extendedCrossNormalAmplitude Ω (fun x u ↦ (χ u : ℂ) • U x u)
      (fun x u ↦ (χ u : ℂ) • weightedForwardAmplitude (phaseJacobian S x u) (U x u))
      η (fun x y u ↦ fderiv ℝ (averagedGradient S x y) u) (x, (x, ξ)) =
        (χ (η x x ξ) : ℂ)^2 • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  rw [extendedCrossNormalAmplitude, Set.indicator_of_mem hΩ]
  exact weighted_crossNormalAmplitude_diagonal S U χ η x ξ hgrad hgap hU

end JanetCartan.FourierIntegral
