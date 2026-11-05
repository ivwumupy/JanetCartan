module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.StressFrame.Frobenius
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Kernel
public import JanetCartan.LinearAlgebra.NormalInverse
public import JanetCartan.LinearAlgebra.GramProjection

/-!
# Projected cube stresses

The concrete projection in `app:ch_background:defn:bg-geometry`. The definition
works for every normal map; its basis property will follow from perturbation and
rank–nullity, rather than being an assumption in its definition.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.StressFrame

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- `Q_i = Π_(ker B) Q_i⁰` in `app:ch_background:defn:bg-geometry`. -/
def projectedCubeStress (B : SymmetricTensor n →ₗ[ℝ] F) (i : Fin n) :
    SymmetricTensor n := B.ker.starProjection (cubeSymmetricStress n i)

omit [FiniteDimensional ℝ F] in
/-- Projected cube stresses are in the stress kernel
(`app:ch_background:defn:bg-geometry`). -/
theorem projectedCubeStress_mem_ker (B : SymmetricTensor n →ₗ[ℝ] F) (i : Fin n) :
    projectedCubeStress B i ∈ B.ker :=
  Submodule.starProjection_apply_mem _ _

/-- The projection agrees with the canonical inverse formula in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem projectedCubeStress_eq_kernelProjection (B : SymmetricTensor n →ₗ[ℝ] F)
    (hB : Function.Surjective B) (i : Fin n) :
    projectedCubeStress B i =
      NormalInverse.kernelProjection B hB (cubeSymmetricStress n i) := by
  rw [NormalInverse.kernelProjection_eq_starProjection]
  rfl

/-- At the cube reference the projected stresses recover the frozen stresses
(`app:ch_background:defn:bg-carriers`). -/
theorem projectedCubeStress_reference (hn : 5 ≤ n) (i : Fin n) :
    projectedCubeStress (cubeNormalLinearMapOnSymmetric n) i =
      cubeSymmetricStress n i := by
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [cubeNormalLinearMapOnSymmetric_ker hn]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- Rank–nullity turns independence of the projected stresses into spanning
(`app:ch_seed:setup:seed-current`). Independence is discharged by the separate
perturbation theorem, not included in the definition of the frame. -/
theorem ker_eq_span_projectedCubeStress (B : SymmetricTensor n →ₗ[ℝ] F)
    (hB : Function.Surjective B)
    (hdim : Module.finrank ℝ (SymmetricTensor n) = n + Module.finrank ℝ F)
    (hQ : LinearIndependent ℝ (projectedCubeStress B)) :
    B.ker = Submodule.span ℝ (Set.range (projectedCubeStress B)) := by
  exact CubeKernel.ker_eq_span_of_finrank B _ hQ
    (fun i ↦ projectedCubeStress_mem_ker B i) hB (by simpa using hdim)

/-- The projected stresses as a basis of the kernel, after the rank and
independence steps of `app:ch_seed:setup:seed-current`. -/
def projectedCubeStressBasis (B : SymmetricTensor n →ₗ[ℝ] F)
    (hB : Function.Surjective B)
    (hdim : Module.finrank ℝ (SymmetricTensor n) = n + Module.finrank ℝ F)
    (hQ : LinearIndependent ℝ (projectedCubeStress B)) : Module.Basis (Fin n) ℝ B.ker :=
  (Module.Basis.span hQ).map
    (LinearEquiv.ofEq _ _ (ker_eq_span_projectedCubeStress B hB hdim hQ).symm)

/-- The basis vectors are the specified projections, rather than a newly
chosen basis (`app:ch_background:defn:bg-geometry`). -/
@[simp] theorem projectedCubeStressBasis_apply (B : SymmetricTensor n →ₗ[ℝ] F)
    (hB : Function.Surjective B)
    (hdim : Module.finrank ℝ (SymmetricTensor n) = n + Module.finrank ℝ F)
    (hQ : LinearIndependent ℝ (projectedCubeStress B)) (i : Fin n) :
    (projectedCubeStressBasis B hB hdim hQ i : SymmetricTensor n) =
      projectedCubeStress B i := by
  simp [projectedCubeStressBasis, Module.Basis.map_apply, Module.Basis.span_apply]

/-- Reconstruction in the projected stress basis by the inverse Gram matrix,
as in `main:eq:completion-error`. -/
theorem kernelProjection_eq_inverseGramReconstruction
    (B : SymmetricTensor n →ₗ[ℝ] F) (hB : Function.Surjective B)
    (hdim : Module.finrank ℝ (SymmetricTensor n) = n + Module.finrank ℝ F)
    (hQ : LinearIndependent ℝ (projectedCubeStress B)) (H : SymmetricTensor n) :
    B.ker.starProjection H = inverseGramReconstruction (projectedCubeStress B)
      (frameContractions (projectedCubeStress B) H) := by
  have hspan := ker_eq_span_projectedCubeStress B hB hdim hQ
  calc
    B.ker.starProjection H =
        (Submodule.span ℝ (Set.range (projectedCubeStress B))).starProjection H := by
      rw [hspan]
    _ = _ := starProjection_span_eq_inverseGramReconstruction hQ H

end JanetCartan.StressFrame
