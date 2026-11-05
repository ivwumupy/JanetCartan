module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Factorization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.KernelBound
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity.Density
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity.TestEnergy

/-!
# Fixed source-square double-kernel energy identity

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the literal frozen
channel energy defect equals the fixed source-square double-kernel energy.
The compact smooth test identity extends to supported L² inputs by continuity
of both bounded-operator quadratic forms and density inside the auxiliary
plateau. The original measurement and source masks remain unchanged.
Consumer: the source-tail L¹-squared estimate in `SourceTail.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace
open JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

/-- The literal frozen-channel energy defect is the double integral of the
fixed source-square kernel on every L² input supported almost everywhere in
the input ball (`paper-v2.tex`, `app:ch_background:prop:bg-frame`). This
identification supplies the source-tail L¹-squared estimate without any
additional analytic or dimension hypothesis. -/
theorem fixedEuclideanChannel_energy_defect_eq_kernel (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²)
    (hu : ∀ᵐ x ∂volume, x ∉ ball (0 : E) R → u x = 0) :
    ‖(uncutRealChannel A).adjoint u‖ ^ 2 - ‖(fixedEuclideanChannel hR A).adjoint u‖ ^ 2 =
      ∫ x, ∫ y, ⟪u x, fixedSourceTailKernel hR A (x, y) (u y)⟫ := by
  rw [fixedEuclideanChannel_adjoint_of_supported hR A u hu,
    ← fixedSourceTailOperator_inner_eq_integral hR A u]
  have hclosed : IsClosed {v : R² |
      ‖(uncutRealChannel A).adjoint v‖ ^ 2 -
        ‖fixedPhysicalMask hR 2 ((uncutRealChannel A).adjoint v)‖ ^ 2 =
          ⟪v, fixedSourceTailOperator hR A v⟫} :=
    isClosed_eq
      (((uncutRealChannel A).adjoint.continuous.norm.pow 2).sub
        (((fixedPhysicalMask hR 2).continuous.comp
          (uncutRealChannel A).adjoint.continuous).norm.pow 2))
      (continuous_id.inner (fixedSourceTailOperator hR A).continuous)
  exact closure_minimal
    (fun v hv ↦ fixedSourceTail_energy_eq_inner_of_test hR A v hv) hclosed
    (fixedSourceTailTestInputs_dense_supported hR u hu)

end JanetCartan.ContinuumNormal.FrozenImageComparison
