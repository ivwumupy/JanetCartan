module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.AssemblyBasic

/-! Scalar and exact-source transport used by the actual primary node proof
(`main:eq:primary-strain`). -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer

/-- The original dimension coefficient preserves the nonnegative common
source price after summing the two quadratures. -/
theorem node_coefficient_nonneg {n : ℕ} (hn : 5 ≤ n) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ UniformStep.projectedStressResidualConstant hn * (C+C) := by
  exact mul_nonneg (le_of_lt (UniformStep.projectedStressResidualConstant_pos hn))
    (add_nonneg hC hC)

/-- Apply the already proved source and carrier identities before the two
quadrature bounds are assembled. No source estimate is inferred here. -/
theorem point_bound_of_eq {X V : Type*} [Norm V] {f g : X → V}
    (hf : f = g) {r s C : ℝ} (hr : r = s) (q : ℕ) (x : X)
    (h : ‖f x‖ ≤ C * r ^ (-(q : ℝ))) :
    ‖g x‖ ≤ C * s ^ (-(q : ℝ)) := by
  cases hf
  cases hr
  exact h

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer
end
