module

public import JanetCartan.Analysis.Microlocal.SingleChannel.Oscillatory

/-!
# Frobenius components in a single channel

Flattening a fixed matrix into the finite vector used by
`app:ch_osc:prop:osc-channel` preserves the Frobenius norm exactly.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.SingleChannel

/-- Flatten the two finite matrix indices into the component index of
`app:ch_osc:prop:osc-channel`. -/
def matrixChannelComponents {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin (m * n)) :=
  WithLp.toLp 2 (fun k ↦ A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

/-- There is no norm loss between fixed matrix Frobenius components and the
single-channel theorem's Euclidean components (`app:ch_osc:prop:osc-channel`). -/
theorem norm_matrixChannelComponents {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ‖matrixChannelComponents A‖ = ‖A‖ := by
  rw [PiLp.norm_eq_of_L2, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  simp only [matrixChannelComponents, WithLp.ofLp_toLp, Real.rpow_two]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]

end JanetCartan.SingleChannel
