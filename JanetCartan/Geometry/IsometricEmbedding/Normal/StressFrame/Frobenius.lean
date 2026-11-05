module

public import JanetCartan.Analysis.Matrix.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Frobenius inner product on symmetric tensors

The pairing in `app:ch_background:defn:bg-geometry`, with the previously chosen
Frobenius norm. The instance is scoped to avoid changing matrix norm conventions.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.StressFrame

/-- The operator topology for `app:ch_background:defn:bg-geometry` is the
topology of the chosen Frobenius norm. -/
scoped instance tensorTopology (n : ℕ) : TopologicalSpace (MetricTensor n) :=
  (Matrix.frobeniusSeminormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The Frobenius Hilbert structure used for the stress projection in
`app:ch_background:defn:bg-geometry`. It preserves the existing norm. -/
scoped instance symmetricTensorInnerProductSpace (n : ℕ) :
    InnerProductSpace ℝ (SymmetricTensor n) where
  inner A B := tensorPairing A.val B.val
  norm_sq_eq_re_inner A := A.tensorPairing_self.symm
  conj_inner_symm A B := by simp [tensorPairing, mul_comm]
  add_left A B C := by
    simp [tensorPairing, add_mul, Finset.sum_add_distrib]
  smul_left A B c := by
    simp [tensorPairing, mul_assoc, Finset.mul_sum]

/-- The Hilbert pairing is exactly the manuscript's tensor contraction
(`app:ch_background:defn:bg-geometry`). -/
theorem inner_eq_tensorPairing {n : ℕ} (A B : SymmetricTensor n) :
    inner ℝ A B = tensorPairing A.val B.val := rfl

end JanetCartan.StressFrame
