module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.Components

/-!
# The complex Frobenius fiber of the full source

The Hilbert-valued Fourier estimate in `app:ch_response:prop:response-graded`
acts on the literal complex tensor. Pull the inner product back along the
existing complex linear isometry; the matrix norm and all entries are unchanged.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.TensorFrobenius

/-- The full complex source has precisely its original Frobenius norm.
Consumer: `SourceNegative.SobolevEnvelopeBounds` for
`app:ch_response:cor:current-atoms`. -/
scoped instance complexMatrixInnerProductSpace (m n : ℕ) :
    InnerProductSpace ℂ (Matrix (Fin m) (Fin n) ℂ) where
  inner A B := inner ℂ (SingleChannel.matrixChannelEquiv m n A)
    (SingleChannel.matrixChannelEquiv m n B)
  norm_sq_eq_re_inner A := by
    rw [← (SingleChannel.matrixChannelEquiv m n).norm_map A]
    exact norm_sq_eq_re_inner _
  conj_inner_symm A B := inner_conj_symm _ _
  add_left A B C := by simp only [map_add, inner_add_left]
  smul_left A B c := by simp only [map_smul, inner_smul_left]

end JanetCartan.TensorFrobenius
