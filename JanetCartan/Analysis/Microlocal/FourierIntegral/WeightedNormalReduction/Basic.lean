module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.CoordinateInverse.MatrixReduction
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.PairedCoordinates
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.PrimitiveDiagonal
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Bounds

/-!
# The literal diagonal and remainder symbols

The two symbols in `app:ch_regular_base:eq:actual-pdo-remainder`, expressed in
the existing paired-position coordinates. The input `c` is already in cycle
frequency. In the weighted normal application it is the full zero-extended
`cycleCrossNormalAmplitude`; these definitions perform no further frequency
rescaling and retain the fixed source cutoff.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.WeightedNormalReduction

open AmplitudeBound NormalComparison Pseudodifferential CoordinateInverse

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean (2 * n)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The principal term with its source multiplier in
`app:ch_regular_base:eq:actual-pdo-remainder`. -/
def diagonalSymbol (c : FullAmplitude n r) (β : E → ℝ) : E → P → Mat :=
  pairedNormalAmplitude (fun q ↦ diagonalAmplitude c β q.1 q.2.1 q.2.2)

/-- The literal matrix Taylor/divergence remainder in
`app:ch_regular_base:eq:actual-pdo-remainder`, including the cycle-frequency
factor `(2πi)⁻¹` from `matrixDiagonalRemainder`. -/
def remainderSymbol (basis : OrthonormalBasis (Fin n) ℝ E)
    (c : FullAmplitude n r) (β : E → ℝ) : E → P → Mat :=
  pairedNormalAmplitude (fun q ↦ matrixDiagonalRemainder basis c β q.1 q.2.1 q.2.2)

/-- Recover both physical positions of the principal term in
`app:ch_regular_base:eq:actual-pdo-remainder`. -/
@[simp] theorem diagonalSymbol_pairedPosition (c : FullAmplitude n r) (β : E → ℝ)
    (x y ξ : E) : diagonalSymbol c β ξ (pairedPosition x y) = β y • c x x ξ := by
  simp [diagonalSymbol, diagonalAmplitude]

/-- Recover the same entrywise Taylor/divergence amplitude used by the
coordinate-inverse ledger (`app:ch_regular_base:eq:actual-right-inverse`). -/
@[simp] theorem remainderSymbol_pairedPosition (basis : OrthonormalBasis (Fin n) ℝ E)
    (c : FullAmplitude n r) (β : E → ℝ) (x y ξ : E) :
    remainderSymbol basis c β ξ (pairedPosition x y) =
      matrixDiagonalRemainder basis c β x y ξ := by
  simp [remainderSymbol]

/-- Exact matrix diagonal reduction with convergence discharged from finite
primitive Frobenius jets. There is no assumed integral identity or convergence
of the Taylor coefficient. This compact-test deduction is consumed by the
bounded reduction; production of the symbol jets from the original phase,
mask and matrix remains a separate obligation.
Source: `app:ch_regular_base:eq:actual-pdo-remainder`. -/
theorem matrixFullAmplitudeOperator_eq_diagonal_add_remainder_of_symbolBounds
    (basis : OrthonormalBasis (Fin n) ℝ E) (c : FullAmplitude n r) (β : E → ℝ)
    (hc : ContDiff ℝ ∞ (fun q : NormalVariables n ↦ c q.1 q.2.1 q.2.2))
    (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)
    (hβc : ∀ x y ξ, c x y ξ ≠ 0 → β y = 1)
    (u : E → Fin r → ℂ) (hu : ∀ j, ContDiff ℝ (n + 1) (fun y ↦ u y j))
    (hus : ∀ j, HasCompactSupport (fun y ↦ u y j))
    (M : ℕ → ℝ) (hM : ∀ k ≤ n + 3, ∀ q : NormalVariables n,
      ‖iteratedFDeriv ℝ k (fun p : NormalVariables n ↦ c p.1 p.2.1 p.2.2) q‖ ≤ M k)
    (x : E) :
    matrixFullAmplitudeOperator c u x =
      matrixFullAmplitudeOperator (diagonalAmplitude c β) u x +
        matrixFullAmplitudeOperator (matrixDiagonalRemainder basis c β) u x := by
  classical
  funext i
  simp only [matrixFullAmplitudeOperator, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : ∀ k ≤ n + 3, ∀ y ξ : E,
      ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦ c q.1 q.2.1 q.2.2 i j)
        (x, y, ξ)‖ ≤ matrixEntryBound (Fin r) (Fin r) * M k := by
    intro k hk y ξ
    exact (norm_iteratedFDeriv_matrix_entry_le _ k k le_rfl
      (hc.of_le (by simp)) _ i j).trans
        (mul_le_mul_of_nonneg_left (hM k hk _) (matrixEntryBound_nonneg ..))
  refine fullAmplitudeOperator_eq_diagonal_add_remainder_of_symbolBounds basis
    (fun x y ξ ↦ c x y ξ i j) β (fun y ↦ u y j) x 0
    ((matrixEntryEvaluation i j).contDiff.comp hc) hβ hβs ?_ ?_ (hus j)
    (fun k ↦ matrixEntryBound (Fin r) (Fin r) * M k) ?_
  · intro ξ y hne
    apply hβc x y ξ
    intro hz
    exact hne (by simp [hz])
  · simpa using hu j
  · intro k hk y ξ
    simpa using he k (by simpa using hk) y ξ

end JanetCartan.FourierIntegral.WeightedNormalReduction
