module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Amplitude

/-!
# Literal weights and cutoffs in the reverse graph

The matrix weight in `app:ch_regular_base:eq:actual-matrix-inverse` is retained
as a full two-position amplitude for the derivative calculation of
`app:ch_response:eq:direct-envelope-profile`. These identities are exact integral
identities; no derivative identity for a graph operator is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory JanetCartan.FourierIntegral
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.ReverseDerivative

variable {n r : ℕ}

/-- The full literal reverse amplitude, including `j_S U⁻¹` and every cutoff
from `app:ch_regular_base:eq:actual-matrix-inverse`. -/
def literalAmplitude (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) : FullAmplitude n r :=
  fun y x η ↦ ((χs y : ℂ) * (χg η : ℂ) * (χt x : ℂ)) •
    reverseWeight (phaseJacobian S x η) (U x η)

/-- The selected shifted amplitude in
`app:ch_response:eq:direct-envelope-profile`. Both physical positions, the
selector, the Jacobian, the matrix inverse, and the literal cutoffs are present. -/
def selectedWeightedAmplitude (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (q : Euclidean n → ℂ) : FullAmplitude n r :=
  fun y x δ ↦ q δ • literalAmplitude S U χs χt χg y x (ρ • ζ + δ)

/-- Full-amplitude reverse graph integral with the paper's physical-covector
normalization (`app:ch_regular_base:eq:actual-matrix-inverse`). -/
def reverseGraph (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (f : Euclidean n → Fin r → ℂ) (y : Euclidean n) : Fin r → ℂ :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    ∫ η, ∫ x, star (graphOscillation S x y η) • (A y x η).mulVec (f x)

/-- The full-amplitude notation is the existing literal weighted graph,
including its normalization (`app:ch_regular_base:eq:actual-matrix-inverse`). -/
theorem reverseGraph_literalAmplitude
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (f : Euclidean n → Fin r → ℂ) (y : Euclidean n) :
    reverseGraph S (literalAmplitude S U χs χt χg) f y =
      weightedReverseGraph S U χs χt χg f y := by
  simp only [reverseGraph, literalAmplitude, weightedReverseGraph,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  simp only [mul_assoc, mul_left_comm, mul_comm, ← smul_smul, integral_smul]
  exact smul_comm _ _ _

/-- Exact reverse demodulation, before changing frequency variables, for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem demodulated_reverse_oscillation
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (x y δ : Euclidean n)
    (hc : S x (ρ • ζ) = ρ * φ x) :
    carrier (-ρ) (fun z ↦ inner ℝ z ζ) y *
      star (graphOscillation S x y (ρ • ζ + δ)) * carrier ρ φ x =
      oscillation S ζ ρ y x δ := by
  simp only [carrier, graphOscillation, Complex.star_def, ← Complex.exp_conj,
    map_mul, Complex.conj_I, Complex.conj_ofReal, phaseIncrement, oscillation,
    inner_add_right, inner_smul_right, ← Complex.exp_add, hc]
  congr 1
  push_cast
  ring

end JanetCartan.ResponseTransfer.ReverseDerivative
