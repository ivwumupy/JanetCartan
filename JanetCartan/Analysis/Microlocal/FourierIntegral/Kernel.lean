module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Graph kernels and the weighted reverse graph

The phase is in physical covectors, with the Euclidean normalization `(2π)⁻ⁿ`
from `app:ch_regular_base:eq:actual-normal-kernel`. Thus integer torus frequencies
are `2π k`, consistently with `Analysis.Fourier.Periodic`.

These are actual iterated Bochner integral formulas. They directly describe
frequency-regularized graph operators. Interpreting them as the unregularized
oscillatory operators for nonintegrable symbols requires a separate limiting
construction, which is not asserted here. No symbol estimates are claimed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral

/-- Matrix amplitudes on physical output, source, and physical covector
(`app:ch_regular_base:thm:actual-calculus`, item 2). -/
abbrev FullAmplitude (n r : ℕ) :=
  Euclidean n → Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ

/-- The unit-modulus graph oscillation of `app:ch_regular_base:thm:actual-calculus`. -/
def graphOscillation {n : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (x y η : Euclidean n) : ℂ :=
  Complex.exp (Complex.I * ((S x η - inner ℝ y η : ℝ) : ℂ))

/-- The actual normalized, iterated kernel integral of a full graph amplitude.
Frequency cutoffs, when needed for absolute integrability, belong to `A`.
Source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def graphOperator {n r : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (v : Euclidean n → Fin r → ℂ)
    (x : Euclidean n) : Fin r → ℂ :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    ∫ η, ∫ y, graphOscillation S x y η • (A x y η).mulVec (v y)

/-- Exact right multiplication by a scalar source cutoff, before any Taylor
reduction (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
theorem graphOperator_source_mul {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (b : Euclidean n → ℂ) (v : Euclidean n → Fin r → ℂ) :
    graphOperator S A (fun y ↦ b y • v y) =
      graphOperator S (fun x y η ↦ b y • A x y η) v := by
  funext x
  simp only [graphOperator, Matrix.mulVec_smul, Matrix.smul_mulVec]

/-- Exact left multiplication by a scalar physical cutoff
(`app:ch_regular_base:eq:actual-global-cutoff`). -/
theorem graphOperator_target_mul {n r : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (b : Euclidean n → ℂ) (v : Euclidean n → Fin r → ℂ) (x : Euclidean n) :
    graphOperator S (fun x y η ↦ b x • A x y η) v x =
      b x • graphOperator S A v x := by
  simp only [graphOperator, Matrix.smul_mulVec, smul_comm (graphOscillation S _ _ _),
    integral_smul, smul_comm _ (b x)]

/-- The reverse-graph matrix weight `j_S U⁻¹`
(`app:ch_regular_base:eq:actual-matrix-inverse`). -/
def reverseWeight {r : ℕ} (j : ℝ) (U : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ := (j : ℂ) • U⁻¹

/-- The forward amplitude whose adjoint has matrix weight `j_S U⁻¹`
(`app:ch_regular_base:eq:actual-matrix-inverse`). -/
def weightedForwardAmplitude {r : ℕ} (j : ℝ) (U : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ := (reverseWeight j U).conjTranspose

/-- Taking the literal matrix adjoint recovers the reverse weight
(`app:ch_regular_base:eq:actual-matrix-inverse`). -/
theorem weightedForwardAmplitude_conjTranspose {r : ℕ} (j : ℝ)
    (U : Matrix (Fin r) (Fin r) ℂ) :
    (weightedForwardAmplitude j U).conjTranspose = reverseWeight j U := by
  simp [weightedForwardAmplitude]

/-- The weighted diagonal principal amplitude is the identity under the stated
Jacobian and matrix inverse gaps. This is only the pointwise matrix cancellation
in `app:ch_regular_base:thm:actual-calculus`, Step 4, not an operator inverse theorem. -/
theorem weighted_principal_amplitude {r : ℕ} (j : ℝ) (hj : j ≠ 0)
    (U : Matrix (Fin r) (Fin r) ℂ) (hU : IsUnit U.det) :
    (j : ℂ)⁻¹ • (U * reverseWeight j U) = 1 := by
  have hj' : (j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hj
  simp only [reverseWeight, Matrix.mul_smul, Matrix.mul_nonsing_inv U hU,
    smul_smul, inv_mul_cancel₀ hj', one_smul]

/-- The mixed phase matrix `S_{xη}` in
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
def mixedPhaseMatrix {n : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (x η : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ partialDeriv (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i) η j

/-- The positive Jacobian density `|det S_{xη}|` in
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
def phaseJacobian {n : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (x η : Euclidean n) : ℝ := |(mixedPhaseMatrix S x η).det|

/-- The source- and target-cut weighted reverse graph of
`app:ch_regular_base:eq:actual-matrix-inverse`, as an iterated integral. -/
def weightedReverseGraph {n r : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (f : Euclidean n → Fin r → ℂ)
    (y : Euclidean n) : Fin r → ℂ :=
  (χs y : ℂ) • (((2 * Real.pi) ^ n : ℂ)⁻¹ •
    ∫ η, ∫ x, (star (graphOscillation S x y η) * (χg η : ℂ)) •
      (reverseWeight (phaseJacobian S x η) (U x η)).mulVec ((χt x : ℂ) • f x))

end JanetCartan.FourierIntegral
