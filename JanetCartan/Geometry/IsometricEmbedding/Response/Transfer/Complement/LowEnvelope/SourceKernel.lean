module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import JanetCartan.Analysis.Microlocal.Localization.Vector
public import JanetCartan.Analysis.Microlocal.Localization.FourierPhase

/-!
# Source kernels for the low envelope

The source integration in `app:ch_response:thm:response-literal-transfer`.
All covectors are physical Euclidean covectors and all integrals use Lebesgue
measure. The full amplitude retains both physical positions. The estimates in
this file concern the source integral before frequency integration; they do not
assert the final Sobolev estimate or its regularization limit.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral JanetCartan.Localization

/-- Full forward phase after Fourier inversion of the envelope, for
`app:ch_response:thm:response-literal-transfer`. The source carrier is included;
the output carrier, being constant in the source variable, can be removed later. -/
def forwardSourcePhase {n : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (x η θ y : Euclidean n) : ℝ :=
  S x η - inner ℝ (η - ρ • ζ - θ) y

/-- Full reverse phase, retaining the exact inverse-chart source phase in
`app:ch_response:thm:response-literal-transfer`. -/
def reverseSourcePhase {n : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (φ : Euclidean n → ℝ) (ρ : ℝ) (y η θ x : Euclidean n) : ℝ :=
  inner ℝ y η - S x η + ρ * φ x + inner ℝ x θ

/-- The matrix-valued source kernel used inside the low-envelope Fourier
integral in `app:ch_response:thm:response-literal-transfer`. No output or
frequency projection is part of this definition. -/
def sourceKernel {n r : ℕ} (ψ : Euclidean n → ℝ) (A : FullAmplitude n r)
    (x η : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  ∫ y, phaseOscillation ψ y • A x y η

/-- Literal reverse amplitude, with all three cutoffs and the matrix order
`j_S U⁻¹` from `app:ch_regular_base:eq:actual-matrix-inverse`. -/
def reverseFullAmplitude {n r : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) : FullAmplitude n r :=
  fun y x η ↦ ((χs y : ℂ) * (χg η : ℂ) * (χt x : ℂ)) •
    reverseWeight (phaseJacobian S x η) (U x η)

/-- The source oscillation is exactly the forward graph oscillation multiplied
by the input carrier and the physical inverse-Fourier oscillation
(`app:ch_response:thm:response-literal-transfer`). -/
theorem phaseOscillation_forwardSourcePhase {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (x η θ y : Euclidean n) :
    phaseOscillation (forwardSourcePhase S ζ ρ x η θ) y =
      graphOscillation S x y η * carrier ρ (fun z ↦ inner ℝ z ζ) y *
        phaseOscillation (fun z ↦ inner ℝ z θ) y := by
  simp only [phaseOscillation, forwardSourcePhase, graphOscillation, carrier,
    inner_sub_left, real_inner_smul_left, real_inner_comm η y, real_inner_comm ζ y,
    real_inner_comm θ y, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The source oscillation in the reverse direction is the literal conjugated
forward graph phase, with the nonlinear input carrier and Fourier oscillation
(`app:ch_response:thm:response-literal-transfer`). -/
theorem phaseOscillation_reverseSourcePhase {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ) (ρ : ℝ)
    (y η θ x : Euclidean n) :
    phaseOscillation (reverseSourcePhase S φ ρ y η θ) x =
      star (graphOscillation S x y η) * carrier ρ φ x *
        phaseOscillation (fun z ↦ inner ℝ z θ) x := by
  simp only [phaseOscillation, reverseSourcePhase, graphOscillation, carrier,
    Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Repeated source-variable integration by parts for the full matrix amplitude,
consumed by the low-envelope estimate in
`app:ch_response:thm:response-literal-transfer`. The assumptions are smoothness,
compact source support, the full source-gradient gap, and normalized phase and
amplitude derivative grades. The oscillatory kernel bound is derived, not an
input. The amplitude size may include a fixed `L^b`, with `b` fixed before `q`.
The constant depends on the profiles and `q`, and not on `ρ`, `η`, or `L`. -/
theorem norm_sourceKernel_le {n r : ℕ} {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) (ψ : Euclidean n → ℝ) (A : FullAmplitude n r)
    (x η : Euclidean n) (q : ℕ)
    (hψ : ContDiffOn ℝ ∞ ψ Ω)
    (ha : ContDiffOn ℝ ∞ (fun y ↦ A x y η) Ω)
    (hs : tsupport (fun y ↦ A x y η) ⊆ Ω)
    (hc : HasCompactSupport (fun y ↦ A x y η))
    {c G a L ρ : ℝ} (hcpos : 0 < c) (ha0 : 0 ≤ a) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hgap : ∀ y ∈ Ω, c * (ρ + ‖η‖) ≤ ‖fderiv ℝ ψ y‖)
    (hupper : ∀ y ∈ Ω, ‖fderiv ℝ ψ y‖ ≤ G * (ρ + ‖η‖))
    {P C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hp : ∀ y ∈ tsupport (fun y ↦ A x y η), ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) ψ y‖ ≤ P j * (ρ + ‖η‖) * L ^ j)
    (ha_bound : ∀ y ∈ tsupport (fun y ↦ A x y η), ∀ j,
      ‖iteratedFDeriv ℝ j (fun z ↦ A x z η) y‖ ≤ C j * (a * L ^ j)) :
    ‖sourceKernel ψ A x η‖ ≤
      (transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
        (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
          (c ^ 2) G P) C q 0 * (a * (L / (ρ + ‖η‖)) ^ q)) *
        volume.real (tsupport (fun y ↦ A x y η)) := by
  apply norm_vector_oscillatory_integral_le hΩ
    (EuclideanSpace.basisFun (Fin n) ℝ) ψ (fun y ↦ A x y η) q
    hψ ha hs hc (sq_pos_of_pos hcpos) ha0 hL
    (add_pos_of_pos_of_nonneg hρ (norm_nonneg η)) ?_ hupper hC hp ha_bound
  intro y hy
  rw [phaseGradientSquare_orthonormalBasis]
  simpa only [mul_pow] using pow_le_pow_left₀
    (mul_nonneg hcpos.le (add_nonneg hρ.le (norm_nonneg η))) (hgap y hy) 2

/-- The packaged reverse amplitude is exactly the literal weighted reverse
graph, including its physical `(2π)⁻ⁿ` normalization and cutoff order
(`app:ch_response:thm:response-literal-transfer`). -/
theorem weightedReverseGraph_eq_integral_reverseFullAmplitude {n r : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (f : Euclidean n → Fin r → ℂ)
    (y : Euclidean n) :
    weightedReverseGraph S U χs χt χg f y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
        star (graphOscillation S x y η) •
          (reverseFullAmplitude S U χs χt χg y x η).mulVec (f x) := by
  simp only [weightedReverseGraph, reverseFullAmplitude, Matrix.smul_mulVec,
    Matrix.mulVec_smul, ← smul_assoc]
  simp only [smul_eq_mul]
  simp_rw [show ∀ η x, star (graphOscillation S x y η) *
      ((χs y : ℂ) * (χg η : ℂ) * (χt x : ℂ)) =
      (χs y : ℂ) * (star (graphOscillation S x y η) * (χg η : ℂ) * (χt x : ℂ))
      from fun η x ↦ by ring]
  simp only [mul_smul, integral_smul]
  exact smul_comm _ _ _

end JanetCartan.ResponseTransfer.LowEnvelope
