module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Complex

/-!
# Coordinate expansion of the same completed variation

The literal coefficient entries in `app:ch_response:eq:response-reconstruction-grading`.
The source coordinates are pairs (the Frobenius convention), and the phase term
retains `I * ρ`. These are the terms to which the finite multiplier bounds apply.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ResponseTransfer

variable {n N : ℕ}
local notation "E" => Euclidean n

/-- Value coefficient entry of the actual completion in
`app:ch_response:eq:response-reconstruction-grading`. -/
def reconstructionValueEntry (F : E → Euclidean N) (k : Fin N) (j : Fin n)
    (x : E) : ℂ := (reconstructionValueCoefficient F x (Pi.single j 1) k : ℂ)

/-- First-derivative coefficient entry of the actual completion in
`app:ch_response:eq:response-reconstruction-grading`. -/
def reconstructionDerivativeEntry (F : E → Euclidean N) (k : Fin N)
    (ij : Fin n × Fin n) (x : E) : ℂ :=
  (reconstructionDerivativeCoefficient F x (Pi.single ij 1) k : ℂ)

/-- Source coefficient entry, including `-1/2`, in
`app:ch_response:eq:response-full-map`. All tensor coordinates are retained. -/
def reconstructionSourceEntry (F : E → Euclidean N) (k : Fin N)
    (ij : Fin n × Fin n) (x : E) : ℂ :=
  (reconstructionSourceCoefficient F x (Pi.single ij 1) k : ℂ)

private theorem complexCoefficient_coordinate {J : Type*} [Fintype J] [DecidableEq J]
    (T : (J → ℝ) →ₗ[ℝ] Euclidean N) (z : J → ℂ) (k : Fin N) :
    complexCoefficient T z k = ∑ j, (T (Pi.single j 1) k : ℂ) * z j := by
  simp [complexCoefficient, mul_comm]

/-- The three literal coefficient sums for the displacement amplitude in
`app:ch_response:eq:response-graded-displacement`. The derivative slot contains
both the physical carrier term and the ordinary envelope derivative. -/
theorem reconstructionAmplitude_coordinate (F : E → Euclidean N)
    (ρ : ℝ) (φ χ : E → ℝ) (g : E → EuclideanSpace ℂ (Fin n))
    (a : E → Matrix (Fin n) (Fin n) ℂ) (x : E) (k : Fin N) :
    reconstructionAmplitude F ρ φ χ g a x k =
      (∑ j, reconstructionValueEntry F k j x * g x j) +
      (∑ ij : Fin n × Fin n, reconstructionDerivativeEntry F k ij x *
        (Complex.I * (ρ : ℂ) * ((partialDeriv φ x ij.1 : ℝ) : ℂ) * g x ij.2 +
          partialDeriv (fun y ↦ g y ij.2) x ij.1)) +
      ∑ ij : Fin n × Fin n,
        ((χ x : ℂ) * reconstructionSourceEntry F k ij x) * a x ij.1 ij.2 := by
  simp only [reconstructionAmplitude, PiLp.add_apply, PiLp.smul_apply,
    complexCoefficient_coordinate, waveFirstAmplitude, smul_eq_mul,
    reconstructionValueEntry, reconstructionDerivativeEntry, reconstructionSourceEntry,
    partialDeriv, Finset.mul_sum, mul_assoc]

/-- The observed displacement is exactly the scalar coefficient expansion,
with the observation cutoff outside the same completed variation, for
`app:ch_response:eq:response-graded-displacement`. -/
theorem demodulated_completedVariationComplex_coordinate (F : E → Euclidean N)
    {ρ : ℝ} {φ : E → ℝ} (χ ψ : E → ℝ)
    {g : E → EuclideanSpace ℂ (Fin n)} (a : E → Matrix (Fin n) (Fin n) ℂ)
    {x : E} (hφ : DifferentiableAt ℝ φ x) (hg : DifferentiableAt ℝ g x) (k : Fin N) :
    (waveCarrier (-ρ) φ x • ((ψ x : ℂ) •
      completedVariationComplex F (modulatedWave ρ φ g)
        (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y)) x)) k =
      (∑ j, ((ψ x : ℂ) * reconstructionValueEntry F k j x) * g x j) +
      (∑ ij : Fin n × Fin n,
        ((ψ x : ℂ) * reconstructionDerivativeEntry F k ij x) *
          partialDeriv (fun y ↦ g y ij.2) x ij.1) +
      (Complex.I * (ρ : ℂ)) *
        (∑ ij : Fin n × Fin n,
          ((ψ x : ℂ) * reconstructionDerivativeEntry F k ij x *
            ((partialDeriv φ x ij.1 : ℝ) : ℂ)) * g x ij.2) +
      ∑ ij : Fin n × Fin n,
        ((ψ x : ℂ) * ((χ x : ℂ) * reconstructionSourceEntry F k ij x)) *
          a x ij.1 ij.2 := by
  rw [demodulated_completedVariationComplex F χ ψ a hφ hg]
  simp only [PiLp.smul_apply, smul_eq_mul, reconstructionAmplitude_coordinate,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  abel

end JanetCartan.ResponseTransfer
