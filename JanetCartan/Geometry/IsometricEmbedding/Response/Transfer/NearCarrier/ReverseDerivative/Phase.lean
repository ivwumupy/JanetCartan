module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# The reverse near-carrier phase

Pointwise identities consumed by the source integration by parts in
`app:ch_response:eq:direct-envelope-profile`. The matrix `C` below is the supplied
inverse of the averaged mixed phase matrix `B`. Invertibility is required only
where the identity is used; no global inverse extension is asserted.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.ReverseDerivative

variable {n r : ℕ}

/-- The demodulated reverse phase, in physical covectors, from
`app:ch_response:eq:direct-envelope-profile`. -/
def oscillation (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (y x δ : Euclidean n) : ℂ :=
  Complex.exp (Complex.I * ((inner ℝ y δ - phaseIncrement S ζ ρ x δ : ℝ) : ℂ))

/-- Source derivative of the reverse oscillation
(`app:ch_regular_base:eq:actual-adjoint-trade`). -/
theorem partialDeriv_oscillation_source
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (y x δ : Euclidean n) (l : Fin n)
    (hS : DifferentiableAt ℝ (fun z ↦ phaseIncrement S ζ ρ z δ) x) :
    partialDeriv (fun z ↦ oscillation S ζ ρ y z δ) x l =
      -(oscillation S ζ ρ y x δ * Complex.I *
        ((partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l : ℝ) : ℂ)) := by
  have hd := (((Complex.ofRealCLM.hasFDerivAt.comp x
    (hS.hasFDerivAt.const_sub (inner ℝ y δ))).const_mul Complex.I).cexp).fderiv
  have hh := congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦
    L (EuclideanSpace.single l 1)) hd
  simpa [oscillation, partialDeriv, Function.comp_def, mul_assoc] using hh

/-- Output derivative of the reverse oscillation
(`app:ch_regular_base:eq:actual-adjoint-trade`). -/
theorem partialDeriv_oscillation_output
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (y x δ : Euclidean n) (j : Fin n) :
    partialDeriv (fun z ↦ oscillation S ζ ρ z x δ) y j =
      oscillation S ζ ρ y x δ * Complex.I * (δ j : ℂ) := by
  have hl : HasFDerivAt (fun z : Euclidean n ↦ inner ℝ z δ)
      (innerSL ℝ δ) y := by
    convert (innerSL ℝ δ).hasFDerivAt (x := y) using 1
    ext z
    exact (real_inner_comm z δ).symm
  have hd := (((Complex.ofRealCLM.hasFDerivAt.comp y
    (hl.sub_const (phaseIncrement S ζ ρ x δ))).const_mul Complex.I).cexp).fderiv
  have hh := congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦
    L (EuclideanSpace.single j 1)) hd
  simpa [oscillation, partialDeriv, Function.comp_def, mul_assoc,
    EuclideanSpace.inner_single_right] using hh

/-- The exact inverse-matrix phase trade used before integration by parts in
`app:ch_regular_base:eq:actual-adjoint-trade`, with `B` the averaged matrix of
`app:ch_response:eq:direct-envelope-profile`. This is derived from `C * B = 1`
and `Dₓ ΔS = B δ`, rather than assumed as an operator identity. -/
theorem oscillation_phase_trade
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (y x δ : Euclidean n) (j : Fin n)
    (B C : Matrix (Fin n) (Fin n) ℝ) (hCB : C * B = 1)
    (hS : DifferentiableAt ℝ (fun z ↦ phaseIncrement S ζ ρ z δ) x)
    (hgrad : ∀ l, partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
      B.mulVec (fun k ↦ δ k) l) :
    oscillation S ζ ρ y x δ * Complex.I * (δ j : ℂ) =
      -∑ l, (C j l : ℂ) * partialDeriv (fun z ↦ oscillation S ζ ρ y z δ) x l := by
  have hinv : ∑ l, C j l * partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
      δ j := by
    simp_rw [hgrad]
    change (C.mulVec (B.mulVec (fun k ↦ δ k))) j = δ j
    rw [Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
  rw [← hinv]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    partialDeriv_oscillation_source S ζ ρ y x δ _ hS, mul_neg,
    Finset.sum_neg_distrib, neg_neg]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The datum-derivative amplitude `(B⁻¹)ⱼₗ A` in
`app:ch_response:eq:direct-envelope-profile`. The amplitude arguments are output
`y`, source `x`, and physical frequency displacement `δ`. -/
def datumAmplitude (C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (A : FourierIntegral.FullAmplitude n r) (j l : Fin n) :
    FourierIntegral.FullAmplitude n r :=
  fun y x δ ↦ (C x δ j l : ℂ) • A y x δ

/-- The complete remainder `∂yⱼ A + Σₗ ∂xₗ((B⁻¹)ⱼₗ A)` in
`app:ch_response:eq:direct-envelope-profile`. In particular, the inverse matrix
is differentiated, and neither physical amplitude position is discarded. -/
def remainderAmplitude (C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (A : FourierIntegral.FullAmplitude n r) (j : Fin n) :
    FourierIntegral.FullAmplitude n r :=
  fun y x δ ↦ partialDeriv (fun z ↦ A z x δ) y j +
    ∑ l, partialDeriv (fun z ↦ datumAmplitude C A j l y z δ) x l

end JanetCartan.ResponseTransfer.ReverseDerivative
