module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel

import Mathlib.Tactic.Ring

/-!
# Exact carrier conventions and the frequency split

Shared definitions for the two graph estimates in
`app:ch_response:thm:response-literal-transfer`. Covectors here are physical
covectors, as in `FourierIntegral.graphOperator`; integer unit-torus frequencies
must therefore enter as `2π k`. No support restriction or frequency projection
is applied to the input envelope by these definitions.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer

open FourierIntegral

/-- The physical carrier in `app:ch_response:eq:fixed-factor-transfer`. -/
def carrier {n : ℕ} (ρ : ℝ) (φ : Euclidean n → ℝ) (x : Euclidean n) : ℂ :=
  Complex.exp (Complex.I * ((ρ * φ x : ℝ) : ℂ))

/-- The exact phase increment from the derivative-transfer argument in
`app:ch_response:thm:response-literal-transfer`. -/
def phaseIncrement {n : ℕ} (S : Euclidean n → Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (x δ : Euclidean n) : ℝ :=
  S x (ρ • ζ + δ) - S x (ρ • ζ)

/-- Near-carrier selection of the full amplitude, including both physical
positions. In applications `q δ` is supported in `|δ| ≤ c ρ` and is one on
a smaller neighborhood (`app:ch_response:thm:response-literal-transfer`). -/
def selectedAmplitude {n r : ℕ} (A : FullAmplitude n r)
    (ζ : Euclidean n) (ρ : ℝ) (q : Euclidean n → ℂ) : FullAmplitude n r :=
  fun x y η ↦ q (η - ρ • ζ) • A x y η

/-- The complete complementary amplitude; the original physical cutoffs remain
in `A` (`app:ch_response:thm:response-literal-transfer`). -/
def complementaryAmplitude {n r : ℕ} (A : FullAmplitude n r)
    (ζ : Euclidean n) (ρ : ℝ) (q : Euclidean n → ℂ) : FullAmplitude n r :=
  fun x y η ↦ (1 - q (η - ρ • ζ)) • A x y η

/-- The split is an exact identity for the full amplitude, including shoulders
(`app:ch_response:thm:response-literal-transfer`). Passing this identity through
an oscillatory integral requires the actual operator construction. -/
theorem selected_add_complementary {n r : ℕ} (A : FullAmplitude n r)
    (ζ : Euclidean n) (ρ : ℝ) (q : Euclidean n → ℂ) :
    selectedAmplitude A ζ ρ q + complementaryAmplitude A ζ ρ q = A := by
  funext x y η
  change q _ • A x y η + (1 - q _) • A x y η = A x y η
  rw [← add_smul, add_sub_cancel, one_smul]

/-- Multiplication by the opposite carrier removes the carrier exactly
(`app:ch_response:eq:response-two-envelopes`). -/
theorem carrier_neg_mul {n : ℕ} (ρ : ℝ) (φ : Euclidean n → ℝ) (x : Euclidean n) :
    carrier (-ρ) φ x * carrier ρ φ x = 1 := by
  simp only [carrier, neg_mul, Complex.ofReal_neg, mul_neg, ← Complex.exp_add,
    neg_add_cancel, Complex.exp_zero]

/-- Exact forward demodulation at `η = ρ ζ + δ`
(`app:ch_response:thm:response-literal-transfer`). The central phase identity
is an explicit input supplied by homogeneity and the compatible phase theorem. -/
theorem demodulated_graphOscillation {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (x y δ : Euclidean n)
    (hcentral : S x (ρ • ζ) = ρ * φ x) :
    carrier (-ρ) φ x * graphOscillation S x y (ρ • ζ + δ) *
        carrier ρ (fun z ↦ inner ℝ z ζ) y =
      Complex.exp (Complex.I * ((phaseIncrement S ζ ρ x δ - inner ℝ y δ : ℝ) : ℂ)) := by
  simp only [carrier, graphOscillation, phaseIncrement, hcentral,
    inner_add_right, inner_smul_right, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end JanetCartan.ResponseTransfer
