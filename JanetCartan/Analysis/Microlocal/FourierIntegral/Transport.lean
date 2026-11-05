module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Module

/-!
# The algebra of the two-term transport amplitude

Pointwise algebra from Step 5 of `app:ch_regular_base:thm:actual-calculus`.
The inputs are the symbol and its first two covector derivatives, the symmetric
phase Hessian, and the first spatial derivatives of the transport matrix.
Identifying these arrays with actual derivatives, solving the transport ODE,
and passing differentiation through the graph integral are separate analytic
obligations. The results here do not assert that those obligations are solved.
-/

@[expose] public noncomputable section

open scoped BigOperators
namespace JanetCartan.FourierIntegral
variable {ι R : Type*} [Fintype ι] [Ring R] [Algebra ℂ R]

/-- First covector-derivative cancellation in
`app:ch_regular_base:eq:direct-graph-identity`. -/
theorem first_symbol_cancellation (H : R) (A c1 dU : ι → R) (c : R) (h1 : ι → ℂ)
    (hc1 : ∀ j, H * c1 j = h1 j • 1 - A j * c) :
    H * (∑ j, c1 j * dU j) = ∑ j, h1 j • dU j - ∑ j, A j * c * dU j := by
  simp_rw [Finset.mul_sum, ← mul_assoc, hc1, sub_mul, smul_mul_assoc, one_mul]
  rw [Finset.sum_sub_distrib]

/-- Second covector-derivative cancellation, using symmetry of the phase
Hessian (`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem second_symbol_cancellation (H U : R) (A c1 : ι → R) (c2 : ι → ι → R) (S h2 : ι → ι → ℂ)
    (hS : ∀ j l, S j l = S l j)
    (hc2 : ∀ j l, H * c2 j l = h2 j l • 1 - A j * c1 l - A l * c1 j) :
    H * (∑ j, ∑ l, S j l • (c2 j l * U)) =
      (∑ j, ∑ l, (S j l * h2 j l) • U) -
      (2 : ℂ) • (∑ j, ∑ l, S j l • (A j * c1 l * U)) := by
  have hswap : (∑ j, ∑ l, S j l • (A l * c1 j * U)) =
      ∑ j, ∑ l, S j l • (A j * c1 l * U) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    rw [hS l j]
  simp_rw [Finset.mul_sum, mul_smul_comm, ← mul_assoc, hc2, sub_mul,
    smul_sub, smul_mul_assoc, one_mul, smul_smul, Finset.sum_sub_distrib]
  rw [hswap]
  module


/-- Leading graph amplitude `c U` (`app:ch_regular_base:eq:direct-graph-amplitudes`). -/
def leadingAmplitude (c U : R) : R := c * U

/-- The two contributions to the degree minus one graph amplitude
(`app:ch_regular_base:eq:direct-graph-amplitudes`). -/
def correctionAmplitude (c1 dU : ι → R) (c2 : ι → ι → R)
    (S : ι → ι → ℂ) (U : R) : R :=
  -Complex.I • (∑ j, c1 j * dU j) -
    (Complex.I / 2) • (∑ j, ∑ l, S j l • (c2 j l * U))

/-- The effective matrix transport coefficient; `cx` is the derivative of `c`
at fixed covector (`app:ch_regular_base:eq:actual-effective-transport`). -/
def transportCoefficient (A cx : ι → R) (B c : R) (S h2 : ι → ι → ℂ) : R :=
  (∑ j, A j * cx j) + B * c + (1 / 2 : ℂ) • (∑ j, ∑ l, (S j l * h2 j l) • 1)

/-- The chain-rule expression for the derivative of `c(x,S_x) U`
(`app:ch_regular_base:eq:direct-graph-identity`). -/
def leadingAmplitudeDerivative (c U : R) (cx c1 dU : ι → R)
    (S : ι → ι → ℂ) (j : ι) : R :=
  (cx j + ∑ l, S j l • c1 l) * U + c * dU j

/-- Expansion of the differentiated leading amplitude, with all matrix products
in their original order (`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem leadingAmplitudeDerivative_sum (A cx c1 dU : ι → R) (c U : R)
    (S : ι → ι → ℂ) :
    (∑ j, A j * leadingAmplitudeDerivative c U cx c1 dU S j) =
      (∑ j, A j * cx j) * U +
      (∑ j, ∑ l, S j l • (A j * c1 l * U)) + (∑ j, A j * c * dU j) := by
  simp only [leadingAmplitudeDerivative, mul_add, add_mul, Finset.mul_sum,
    Finset.sum_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, Finset.sum_add_distrib]

/-- Exact cancellation of orders one and zero in the two-term amplitude.
The three hypotheses are precisely the differentiated identity `H c = h I`
evaluated at the eikonal covector, not an operator conjugation hypothesis.
Source: `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem two_term_symbol_identity (H B c U : R) (A cx c1 dU : ι → R)
    (c2 : ι → ι → R) (e : ℂ) (h1 : ι → ℂ) (S h2 : ι → ι → ℂ)
    (hS : ∀ j l, S j l = S l j)
    (hc : H * c = e • 1)
    (hc1 : ∀ j, H * c1 j = h1 j • 1 - A j * c)
    (hc2 : ∀ j l, H * c2 j l = h2 j l • 1 - A j * c1 l - A l * c1 j) :
    H * (leadingAmplitude c U + correctionAmplitude c1 dU c2 S U) -
      Complex.I • ((∑ j, A j * leadingAmplitudeDerivative c U cx c1 dU S j) +
        B * leadingAmplitude c U) =
      e • U - Complex.I • ((∑ j, h1 j • dU j) +
        transportCoefficient A cx B c S h2 * U) := by
  rw [leadingAmplitudeDerivative_sum]
  simp only [leadingAmplitude, correctionAmplitude, mul_add, mul_sub, mul_smul_comm]
  rw [← mul_assoc H c U, hc, smul_mul_assoc, one_mul,
    first_symbol_cancellation H A c1 dU c h1 hc1,
    second_symbol_cancellation H U A c1 c2 S h2 hS hc2]
  simp only [transportCoefficient, add_mul, smul_mul_assoc, Finset.sum_mul,
    one_mul, mul_assoc]
  module

/-- The remaining amplitude consists exactly of derivatives and the zeroth-order
coefficient applied to `b₋₁` (`app:ch_regular_base:eq:direct-graph-identity`). -/
def transportRemainder (A db : ι → R) (B b : R) : R :=
  -Complex.I • ((∑ j, A j * db j) + B * b)

/-- The algebraic two-term transport identity after imposing the full matrix
transport equation. The input `db` represents the actual derivative of `b₋₁`;
no estimate or differentiation-under-the-integral assertion is made here.
Source: `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem two_term_transport_identity (H B c U : R) (A cx c1 dU db : ι → R)
    (c2 : ι → ι → R) (e : ℂ) (h1 : ι → ℂ) (S h2 : ι → ι → ℂ)
    (hS : ∀ j l, S j l = S l j)
    (hc : H * c = e • 1)
    (hc1 : ∀ j, H * c1 j = h1 j • 1 - A j * c)
    (hc2 : ∀ j l, H * c2 j l = h2 j l • 1 - A j * c1 l - A l * c1 j)
    (htransport : (∑ j, h1 j • dU j) + transportCoefficient A cx B c S h2 * U = 0) :
    H * (leadingAmplitude c U + correctionAmplitude c1 dU c2 S U) -
      Complex.I • ((∑ j, A j * (leadingAmplitudeDerivative c U cx c1 dU S j + db j)) +
        B * (leadingAmplitude c U + correctionAmplitude c1 dU c2 S U)) =
      e • U + transportRemainder A db B (correctionAmplitude c1 dU c2 S U) := by
  have hid := two_term_symbol_identity H B c U A cx c1 dU c2 e h1 S h2 hS hc hc1 hc2
  rw [htransport, smul_zero, sub_zero] at hid
  simp only [mul_add, Finset.sum_add_distrib, transportRemainder]
  rw [← hid]
  rw [mul_add H]
  module

end JanetCartan.FourierIntegral
