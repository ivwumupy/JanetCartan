module

public import JanetCartan.Analysis.Fourier.LatticeQuadrature.FourierZeros
public import JanetCartan.Analysis.Fourier.LatticeQuadrature.Poisson
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Exact polynomial quadrature on translated product lattices

Polynomial exactness for the convolved windows in `app:ch_waves:thm:sampling`
of paper.tex. Fourier zeros, Poisson summation, and finite monomial expansion
discharge all cancellation and convergence requirements.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform ContDiff

namespace JanetCartan.LatticeQuadrature

/-- Exact translated lattice quadrature for tensor monomials whose individual
degrees are below `q`, including convergence (`app:ch_waves:thm:sampling`). -/
theorem hasSum_monomial_productWindow {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) {q n : ℕ}
    (d : Fin n → ℕ) (hd : ∀ i, d i < q) (u : Fin n → ℝ) :
    HasSum (fun m : Fin n → ℤ ↦
      ∏ i, (u i + m i) ^ d i * convolvedBoxWindow κ q (u i + m i))
      (∫ x : Fin n → ℝ, ∏ i, x i ^ d i * convolvedBoxWindow κ q (x i)) := by
  let f (i : Fin n) (x : ℝ) : ℂ := (x : ℂ) ^ d i * (convolvedBoxWindow κ q x : ℂ)
  have hfc (i) : HasCompactSupport (f i) :=
    ((hasCompactSupport_convolvedBoxWindow hc q).comp_left Complex.ofReal_zero).mul_left
  have hfs (i) : ContDiff ℝ ∞ (f i) := by
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.pow _
    · exact Complex.ofRealCLM.contDiff.comp (contDiff_convolvedBoxWindow hc hs q)
  have hsum : Summable (fun m : Fin n → ℤ ↦ ∏ i, f i (u i + m i)) :=
    (hasSum_fin_prod (fun i ↦
      (summable_schwartz_translate ((hfc i).toSchwartzMap (hfs i)) (u i)).hasSum)).summable
  have heq := quadrature_fin_prod_of_fourier_zero f hfc hfs
    (fun i _ hk ↦ fourier_monomial_convolvedBoxWindow_int hc hs (hd i) hk) u
  apply Complex.hasSum_ofReal.mp
  have hsum' := hsum.hasSum
  rw [heq] at hsum'
  convert hsum' using 1 <;>
    simp only [f, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_prod,
      integral_complex_ofReal]

/-- Polynomial moments of the product window are integrable
(`app:ch_waves:thm:sampling`). -/
theorem integrable_monomial_productWindow {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : Continuous κ) (q : ℕ) {n : ℕ}
    (d : Fin n → ℕ) :
    Integrable (fun x : Fin n → ℝ ↦ ∏ i, x i ^ d i * convolvedBoxWindow κ q (x i)) := by
  change Integrable _ (Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ)))
  apply Integrable.fintype_prod (f := fun i (x : ℝ) ↦ x ^ d i * convolvedBoxWindow κ q x)
  intro i
  have hw : Continuous (convolvedBoxWindow κ q) := by
    induction q with
    | zero => exact hs
    | succ q ih =>
      exact (hasCompactSupport_convolvedBoxWindow hc q).continuous_convolution_left
        (ContinuousLinearMap.mul ℝ ℝ) ih integrable_unitBox.locallyIntegrable
  exact ((continuous_id.pow _).mul hw).integrable_of_hasCompactSupport
    (hasCompactSupport_convolvedBoxWindow hc q).mul_left

/-- Exactness for every polynomial of total degree below `q`, with actual
convergence on the full integer lattice (`app:ch_waves:thm:sampling`).
No Fourier vanishing premise is required. -/
theorem hasSum_polynomial_productWindow {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) {q n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree < q) (u : Fin n → ℝ) :
    HasSum (fun m : Fin n → ℤ ↦
      productWindow (convolvedBoxWindow κ q) (fun i ↦ u i + m i) *
        MvPolynomial.eval (fun i ↦ u i + m i) p)
      (∫ x : Fin n → ℝ, productWindow (convolvedBoxWindow κ q) x *
        MvPolynomial.eval x p) := by
  classical
  let F (d : Fin n →₀ ℕ) (x : Fin n → ℝ) :=
    p.coeff d * ∏ i, x i ^ d i * convolvedBoxWindow κ q (x i)
  have hF (d) : Integrable (F d) :=
    (integrable_monomial_productWindow hc hs.continuous q d).const_mul _
  have heval (x : Fin n → ℝ) :
      productWindow (convolvedBoxWindow κ q) x * MvPolynomial.eval x p =
        ∑ d ∈ p.support, F d x := by
    simp only [productWindow, MvPolynomial.eval_eq', Finset.mul_sum, F,
      Finset.prod_mul_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hsum := hasSum_sum (s := p.support) (fun d hd ↦
    (hasSum_monomial_productWindow hc hs d (fun i ↦
      lt_of_le_of_lt ((MvPolynomial.le_degreeOf_of_mem_support i hd).trans
        (p.degreeOf_le_totalDegree i)) hp) u).mul_left (p.coeff d))
  simp_rw [heval]
  rw [integral_finsetSum _ (fun d _ ↦ hF d)]
  simpa only [F, integral_const_mul] using hsum

/-- The background quadrature identity of `app:ch_waves:thm:sampling`.
Specializing to `n = 3` gives the manuscript identity for every translation. -/
theorem quadrature_polynomial_productWindow {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) {q n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree < q) (u : Fin n → ℝ) :
    (∑' m : Fin n → ℤ,
      productWindow (convolvedBoxWindow κ q) (fun i ↦ u i + m i) *
        MvPolynomial.eval (fun i ↦ u i + m i) p) =
      ∫ x : Fin n → ℝ, productWindow (convolvedBoxWindow κ q) x *
        MvPolynomial.eval x p :=
  (hasSum_polynomial_productWindow hc hs p hp u).tsum_eq

end JanetCartan.LatticeQuadrature
