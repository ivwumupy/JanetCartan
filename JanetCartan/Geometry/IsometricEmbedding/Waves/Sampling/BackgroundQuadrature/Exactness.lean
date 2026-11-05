module

public import JanetCartan.Analysis.Fourier.LatticeQuadrature
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature.Taylor
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Banach-valued polynomial exactness

Extension of scalar lattice exactness to the multilinear Taylor terms appearing
in `app:ch_waves:eq:background-quadrature`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.Sampling.BackgroundQuadrature
open LatticeQuadrature

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Integrability of scalar polynomial moments of the actual convolved window
in `app:ch_waves:thm:sampling`. -/
theorem integrable_polynomial_productWindow {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : Continuous κ) (q : ℕ) {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) :
    Integrable (fun x : Fin n → ℝ ↦ productWindow (convolvedBoxWindow κ q) x *
      MvPolynomial.eval x p) := by
  classical
  have heval (x : Fin n → ℝ) :
      productWindow (convolvedBoxWindow κ q) x * MvPolynomial.eval x p =
        ∑ d ∈ p.support, p.coeff d * ∏ i, x i ^ d i * convolvedBoxWindow κ q (x i) := by
    simp only [productWindow, MvPolynomial.eval_eq', Finset.mul_sum,
      Finset.prod_mul_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  simp_rw [heval]
  exact integrable_finsetSum _ fun d _ ↦
    (integrable_monomial_productWindow hc hs q d).const_mul _

/-- A multilinear diagonal expands in coordinate monomials. This algebraic
identity supplies Banach-valued polynomial cancellation in
`app:ch_waves:eq:background-quadrature`. -/
theorem multilinear_diagonal_eq_sum {k n : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ Fin n → ℝ) V)
    (x : Fin n → ℝ) :
    L (fun _ ↦ x) = ∑ j : Fin k → Fin n,
      (∏ i, x (j i)) • L (fun i ↦ Pi.single (j i) 1) := by
  classical
  have hx : x = ∑ j : Fin n, x j • Pi.single j (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  rw [L.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact L.map_smul_univ _ _

/-- Coordinate product monomials have degree at most their number of factors,
as needed for `app:ch_waves:eq:background-quadrature`. -/
theorem coordinateProduct_degree_le {k n : ℕ} (j : Fin k → Fin n) :
    (∏ i, (MvPolynomial.X (j i) : MvPolynomial (Fin n) ℝ)).totalDegree ≤ k := by
  simpa using MvPolynomial.totalDegree_finsetProd Finset.univ
    (fun i ↦ (MvPolynomial.X (j i) : MvPolynomial (Fin n) ℝ))

/-- Integrability of each Banach-valued Taylor term in
`app:ch_waves:eq:background-quadrature`. -/
theorem integrable_multilinear_productWindow {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : Continuous κ) (q : ℕ) {k n : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ Fin n → ℝ) V) :
    Integrable (fun x : Fin n → ℝ ↦
      productWindow (convolvedBoxWindow κ q) x • L (fun _ ↦ x)) := by
  classical
  simp_rw [multilinear_diagonal_eq_sum, Finset.smul_sum, smul_smul]
  apply integrable_finsetSum
  intro j _
  simpa using (integrable_polynomial_productWindow hc hs q
    (∏ i, (MvPolynomial.X (j i) : MvPolynomial (Fin n) ℝ))).smul_const
      (L (fun i ↦ Pi.single (j i) 1))

/-- Exact translated quadrature for every Banach-valued multilinear diagonal of
degree below `q`. This proves the cancellation used in
`app:ch_waves:eq:background-quadrature`, without assuming vector exactness. -/
theorem hasSum_multilinear_productWindow [CompleteSpace V] {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) {q k n : ℕ} (hk : k < q)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ Fin n → ℝ) V)
    (u : Fin n → ℝ) :
    HasSum (fun m : Fin n → ℤ ↦
      productWindow (convolvedBoxWindow κ q) (fun i ↦ u i + m i) •
        L (fun _ i ↦ u i + m i))
      (∫ x : Fin n → ℝ, productWindow (convolvedBoxWindow κ q) x • L (fun _ ↦ x)) := by
  classical
  let P (j : Fin k → Fin n) : MvPolynomial (Fin n) ℝ := ∏ i, MvPolynomial.X (j i)
  have hi (j) := (integrable_polynomial_productWindow hc hs.continuous q (P j)).smul_const
    (L (fun i ↦ Pi.single (j i) 1))
  have he (x : Fin n → ℝ) :
      productWindow (convolvedBoxWindow κ q) x • L (fun _ ↦ x) =
        ∑ j : Fin k → Fin n,
          (productWindow (convolvedBoxWindow κ q) x * MvPolynomial.eval x (P j)) •
            L (fun i ↦ Pi.single (j i) 1) := by
    simp [multilinear_diagonal_eq_sum, Finset.smul_sum, smul_smul, P]
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ ↦ hi j)]
  apply hasSum_sum
  intro j _
  rw [integral_smul_const]
  exact (hasSum_polynomial_productWindow hc hs (P j)
    ((coordinateProduct_degree_le j).trans_lt hk) u).smul_const _

/-- Dilation preserves the homogeneity of each Taylor term in
`app:ch_waves:eq:background-quadrature`. -/
theorem carrierTaylor_dilation {n : ℕ} (f : (Fin n → ℝ) → V) (p : ℕ)
    (x y : Fin n → ℝ) (h : ℝ) :
    carrierTaylor f p x (h • y) =
      ∑ k ∈ Finset.range p, ((k.factorial : ℝ)⁻¹ * h ^ k) •
        iteratedFDeriv ℝ k f x (fun _ ↦ y) := by
  unfold carrierTaylor
  apply Finset.sum_congr rfl
  intro k _
  rw [(iteratedFDeriv ℝ k f x).map_smul_univ]
  simp [smul_smul]

/-- Integrability of the complete rescaled Taylor polynomial from
`app:ch_waves:eq:background-quadrature`. -/
theorem integrable_carrierTaylor_productWindow {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : Continuous κ) {n : ℕ}
    (f : (Fin n → ℝ) → V) (p : ℕ) (x : Fin n → ℝ) (h : ℝ) :
    Integrable (fun y : Fin n → ℝ ↦ productWindow (convolvedBoxWindow κ p) y •
      carrierTaylor f p x (h • y)) := by
  simp_rw [carrierTaylor_dilation, Finset.smul_sum, smul_comm
    (productWindow (convolvedBoxWindow κ p) _) ]
  exact integrable_finsetSum _ fun k _ ↦
    (integrable_multilinear_productWindow hc hs p (iteratedFDeriv ℝ k f x)).smul _

/-- Exact cancellation of the entire Banach-valued Taylor polynomial in the
proof of `app:ch_waves:eq:background-quadrature`, at every mesh and shift. -/
theorem hasSum_carrierTaylor_productWindow [CompleteSpace V] {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) {n : ℕ}
    (f : (Fin n → ℝ) → V) (p : ℕ) (x : Fin n → ℝ) (h : ℝ) (u : Fin n → ℝ) :
    HasSum (fun m : Fin n → ℤ ↦
      productWindow (convolvedBoxWindow κ p) (fun i ↦ u i + m i) •
        carrierTaylor f p x (h • (fun i ↦ u i + m i)))
      (∫ y : Fin n → ℝ, productWindow (convolvedBoxWindow κ p) y •
        carrierTaylor f p x (h • y)) := by
  simp_rw [carrierTaylor_dilation, Finset.smul_sum, smul_comm
    (productWindow (convolvedBoxWindow κ p) _)]
  rw [integral_finsetSum]
  · simp_rw [integral_smul]
    exact hasSum_sum (fun k hk ↦
      (hasSum_multilinear_productWindow hc hs (Finset.mem_range.mp hk)
        (iteratedFDeriv ℝ k f x) u).const_smul _)
  · intro k _
    exact (integrable_multilinear_productWindow hc hs.continuous p
      (iteratedFDeriv ℝ k f x)).smul _

end JanetCartan.Sampling.BackgroundQuadrature
