module

public import JanetCartan.Analysis.Fourier.LatticeQuadrature.Window
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product-lattice summation

Finite products of one-dimensional sums are sums over the actual integer
lattice, as required by `app:ch_waves:thm:sampling` in paper.tex.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.LatticeQuadrature

/-- Tensorization of absolutely convergent scalar sums, used for the lattice
in `app:ch_waves:thm:sampling`. -/
theorem hasSum_fin_prod {𝕜 : Type*} [NormedCommRing 𝕜] [NormedSpace ℝ 𝕜]
    [FiniteDimensional ℝ 𝕜] [CompleteSpace 𝕜] {n : ℕ}
    {f : Fin n → ℤ → 𝕜} {a : Fin n → 𝕜} (hf : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun m : Fin n → ℤ ↦ ∏ i, f i (m i)) (∏ i, a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let g : (Fin n → ℤ) → 𝕜 := fun m ↦ ∏ i, f i.succ (m i)
    have ht : HasSum g (∏ i : Fin n, a i.succ) := ih (fun i ↦ hf i.succ)
    have h0 : Summable (fun m : ℤ ↦ ‖f 0 m‖) := (hf 0).summable.norm
    have htail : Summable (fun m ↦ ‖g m‖) := ht.summable.norm
    have hprod : Summable (fun m : ℤ × (Fin n → ℤ) ↦ f 0 m.1 * g m.2) :=
      summable_mul_of_summable_norm h0 htail
    have hp := (hf 0).mul ht hprod
    apply (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ℤ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ, g] using hp

/-- The product of one-dimensional windows (`app:ch_waves:thm:sampling`).
The application in the manuscript has `n = 3`. -/
def productWindow {n : ℕ} (w : ℝ → ℝ) (x : Fin n → ℝ) : ℝ := ∏ i, w (x i)

/-- Product-lattice partition of unity for every translation
(`app:ch_waves:thm:sampling`), with convergence included. -/
theorem hasSum_productWindow {κ : ℝ → ℝ} (hκ : Integrable κ)
    (hm : ∫ x, κ x = 1) {q n : ℕ} (hq : 0 < q) (u : Fin n → ℝ) :
    HasSum (fun m : Fin n → ℤ ↦
      productWindow (convolvedBoxWindow κ q) (fun i ↦ u i + m i)) 1 := by
  simpa [productWindow] using
    hasSum_fin_prod (fun i ↦ hasSum_convolvedBoxWindow hκ hm hq (u i))

/-- Product-lattice partition in the manuscript's `u - k` convention
(`app:ch_waves:thm:sampling`). -/
theorem hasSum_productWindow_sub {κ : ℝ → ℝ} (hκ : Integrable κ)
    (hm : ∫ x, κ x = 1) {q n : ℕ} (hq : 0 < q) (u : Fin n → ℝ) :
    HasSum (fun m : Fin n → ℤ ↦
      productWindow (convolvedBoxWindow κ q) (fun i ↦ u i - m i)) 1 := by
  simpa [Function.comp_def, sub_eq_add_neg] using
    (Equiv.neg (Fin n → ℤ)).hasSum_iff.mpr (hasSum_productWindow hκ hm hq u)

/-- Product-window mass in `app:ch_waves:thm:sampling`. -/
theorem integral_productWindow {κ : ℝ → ℝ} (hκ : Integrable κ)
    (hm : ∫ x, κ x = 1) (q n : ℕ) :
    ∫ x : Fin n → ℝ, productWindow (convolvedBoxWindow κ q) x = 1 := by
  simp only [productWindow, integral_fintype_prod_volume_eq_prod,
    integral_convolvedBoxWindow hκ, hm, Finset.prod_const_one]

end JanetCartan.LatticeQuadrature
