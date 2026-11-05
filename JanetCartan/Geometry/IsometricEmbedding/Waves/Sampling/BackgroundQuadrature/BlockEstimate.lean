module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature.Window

/-!
# Deterministic error on a normalized carrier block

Taylor cancellation and the two mass-one identities give the Banach-valued
block estimate in `app:ch_waves:eq:background-quadrature`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff

namespace JanetCartan.Sampling.BackgroundQuadrature
open SeparatedSampling LatticeQuadrature

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A supported Taylor remainder is `A (h R)^p`, as used in
`app:ch_waves:eq:background-quadrature`. -/
theorem norm_window_smul_remainder_le {κ : ℝ → ℝ} {p : ℕ} {M : ℝ}
    (hw : WindowBounds p (convolvedBoxWindow κ p) M) (hp : 0 < p)
    {f : Point → V} (hf : ContDiff ℝ p f) {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ z, ‖iteratedFDeriv ℝ p f z‖ ≤ A) {h : ℝ} (hh : 0 ≤ h)
    (x y : Point) :
    ‖productWindow (convolvedBoxWindow κ p) y •
      (f (x + h • y) - carrierTaylor f p x (h • y))‖ ≤
      productWindow (convolvedBoxWindow κ p) y * (A * (h * windowRadius p) ^ p) := by
  have hW : 0 ≤ productWindow (convolvedBoxWindow κ p) y :=
    Finset.prod_nonneg fun i _ ↦ hw.nonneg (y i)
  by_cases hy : productWindow (convolvedBoxWindow κ p) y = 0
  · simp [hy]
  rw [norm_smul, Real.norm_of_nonneg hW]
  apply mul_le_mul_of_nonneg_left _ hW
  apply (norm_sub_carrierTaylor_le hp hA (fun _ _ ↦ hf.contDiffAt)
    (fun _ _ ↦ hD _)).trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_smul, Real.norm_of_nonneg hh]
  exact mul_le_mul_of_nonneg_left (productWindow_support_norm hw hy) hh

/-- Deterministic quadrature error in one normalized block, for the actual
convolved-box window and every admissible shift. Both sampled and integral
masses are exactly one, and the Taylor polynomial cancels by the proved lattice
exactness (`app:ch_waves:eq:background-quadrature`). -/
theorem norm_normalized_block_error_le {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) {p : ℕ} (hp : 0 < p) {M : ℝ}
    (hw : WindowBounds p (convolvedBoxWindow κ p) M)
    {f : Point → V} (hf : ContDiff ℝ p f) {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ z, ‖iteratedFDeriv ℝ p f z‖ ≤ A) {h : ℝ} (hh : 0 ≤ h)
    (x : Point) {u : Point} (hu : ∀ i, 0 ≤ u i ∧ u i < 1) :
    ‖(∑ m ∈ integerCube (p + 2),
        productWindow (convolvedBoxWindow κ p) (fun i ↦ u i + m i) •
          f (x + h • (fun i ↦ u i + m i))) -
      ∫ y : Point, productWindow (convolvedBoxWindow κ p) y • f (x + h • y)‖ ≤
        2 * A * (h * windowRadius p) ^ p := by
  let W : Point → ℝ := productWindow (convolvedBoxWindow κ p)
  let T (y : Point) := carrierTaylor f p x (h • y)
  let R (y : Point) := f (x + h • y) - T y
  let D : ℝ := A * (h * windowRadius p) ^ p
  have hi : Integrable κ := hs.continuous.integrable_of_hasCompactSupport hc
  have hmass : ∫ y : Point, W y = 1 := integral_productWindow hi hm p 3
  have hsum : ∑ m ∈ integerCube (p + 2), W (fun i ↦ u i + m i) = 1 :=
    sum_productWindow_offsets hi hm hp hw hu
  have hTi : Integrable (fun y ↦ W y • T y) :=
    integrable_carrierTaylor_productWindow hc hs.continuous f p x h
  have hFi : Integrable (fun y ↦ W y • f (x + h • y)) := by
    apply integrable_productWindow_smul hw (contDiff_convolvedBoxWindow hc hs p).continuous
    exact hf.continuous.comp (by fun_prop)
  have hWi : Integrable W := by
    simpa [W] using integrable_polynomial_productWindow hc hs.continuous p
      (1 : MvPolynomial (Fin 3) ℝ)
  have hR (y : Point) : ‖W y • R y‖ ≤ W y * D :=
    norm_window_smul_remainder_le hw hp hf hA hD hh x y
  have hsample : ‖∑ m ∈ integerCube (p + 2),
      W (fun i ↦ u i + m i) • R (fun i ↦ u i + m i)‖ ≤ D := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun m _ ↦ hR (fun i ↦ u i + m i))).trans_eq
    rw [← Finset.sum_mul, hsum, one_mul]
  have hintegral : ‖∫ y : Point, W y • R y‖ ≤ D := by
    apply (norm_integral_le_of_norm_le (hWi.mul_const D)
      (Filter.Eventually.of_forall hR)).trans_eq
    rw [integral_mul_const, hmass, one_mul]
  have he :
      (∑ m ∈ integerCube (p + 2), W (fun i ↦ u i + m i) • f (x + h • (fun i ↦ u i + m i))) -
        (∫ y : Point, W y • f (x + h • y)) =
      (∑ m ∈ integerCube (p + 2), W (fun i ↦ u i + m i) • R (fun i ↦ u i + m i)) -
        (∫ y : Point, W y • R y) := by
    simp only [R, smul_sub, Finset.sum_sub_distrib, integral_sub hFi hTi]
    rw [show (∑ m ∈ integerCube (p + 2), W (fun i ↦ u i + m i) • T (fun i ↦ u i + m i)) =
      ∫ y : Point, W y • T y from sum_carrierTaylor_offsets hc hs hw f x h hu]
    abel
  change ‖_‖ ≤ _
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hsample hintegral).trans_eq (by dsimp [D]; ring))

end JanetCartan.Sampling.BackgroundQuadrature
