module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.CompactTensor
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature

/-!
# Deterministic quadrature of compact classical background tensors

Application of the checked Banach-valued quadrature theorem to the literal
physical L2 tensors constructed from classical profiles. This proves the
independent deduction in `app:ch_waves:eq:background-quadrature`, retaining the
original carrier measure, patch, box-convolution window, samples, weights and
colored masks. Radial values are arbitrary unchanged values in `[-1,1]`.

The retained-background parent must instantiate the classical smoothness,
common support and joint budgets on its actual tensor. This module does not
claim their construction or the complete sampling theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground
open SeparatedSampling LatticeQuadrature BackgroundQuadrature CompactTensor

variable {n : ℕ} {J : Set (Euclidean n)} (hJ : IsCompact J)
variable {H : ℝ → Point → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
variable (hH : ContDiff ℝ ∞ (fun q : ℝ × (Point × Euclidean n) ↦ H q.1 q.2.1 q.2.2))
variable (hS : ∀ τ z x, x ∉ J → H τ z x = 0)

/-- Classical compact profiles imply the deterministic L2 background estimate
for every admissible shift realization. The displayed coefficient depends only
on the fixed support, patch, derivative order and classical budget, and is
independent of `L`, frequencies, radial labels, mesh and shifts.
Source: `app:ch_waves:eq:background-quadrature`. -/
theorem norm_retainedBackground_quadrature_le
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (hψsmooth : ContDiff ℝ ∞ ψ)
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {L : ℝ} (hL : 1 ≤ L) {rpar : ℕ}
    (hpr : p ≤ rpar)
    (hjet : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
      ‖iteratedFDeriv ℝ j
        (fun q : ℝ × (Point × Euclidean n) ↦ ψ q.2.1 • H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ ≤ A j * L ^ (j - rpar))
    (τ : (Fin 3 → Fin (p + 1)) → ℝ) (hτ : ∀ c, τ c ∈ Icc (-1 : ℝ) 1)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) :
    ‖(∑ a ∈ samples p B ψ (convolvedBoxWindow κ p) h U,
        weight ψ (convolvedBoxWindow κ p) h U a •
          backgroundL2 hJ hH hS (τ (color p a.1), node h U a)) -
      ∑ c, ∫ z : Point,
        coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h c z •
          (ψ z • backgroundL2 hJ hH hS (τ c, z))‖ ≤
      (backgroundQuadratureConstant p B * physicalL2Constant hJ * A p) * h ^ p := by
  simpa only [mul_assoc] using
    norm_background_quadrature_colored_le hc hs hm hn hk hp hψ
      (fun c z ↦ backgroundL2 hJ hH hS (τ c, z))
      (fun c ↦ contDiff_weighted_backgroundL2 hJ hH hS hψsmooth (τ c) p)
      (mul_nonneg (physicalL2Constant_nonneg hJ) (hA p))
      (fun c z ↦ norm_iteratedFDeriv_weighted_backgroundL2_le_of_le
        hJ hH hS hψsmooth hA hL hjet (hτ c) z hpr) hh hh₁ U hU

/-- The manuscript's quadrature order `2*n-1`, under its positive-dimensional
and parameter-reserve hypotheses. This has the exact original colored masks
and unchanged radial labels (`app:ch_waves:eq:background-quadrature`). -/
theorem norm_retainedBackground_quadrature_two_mul_sub_one_le (hn_dim : 1 ≤ n)
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (hψsmooth : ContDiff ℝ ∞ ψ)
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {L : ℝ} (hL : 1 ≤ L) {rpar : ℕ}
    (hpr : 2 * n - 1 ≤ rpar)
    (hjet : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
      ‖iteratedFDeriv ℝ j
        (fun q : ℝ × (Point × Euclidean n) ↦ ψ q.2.1 • H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ ≤ A j * L ^ (j - rpar))
    (τ : (Fin 3 → Fin (2 * n - 1 + 1)) → ℝ) (hτ : ∀ c, τ c ∈ Icc (-1 : ℝ) 1)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) :
    ‖(∑ a ∈ samples (2 * n - 1) B ψ (convolvedBoxWindow κ (2 * n - 1)) h U,
        weight ψ (convolvedBoxWindow κ (2 * n - 1)) h U a •
          backgroundL2 hJ hH hS (τ (color (2 * n - 1) a.1), node h U a)) -
      ∑ c, ∫ z : Point,
        coloredBlockMask (2 * n - 1) (integerCube (blockCutoff (2 * n - 1) B h))
          (convolvedBoxWindow κ (2 * n - 1)) h c z •
          (ψ z • backgroundL2 hJ hH hS (τ c, z))‖ ≤
      (backgroundQuadratureConstant (2 * n - 1) B * physicalL2Constant hJ * A (2 * n - 1)) *
        h ^ (2 * n - 1) :=
  norm_retainedBackground_quadrature_le hJ hH hS hc hs hm hn hk (by omega)
    hψ hψsmooth hA hL hpr hjet τ hτ hh hh₁ U hU

end JanetCartan.Sampling.RetainedBackground
