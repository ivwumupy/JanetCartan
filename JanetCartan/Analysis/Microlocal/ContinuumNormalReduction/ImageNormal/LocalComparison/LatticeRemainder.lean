module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.HeatJets
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.Series

/-!
# Smoothness and derivative bounds for the Bessel lattice remainder

For `app:ch_background:prop:bg-frame`, Step 1, the explicit heat integral
supplies off-diagonal smoothness and rapid decay of every spatial derivative.
We instantiate the lattice-series deductions with these proved estimates:
every finite family of joint derivatives has a common summable majorant on
each closed coordinate cube of radius less than `1/2`, and the remainder
converges and can be differentiated termwise to every finite order.

Smooth real cutoffs supported in such a cube give a globally smooth,
compactly supported kernel. All its finite joint derivatives, and those of
the reversed kernel, are globally bounded. The `N + 2` budget supplies the
two extra orders for the first-order normal factors. No kernel regularity
or convergence premise remains. The consuming `ImageNormal.LocalComparison`
construction retains operator realization and Fourier identification.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A common nonnegative summable bound for every joint derivative through
order `N` on a closed comparison cube (`app:ch_background:prop:bg-frame`,
Step 1). The heat-integral estimates discharge both analytic inputs of the
series deduction, using the positive lattice gap `1 - 2r`. -/
theorem exists_summable_imageBesselLatticeTerm_jet_majorant_on_cube
    {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1 / 2) (N : ℕ) :
    ∃ u : (Fin d → ℤ) → ℝ, Summable u ∧ (∀ k, 0 ≤ u k) ∧
      ∀ n ≤ N, ∀ k, ∀ p : E × E,
        (∀ i, |p.1 i| ≤ r) → (∀ i, |p.2 i| ≤ r) →
        ‖iteratedFDeriv ℝ n (imageBesselLatticeTerm k) p‖ ≤ u k :=
  exists_summable_imageBesselLatticeTerm_jet_majorant
    contDiffOn_imageBesselKernel_offDiagonal
    exists_imageBesselKernel_offDiagonal_jet_decay hr₀ hr N

/-- Absolute convergence in multilinear operator norm of the derivative
series of the actual heat kernel (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem summable_norm_iteratedFDeriv_imageBesselLatticeTerm
    (n : ℕ) {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    Summable (fun k : Fin d → ℤ ↦ ‖iteratedFDeriv ℝ n (imageBesselLatticeTerm k) p‖) :=
  summable_norm_iteratedFDeriv_imageBesselLatticeTerm_of_offDiagonalBounds
    contDiffOn_imageBesselKernel_offDiagonal
    exists_imageBesselKernel_offDiagonal_jet_decay n hp

/-- Absolute convergence of the literal scalar remainder series
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem summable_norm_imageBesselLatticeTerm
    {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    Summable (fun k : Fin d → ℤ ↦ ‖imageBesselLatticeTerm k p‖) :=
  summable_norm_imageBesselLatticeTerm_of_offDiagonalBounds
    contDiffOn_imageBesselKernel_offDiagonal
    exists_imageBesselKernel_offDiagonal_jet_decay hp

/-- The sum defining the actual remainder converges on the comparison cube
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem summable_imageBesselLatticeTerm
    {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    Summable (fun k : Fin d → ℤ ↦ imageBesselLatticeTerm k p) :=
  (summable_norm_imageBesselLatticeTerm hp).of_norm

/-- The actual lattice series of jets differentiates to the series of their
derivatives (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasFDerivAt_tsum_iteratedFDeriv_imageBesselLatticeTerm
    (n : ℕ) {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    HasFDerivAt (fun q : E × E ↦ ∑' k : Fin d → ℤ,
      iteratedFDeriv ℝ n (imageBesselLatticeTerm k) q)
      (∑' k : Fin d → ℤ, fderiv ℝ (iteratedFDeriv ℝ n (imageBesselLatticeTerm k)) p) p :=
  hasFDerivAt_tsum_iteratedFDeriv_imageBesselLatticeTerm_of_offDiagonalBounds
    contDiffOn_imageBesselKernel_offDiagonal
    exists_imageBesselKernel_offDiagonal_jet_decay n hp

/-- Every finite joint derivative of the remainder is the convergent sum of
the derivatives of its nonzero translates
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem iteratedFDeriv_imageBesselLatticeRemainder
    (n : ℕ) {p : E × E} (hp : p ∈ imageBesselComparisonDomain d) :
    iteratedFDeriv ℝ n (fun q : E × E ↦ imageBesselLatticeRemainder q.1 q.2) p =
      ∑' k : Fin d → ℤ, iteratedFDeriv ℝ n (imageBesselLatticeTerm k) p :=
  iteratedFDeriv_imageBesselLatticeRemainder_of_offDiagonalBounds
    contDiffOn_imageBesselKernel_offDiagonal
    exists_imageBesselKernel_offDiagonal_jet_decay n hp

/-- Joint smoothness of the actual lattice remainder on the open comparison
cube (`app:ch_background:prop:bg-frame`, Step 1), with all heat-integral and
series hypotheses discharged. This supplies the localization input. -/
theorem contDiffOn_imageBesselLatticeRemainder :
    ContDiffOn ℝ ∞ (fun p : E × E ↦ imageBesselLatticeRemainder p.1 p.2)
      (imageBesselComparisonDomain d) :=
  contDiffOn_imageBesselLatticeRemainder_of_offDiagonalBounds
    contDiffOn_imageBesselKernel_offDiagonal
    exists_imageBesselKernel_offDiagonal_jet_decay

/-- Cube-supported cutoffs give compact support to the actual localized
kernel (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasCompactSupport_localizedImageBesselRemainder_of_cube_support
    {r : ℝ} (χ ψ : E → ℝ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) :
    HasCompactSupport (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.1 p.2) :=
  hasCompactSupport_localizedImageBesselRemainder χ ψ
    (hasCompactSupport_of_imageBessel_cube_support χ hχs)
    (hasCompactSupport_of_imageBessel_cube_support ψ hψs)

/-- The reversed kernel also has compact support from the same cube bounds
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasCompactSupport_localizedImageBesselRemainder_reverse_of_cube_support
    {r : ℝ} (χ ψ : E → ℝ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) :
    HasCompactSupport (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.2 p.1) :=
  hasCompactSupport_localizedImageBesselRemainder_reverse χ ψ
    (hasCompactSupport_of_imageBessel_cube_support χ hχs)
    (hasCompactSupport_of_imageBessel_cube_support ψ hψs)

/-- Global joint smoothness of the actual localized remainder, from smooth
cutoffs supported in the comparison cube
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_localizedImageBesselRemainder
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) :
    ContDiff ℝ ∞ (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.1 p.2) :=
  contDiff_localizedImageBesselRemainder_of_contDiffOn hr χ ψ hχ hψ hχs hψs
    contDiffOn_imageBesselLatticeRemainder

/-- Global smoothness of the reversed scalar kernel used for the adjoint
remainder (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiff_localizedImageBesselRemainder_reverse
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) :
    ContDiff ℝ ∞ (fun p : E × E ↦ localizedImageBesselRemainder χ ψ p.2 p.1) :=
  contDiff_localizedImageBesselRemainder_reverse_of_contDiffOn hr χ ψ hχ hψ hχs hψs
    contDiffOn_imageBesselLatticeRemainder

/-- A global bound for all prescribed finite joint derivatives of the
localized remainder (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem exists_localizedImageBesselRemainder_jet_budget
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ p : E × E,
      ‖iteratedFDeriv ℝ n
        (fun q : E × E ↦ localizedImageBesselRemainder χ ψ q.1 q.2) p‖ ≤ C :=
  exists_localizedImageBesselRemainder_jet_budget_of_contDiffOn
    hr χ ψ hχ hψ hχs hψs contDiffOn_imageBesselLatticeRemainder N

/-- One global constant bounds all joint derivatives through `N + 2` of
both kernel orientations. These are the two extra orders needed before
composition with the first-order normal factors in
`app:ch_background:prop:bg-frame`, Step 1. The local-comparison consumer
retains the bounded operator realization; no analytic premise remains here. -/
theorem exists_localizedImageBesselRemainder_two_factor_budget
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N + 2, ∀ p : E × E,
      ‖iteratedFDeriv ℝ n
        (fun q : E × E ↦ localizedImageBesselRemainder χ ψ q.1 q.2) p‖ ≤ C ∧
      ‖iteratedFDeriv ℝ n
        (fun q : E × E ↦ localizedImageBesselRemainder χ ψ q.2 q.1) p‖ ≤ C :=
  exists_localizedImageBesselRemainder_two_factor_budget_of_contDiffOn
    hr χ ψ hχ hψ hχs hψs contDiffOn_imageBesselLatticeRemainder N

end JanetCartan.ContinuumNormalReduction.ImageNormal
