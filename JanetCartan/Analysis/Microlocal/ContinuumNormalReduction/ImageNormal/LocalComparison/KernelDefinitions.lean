module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeSeparation

/-!
# The heat integral and the nonzero-translate Bessel remainder

Shared concrete functions for the local comparison in
`app:ch_background:prop:bg-frame`, Step 1. `imageBesselKernel` is the heat
integral for the multiplier `(1 + |2πξ|²)^(-1/2)`. The definitions do not assert
integrability, Fourier identification, or convergence of the lattice series.
Those analytic obligations are separate from the algebraic symmetries here.
The consuming construction is `ImageNormal.LocalComparison`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The Euclidean heat density used to construct the image inverse in
`app:ch_background:defn:bg-row`. Only positive times are integrated. -/
def imageBesselHeatKernel (t : ℝ) (x : E) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / (4 * t))

/-- The explicit Euclidean Bessel kernel for the local comparison in
`app:ch_background:prop:bg-frame`, Step 1. At singular points the integral
is totalized; no pointwise integrability claim is built into this definition. -/
def imageBesselKernel (x : E) : ℝ :=
  (Real.sqrt Real.pi)⁻¹ * ∫ t in Set.Ioi (0 : ℝ),
    t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x

/-- The candidate off-diagonal remainder, with the zero translate removed
literally (`app:ch_background:prop:bg-frame`, Step 1). -/
def imageBesselLatticeRemainder (x y : E) : ℝ :=
  ∑' k : Fin d → ℤ, if k = 0 then 0 else
    imageBesselKernel (x - y + integerTranslation k)

/-- The kernel localized by the two fixed real cutoffs
(`app:ch_background:prop:bg-frame`, Step 1). -/
def localizedImageBesselRemainder (χ ψ : E → ℝ) (x y : E) : ℝ :=
  χ x * imageBesselLatticeRemainder x y * ψ y

/-- Evenness of the heat density (`app:ch_background:defn:bg-row`). -/
@[simp] theorem imageBesselHeatKernel_neg (t : ℝ) (x : E) :
    imageBesselHeatKernel t (-x) = imageBesselHeatKernel t x := by
  simp only [imageBesselHeatKernel, norm_neg]

/-- Evenness of the actual heat integral (`app:ch_background:defn:bg-row`). -/
@[simp] theorem imageBesselKernel_neg (x : E) :
    imageBesselKernel (-x) = imageBesselKernel x := by
  simp only [imageBesselKernel, imageBesselHeatKernel_neg]

/-- Symmetry of the nonzero lattice remainder by the literal substitution
`k ↦ -k` (`app:ch_background:prop:bg-frame`, Step 1). This algebraic identity
does not substitute for the required convergence proof. -/
theorem imageBesselLatticeRemainder_swap (x y : E) :
    imageBesselLatticeRemainder y x = imageBesselLatticeRemainder x y := by
  classical
  unfold imageBesselLatticeRemainder
  rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq
    (fun k ↦ if k = 0 then 0 else imageBesselKernel (y - x + integerTranslation k))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, neg_eq_zero]
  split_ifs with hk
  · rfl
  · have ht : integerTranslation (-k) = -(integerTranslation k : E) := by
      ext i
      simp [integerTranslation]
    rw [ht, show y - x + -integerTranslation k = -(x - y + integerTranslation k) by abel,
      imageBesselKernel_neg]

/-- The literal reversed scalar adjoint kernel interchanges the two masks
(`app:ch_background:prop:bg-frame`, Step 1). An operator-adjoint assertion
additionally requires the integrability and bounded realization proofs. -/
theorem localizedImageBesselRemainder_swap (χ ψ : E → ℝ) (x y : E) :
    localizedImageBesselRemainder χ ψ y x = localizedImageBesselRemainder ψ χ x y := by
  unfold localizedImageBesselRemainder
  rw [imageBesselLatticeRemainder_swap]
  ring

end JanetCartan.ContinuumNormalReduction.ImageNormal
