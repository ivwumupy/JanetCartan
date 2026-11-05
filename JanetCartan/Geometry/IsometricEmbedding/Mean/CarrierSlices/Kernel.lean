module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Kernel
import Mathlib.Tactic.Ring

/-!
# Finite-band slice integrals and the square partition

Literal Fubini and kernel identities for `app:ch_background:eq:bg-T` and
`app:ch_waves:eq:sampling-prefix-normal`. The mask is real and is retained
in every formula. The integrability hypotheses must be supplied by finite-band
compact support and kernel bounds; no uncut slice boundedness is asserted.
The normal densities here are functions, not postulated Hilbert normal operators.
Their identification with actual operators is a separate obligation.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow

variable {n N : ℕ}

/-- Full complex initial space of a fixed carrier slice, retaining both
quadratures (`app:ch_waves:eq:sampling-prefix-normal`). -/
abbrev CarrierSliceL2 (n : ℕ) := Lp ℂ 2 (volume : Measure (Euclidean (n - 1)))

/-- The literal finite-frequency kernel, including all factors of
`app:ch_background:eq:bg-T` and the chosen real initial mask. -/
def maskedCarrierKernel (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (x : Torus n) (u : CarrierVariable n) : EuclideanSpace ℂ (Fin n) :=
  (m u : ℂ) • carrierKernel d x u

/-- The fixed-carrier annular integral of `app:ch_waves:eq:sampling-prefix-normal`,
using exactly the kernel of the regularized continuum channel. -/
def regularizedCarrierSliceIntegral (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (z : CarrierParameter) (f : Euclidean (n - 1) → ℂ) (x : Torus n) :
    EuclideanSpace ℂ (Fin n) :=
  ∫ η, f η • maskedCarrierKernel d m x (z, η)

/-- The published regularization formula uses the same masked kernel as its
slices (`app:ch_background:eq:bg-T`). -/
theorem regularizedCarrierIntegral_eq_masked (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (f : CarrierVariable n → ℂ) (x : Torus n) :
    regularizedCarrierIntegral d m f x =
      ∫ u, f u • maskedCarrierKernel d m x u ∂carrierMeasure n := by
  simp only [regularizedCarrierIntegral, carrierTestIntegral, maskedCarrierKernel,
    smul_smul, mul_comm]

/-- Fubini disintegrates the regularized continuum formula over literal carrier
Lebesgue measure (`app:ch_background:eq:bg-T`). -/
theorem regularizedCarrierIntegral_eq_integral_slice (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (f : CarrierVariable n → ℂ) (x : Torus n)
    (hf : Integrable (fun u ↦ f u • maskedCarrierKernel d m x u) (carrierMeasure n)) :
    regularizedCarrierIntegral d m f x =
      ∫ z, regularizedCarrierSliceIntegral d m z (fun η ↦ f (z, η)) x
        ∂volume.prod volume := by
  rw [regularizedCarrierIntegral_eq_masked]
  exact integral_prod _ hf

/-- The same disintegration in the sampling theorem's `Fin 3 → ℝ`
coordinates, with the standard sampling volume
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem regularizedCarrierIntegral_eq_sampling_integral (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (f : CarrierVariable n → ℂ) (x : Torus n)
    (hf : Integrable (fun u ↦ f u • maskedCarrierKernel d m x u) (carrierMeasure n)) :
    regularizedCarrierIntegral d m f x =
      ∫ z : SeparatedSampling.Point,
        regularizedCarrierSliceIntegral d m (carrierSamplingEquiv.symm z)
          (fun η ↦ f (carrierSamplingEquiv.symm z, η)) x := by
  rw [regularizedCarrierIntegral_eq_integral_slice d m f x hf]
  simpa only [MeasurableEquiv.symm_apply_apply] using
    integral_carrierSamplingEquiv (fun z ↦
      regularizedCarrierSliceIntegral d m (carrierSamplingEquiv.symm z)
        (fun η ↦ f (carrierSamplingEquiv.symm z, η)) x)

/-- Matrix entry of the literal normal density before initial-variable
integration (`app:ch_waves:eq:colored-normal-comparison`). -/
def carrierNormalDensity (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (x y : Torus n) (i j : Fin n) (u : CarrierVariable n) : ℂ :=
  maskedCarrierKernel d m x u i * star (maskedCarrierKernel d m y u j)

/-- A real band cutoff enters the normal density squared. This is the
kernel calculation behind `app:ch_waves:eq:sampling-prefix-normal`. -/
theorem carrierNormalDensity_mul_mask (d : CarrierData n N)
    (m b : CarrierVariable n → ℝ) (x y : Torus n) (i j : Fin n)
    (u : CarrierVariable n) :
    carrierNormalDensity d (fun u ↦ m u * b u) x y i j u =
      ((b u : ℂ) ^ 2) * carrierNormalDensity d m x y i j u := by
  simp only [carrierNormalDensity, maskedCarrierKernel, PiLp.smul_apply,
    smul_eq_mul, Complex.ofReal_mul, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  ring

/-- The exact finite square-partition identity at the kernel level. The
partition may depend on both initial variables; all geometric and measurement
factors remain literal (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_carrierNormalDensity_eq (d : CarrierData n N)
    {ι : Type*} (s : Finset ι) (m b : CarrierVariable n → ℝ)
    (χ : ι → CarrierVariable n → ℝ)
    (hχ : ∀ u, ∑ a ∈ s, χ a u ^ 2 = b u ^ 2)
    (x y : Torus n) (i j : Fin n) (u : CarrierVariable n) :
    (∑ a ∈ s, carrierNormalDensity d (fun u ↦ m u * χ a u) x y i j u) =
      carrierNormalDensity d (fun u ↦ m u * b u) x y i j u := by
  simp_rw [carrierNormalDensity_mul_mask]
  rw [← Finset.sum_mul]
  congr 1
  exact_mod_cast hχ u

/-- Fubini for a full normal-kernel entry on the original product measure
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_carrierNormalDensity_eq_integral_slice (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) (x y : Torus n) (i j : Fin n)
    (h : Integrable (carrierNormalDensity d m x y i j) (carrierMeasure n)) :
    (∫ u, carrierNormalDensity d m x y i j u ∂carrierMeasure n) =
      ∫ z, ∫ η, carrierNormalDensity d m x y i j (z, η) ∂volume
        ∂volume.prod volume :=
  integral_prod _ h

/-- Integrating a common finite square partition reconstructs exactly the
continuous band normal kernel, not merely an estimate
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_integral_carrierNormalDensity_eq (d : CarrierData n N)
    {ι : Type*} (s : Finset ι) (m b : CarrierVariable n → ℝ)
    (χ : ι → CarrierVariable n → ℝ)
    (hχ : ∀ u, ∑ a ∈ s, χ a u ^ 2 = b u ^ 2)
    (x y : Torus n) (i j : Fin n)
    (hi : ∀ a ∈ s, Integrable
      (carrierNormalDensity d (fun u ↦ m u * χ a u) x y i j) (carrierMeasure n)) :
    (∑ a ∈ s, ∫ u, carrierNormalDensity d (fun u ↦ m u * χ a u) x y i j u
      ∂carrierMeasure n) =
      ∫ u, carrierNormalDensity d (fun u ↦ m u * b u) x y i j u ∂carrierMeasure n := by
  rw [← integral_finsetSum s hi]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (sum_carrierNormalDensity_eq d s m b χ hχ x y i j))

end JanetCartan.ContinuumRow
