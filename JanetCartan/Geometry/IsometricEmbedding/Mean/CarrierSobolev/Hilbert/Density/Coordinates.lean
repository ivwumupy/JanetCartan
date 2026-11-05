module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert.Space
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Density

/-!
# Finite Euclidean coordinates for physical Sobolev density

These coordinate maps transfer compact smooth approximation to the literal
carrier inputs in `app:ch_background:prop:bg-adjoint` and
`app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap ContDiff

namespace JanetCartan.CarrierSobolev
open ContinuumRow

/-- The finite Euclidean coordinate target for compact smooth density in
`app:ch_background:prop:bg-adjoint`. -/
abbrev DensityEuclidean (n : ℕ) := EuclideanSpace ℝ (Fin (Module.finrank ℝ (InitialSpace n)))

/-- Orthonormal coordinates preserve the full initial Euclidean geometry
(`app:ch_background:prop:bg-adjoint`). -/
def densityEuclideanEquiv (n : ℕ) : InitialSpace n ≃ₗᵢ[ℝ] DensityEuclidean n :=
  (stdOrthonormalBasis ℝ (InitialSpace n)).repr

/-- The published coordinate map is a continuous linear equivalence, allowing
smooth functions to be transferred for `app:ch_background:prop:bg-adjoint`. -/
def initialCoordinatesLinear (n : ℕ) : CarrierVariable n ≃L[ℝ] InitialSpace n :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean 2)).symm.prodCongr
    (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1)))).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ ParameterSpace (Euclidean (n - 1))).symm

/-- This linear map is the existing measure-theoretic coordinate change
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialCoordinatesLinear_apply (n : ℕ) (x : CarrierVariable n) :
    initialCoordinatesLinear n x = initialCoordinates n x := rfl

/-- Smooth, invertible finite coordinates on the actual carrier domain
(`app:ch_background:prop:bg-adjoint`). -/
def densityCoordinates (n : ℕ) : CarrierVariable n ≃L[ℝ] DensityEuclidean n :=
  (initialCoordinatesLinear n).trans (densityEuclideanEquiv n).toContinuousLinearEquiv

/-- Finite coordinates preserve the prescribed physical product measure
(`app:ch_background:prop:bg-adjoint`). -/
theorem densityCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (densityCoordinates n) (carrierMeasure n) volume :=
  (densityEuclideanEquiv n).measurePreserving.comp (initialCoordinates_measurePreserving n)

/-- The inverse finite coordinate map preserves volume
(`app:ch_background:prop:bg-adjoint`). -/
theorem densityCoordinates_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (densityCoordinates n).symm volume (carrierMeasure n) :=
  (initialCoordinates_symm_measurePreserving n).comp
    (densityEuclideanEquiv n).symm.measurePreserving

/-- Orthonormal coordinates retain exactly the norm in the physical weight
(`app:ch_background:prop:bg-adjoint`). -/
theorem densityCoordinates_norm (n : ℕ) (x : CarrierVariable n) :
    ‖densityCoordinates n x‖ = ‖initialCoordinates n x‖ :=
  (densityEuclideanEquiv n).norm_map _

/-- L² transport from full initial Euclidean space to finite coordinates
(`app:ch_background:prop:bg-adjoint`). -/
def densityEuclideanL2Equiv (n : ℕ) :
    Lp ℂ 2 (volume : Measure (InitialSpace n)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (DensityEuclidean n)) where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (densityEuclideanEquiv n).symm
    (densityEuclideanEquiv n).symm.measurePreserving
  invFun := Lp.compMeasurePreserving (densityEuclideanEquiv n)
    (densityEuclideanEquiv n).measurePreserving
  left_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [LinearIsometryEquiv.symm_comp_self] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [LinearIsometryEquiv.self_comp_symm] using Lp.compMeasurePreserving_id_apply f

/-- L² transport of actual physical classes to finite coordinates, used to
instantiate the compact smooth density theorem (`app:ch_background:prop:bg-adjoint`). -/
def densityL2Equiv (n : ℕ) :
    CarrierL2 n ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (DensityEuclidean n)) :=
  (initialL2Equiv n).trans (densityEuclideanL2Equiv n)

/-- Representative formula for physical L² transport
(`app:ch_background:prop:bg-adjoint`). -/
theorem densityL2Equiv_coeFn (n : ℕ) (f : CarrierL2 n) :
    densityL2Equiv n f =ᵐ[volume] f ∘ (densityCoordinates n).symm := by
  have h := (densityEuclideanEquiv n).symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (initialL2Equiv_coeFn n f)
  exact (Lp.coeFn_compMeasurePreserving _ _).trans h

/-- Representative formula for the reverse physical L² transport
(`app:ch_background:prop:bg-adjoint`). -/
theorem densityL2Equiv_symm_coeFn (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure (DensityEuclidean n))) :
    (densityL2Equiv n).symm f =ᵐ[carrierMeasure n] f ∘ densityCoordinates n := by
  have h := (initialCoordinates_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving f (densityEuclideanEquiv n).measurePreserving)
  exact (initialL2Equiv_symm_coeFn n _).trans h

end JanetCartan.CarrierSobolev
