module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Euclidean coordinates for the carrier input

The initial Sobolev norm in `app:ch_background:prop:bg-adjoint` includes all
three carrier parameters and all transverse initial coordinates. The literal
product used by `ContinuumRow.CarrierL2` has the product norm, so it cannot be
used as a Euclidean Fourier domain directly. This leaf supplies the actual
measure-preserving coordinate change to a Hilbert product and its L² isometry.
It is shared by the partial inverse transform and the full Sobolev construction.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan.CarrierSobolev
open ContinuumRow

/-- Euclidean carrier parameter space for `app:ch_background:prop:bg-adjoint`.
The underlying coordinates are exactly `z = (s,v)`. -/
abbrev ParameterSpace := WithLp 2 (ℝ × Euclidean 2)

/-- Euclidean initial space `(z,y)` for `app:ch_background:prop:bg-adjoint`.
The same coordinates describe `(ζ,η)` after taking the full Fourier transform. -/
abbrev InitialSpace (n : ℕ) := WithLp 2 (ParameterSpace × Euclidean (n - 1))

/-- Coordinate identification without changing any initial variables
(`app:ch_background:prop:bg-adjoint`). -/
def initialCoordinates (n : ℕ) : CarrierVariable n ≃ᵐ InitialSpace n :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 CarrierParameter)
    (MeasurableEquiv.refl (Euclidean (n - 1)))).trans
      (MeasurableEquiv.toLp 2 (ParameterSpace × Euclidean (n - 1)))

/-- The Euclidean volume is exactly the prescribed Lebesgue product
`(ds dv) dy`, not a transported or periodic measure
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (initialCoordinates n) (carrierMeasure n) volume :=
  (WithLp.volume_preserving_toLp ParameterSpace (Euclidean (n - 1))).comp
    ((WithLp.volume_preserving_toLp ℝ (Euclidean 2)).prod
      (MeasurePreserving.id volume))

/-- The inverse coordinate change also preserves the literal initial measure
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialCoordinates_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (initialCoordinates n).symm volume (carrierMeasure n) :=
  (initialCoordinates_measurePreserving n).symm

/-- Squared Euclidean length includes every carrier and transverse coordinate
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialCoordinates_norm_sq (n : ℕ) (x : CarrierVariable n) :
    ‖initialCoordinates n x‖ ^ 2 = |x.1.1| ^ 2 + ‖x.1.2‖ ^ 2 + ‖x.2‖ ^ 2 := by
  simp [initialCoordinates, WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs,
    MeasurableEquiv.prodCongr, WithLp.fst, WithLp.snd]

/-- The Euclidean inner product is the sum of the coordinate inner products
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialCoordinates_inner (n : ℕ) (x y : CarrierVariable n) :
    inner ℝ (initialCoordinates n x) (initialCoordinates n y) =
      x.1.1 * y.1.1 + inner ℝ x.1.2 y.1.2 + inner ℝ x.2 y.2 := by
  simp [initialCoordinates, WithLp.prod_inner_apply, mul_comm,
    MeasurableEquiv.prodCongr]

/-- Actual L² identification between the published carrier input and Euclidean
initial coordinates (`app:ch_background:prop:bg-adjoint`). -/
def initialL2Equiv (n : ℕ) :
    CarrierL2 n ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (InitialSpace n)) where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (initialCoordinates n).symm
    (initialCoordinates_symm_measurePreserving n)
  invFun := Lp.compMeasurePreserving (initialCoordinates n)
    (initialCoordinates_measurePreserving n)
  left_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.symm_comp_self] using
      Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.self_comp_symm] using
      Lp.compMeasurePreserving_id_apply f

/-- Representative formula for the coordinate isometry
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialL2Equiv_coeFn (n : ℕ) (f : CarrierL2 n) :
    initialL2Equiv n f =ᵐ[volume] f ∘ (initialCoordinates n).symm :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Representative formula in the reverse direction
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialL2Equiv_symm_coeFn (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure (InitialSpace n))) :
    (initialL2Equiv n).symm f =ᵐ[carrierMeasure n] f ∘ initialCoordinates n :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Full unit-period Fourier transform on physical `(z,y)` classes, with every
coordinate included. This is a genuine L² equivalence; the partial radian
`η → y` realization is a separate construction
(`app:ch_background:prop:bg-adjoint`). -/
def initialFourier (n : ℕ) : CarrierL2 n ≃ₗᵢ[ℂ] CarrierL2 n :=
  ((initialL2Equiv n).trans (Lp.fourierTransformₗᵢ (InitialSpace n) ℂ)).trans
    (initialL2Equiv n).symm

/-- Plancherel on the literal initial product measure
(`app:ch_background:prop:bg-adjoint`). -/
theorem initialFourier_norm (n : ℕ) (f : CarrierL2 n) :
    ‖initialFourier n f‖ = ‖f‖ := (initialFourier n).norm_map f

end JanetCartan.CarrierSobolev
