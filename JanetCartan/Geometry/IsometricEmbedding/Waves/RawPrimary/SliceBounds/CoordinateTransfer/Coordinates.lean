module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Coordinates
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The actual adapted physical coordinate transfer

The output of `exists_rawSliceBandOperator` uses full product Lebesgue measure.
For `app:ch_waves:eq:individual-raw-slice`, this leaf identifies that measure
with Euclidean physical volume using the retained section of
`app:ch_seed:prop:seed-phase-charts`. No output measure is transported by
definition: preservation of the two existing volumes is a theorem.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace JanetCartan.RawPrimary.SliceBounds
open ActualCarriers.FrozenPhaseReference

variable {n : ℕ} {ξ : Euclidean n} (a : AdaptedSection ξ)

/-- The retained adapted physical isometry is onto, by the section's spanning
property (`app:ch_seed:prop:seed-phase-charts`). -/
def adaptedSpacetimeEquiv :
    WithLp 2 (ℝ × Euclidean (n - 1)) ≃ₗᵢ[ℝ] Euclidean n :=
  LinearIsometryEquiv.ofSurjective (FullPhaseCharts.adaptedSpacetime a)
    (FullPhaseCharts.adaptedSpacetime_surjective a)

/-- Literal adapted coordinates on the product used by the slice operator
(`app:ch_waves:setup:oscillatory`). -/
def adaptedPhysicalCoordinates : (ℝ × Euclidean (n - 1)) ≃ᵐ Euclidean n :=
  (MeasurableEquiv.toLp 2 (ℝ × Euclidean (n - 1))).trans
    (adaptedSpacetimeEquiv a).toMeasurableEquiv

/-- The forward map uses the retained normal and transverse embedding
(`app:ch_seed:prop:seed-phase-charts`). -/
@[simp] theorem adaptedPhysicalCoordinates_apply (q : ℝ × Euclidean (n - 1)) :
    adaptedPhysicalCoordinates a q = q.1 • a.normal + a.embedding q.2 := rfl

/-- The inverse consists of the normal coordinate and the adjoint section
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem adaptedPhysicalCoordinates_symm_apply (x : Euclidean n) :
    (adaptedPhysicalCoordinates a).symm x =
      (⟪a.normal, x⟫_ℝ, a.embedding.toContinuousLinearMap.adjoint x) := by
  apply (adaptedPhysicalCoordinates a).injective
  rw [MeasurableEquiv.apply_symm_apply, adaptedPhysicalCoordinates_apply]
  exact (a.covector_decomposition x).symm

/-- Actual product Lebesgue volume maps to actual Euclidean volume, with
Jacobian of absolute value one (`app:ch_waves:eq:individual-raw-slice`). -/
theorem adaptedPhysicalCoordinates_measurePreserving :
    MeasurePreserving (adaptedPhysicalCoordinates a)
      (volume : Measure (ℝ × Euclidean (n - 1))) volume :=
  (adaptedSpacetimeEquiv a).measurePreserving.comp
    (WithLp.volume_preserving_toLp ℝ (Euclidean (n - 1)))

/-- The inverse preserves those same full volumes
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem adaptedPhysicalCoordinates_symm_measurePreserving :
    MeasurePreserving (adaptedPhysicalCoordinates a).symm volume
      (volume : Measure (ℝ × Euclidean (n - 1))) :=
  (adaptedPhysicalCoordinates_measurePreserving a).symm

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Complex L² equivalence from the actual full slice output to physical
Euclidean space (`app:ch_waves:eq:individual-raw-slice`). It retains both
quadratures and works for scalar, vector, and Frobenius matrix outputs. -/
def adaptedL2Equiv :
    Lp F 2 (volume : Measure (ℝ × Euclidean (n - 1))) ≃ₗᵢ[ℂ]
      Lp F 2 (volume : Measure (Euclidean n)) where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (adaptedPhysicalCoordinates a).symm
    (adaptedPhysicalCoordinates_symm_measurePreserving a)
  invFun := Lp.compMeasurePreserving (adaptedPhysicalCoordinates a)
    (adaptedPhysicalCoordinates_measurePreserving a)
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

/-- Forward representative of the slice-to-physical L² transfer
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem adaptedL2Equiv_coeFn
    (f : Lp F 2 (volume : Measure (ℝ × Euclidean (n - 1)))) :
    adaptedL2Equiv a F f =ᵐ[volume] f ∘ (adaptedPhysicalCoordinates a).symm :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Reverse representative of the physical-to-slice L² transfer
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem adaptedL2Equiv_symm_coeFn (f : Lp F 2 (volume : Measure (Euclidean n))) :
    (adaptedL2Equiv a F).symm f =ᵐ[volume] f ∘ adaptedPhysicalCoordinates a :=
  Lp.coeFn_compMeasurePreserving _ _

variable {F}

/-- Change of variables for actual Bochner integrals, used for the physical
weak jets in `app:ch_waves:eq:individual-raw-slice`. -/
theorem integral_adaptedPhysicalCoordinates (f : Euclidean n → F) :
    ∫ q, f (adaptedPhysicalCoordinates a q) = ∫ x, f x :=
  (adaptedPhysicalCoordinates_measurePreserving a).integral_comp' f

/-- Reverse change of variables for the literal product integral
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem integral_adaptedPhysicalCoordinates_symm (f : (ℝ × Euclidean (n - 1)) → F) :
    ∫ x, f ((adaptedPhysicalCoordinates a).symm x) = ∫ q, f q :=
  (adaptedPhysicalCoordinates_symm_measurePreserving a).integral_comp' f

end JanetCartan.RawPrimary.SliceBounds
