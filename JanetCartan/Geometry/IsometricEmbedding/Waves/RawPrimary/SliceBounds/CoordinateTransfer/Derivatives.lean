module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.Coordinates
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Directional derivative integrals in actual physical coordinates

These change-of-variables identities supply the physical weak-jet step in
`app:ch_waves:eq:individual-raw-slice`. The chain rule uses the already
constructed continuous linear coordinate map of the retained adapted section.
No identification of physical and slice derivatives is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace JanetCartan.RawPrimary.SliceBounds
open ActualCarriers.FrozenPhaseReference

variable {n : ℕ} {ξ : Euclidean n} (a : AdaptedSection ξ)

/-- The measurable physical map is the inverse of the actual continuous
linear coordinate map used by the wave construction
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem adaptedPhysicalCoordinates_eq_linear :
    (adaptedPhysicalCoordinates a : (ℝ × Euclidean (n - 1)) → Euclidean n) =
      (NullTransport.ActualFlow.adaptedCoordinates a).symm := rfl

/-- The inverse measurable map is that same continuous linear map
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem adaptedPhysicalCoordinates_symm_eq_linear :
    ((adaptedPhysicalCoordinates a).symm : Euclidean n → (ℝ × Euclidean (n - 1))) =
      NullTransport.ActualFlow.adaptedCoordinates a := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Literal chain rule in every slice direction, including the time direction,
for `app:ch_waves:eq:individual-raw-slice`. -/
theorem fderiv_comp_adaptedPhysicalCoordinates (f : Euclidean n → E)
    (q v : ℝ × Euclidean (n - 1)) :
    fderiv ℝ (f ∘ adaptedPhysicalCoordinates a) q v =
      fderiv ℝ f (adaptedPhysicalCoordinates a q) (adaptedPhysicalCoordinates a v) := by
  change fderiv ℝ (f ∘ (NullTransport.ActualFlow.adaptedCoordinates a).symm) q v = _
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  rfl

/-- Literal chain rule for a physical direction, with its normal and
transverse components (`app:ch_waves:eq:individual-raw-slice`). -/
theorem fderiv_comp_adaptedPhysicalCoordinates_symm
    (f : (ℝ × Euclidean (n - 1)) → E) (x v : Euclidean n) :
    fderiv ℝ (f ∘ (adaptedPhysicalCoordinates a).symm) x v =
      fderiv ℝ f ((adaptedPhysicalCoordinates a).symm x)
        (⟪a.normal, v⟫_ℝ, a.embedding.toContinuousLinearMap.adjoint v) := by
  change fderiv ℝ (f ∘ NullTransport.ActualFlow.adaptedCoordinates a) x v = _
  rw [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply]
  change fderiv ℝ f ((adaptedPhysicalCoordinates a).symm x)
    ((adaptedPhysicalCoordinates a).symm v) = _
  rw [adaptedPhysicalCoordinates_symm_apply a v]

/-- A physical directional test derivative is exactly the derivative in the
corresponding actual slice direction (`app:ch_waves:eq:individual-raw-slice`). -/
theorem fderiv_adaptedPhysicalCoordinates_direction (f : Euclidean n → E)
    (q : ℝ × Euclidean (n - 1)) (v : Euclidean n) :
    fderiv ℝ (f ∘ adaptedPhysicalCoordinates a) q
        ((adaptedPhysicalCoordinates a).symm v) =
      fderiv ℝ f (adaptedPhysicalCoordinates a q) v := by
  rw [fderiv_comp_adaptedPhysicalCoordinates, MeasurableEquiv.apply_symm_apply]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Transfer a test pairing from physical L² to the actual full product
measure (`app:ch_waves:eq:individual-raw-slice`). No integrability premise is
needed for this equality of Bochner integrals. -/
theorem integral_smul_adaptedL2Equiv
    (u : Lp F 2 (volume : Measure (ℝ × Euclidean (n - 1))))
    (φ : Euclidean n → ℂ) :
    ∫ x, φ x • adaptedL2Equiv a F u x =
      ∫ q, φ (adaptedPhysicalCoordinates a q) • u q := by
  calc
    _ = ∫ x, φ x • u ((adaptedPhysicalCoordinates a).symm x) := by
      apply integral_congr_ae
      filter_upwards [adaptedL2Equiv_coeFn a F u] with x hx
      rw [hx]
      rfl
    _ = _ := by
      simpa only [MeasurableEquiv.apply_symm_apply] using
        integral_adaptedPhysicalCoordinates_symm a
          (fun q ↦ φ (adaptedPhysicalCoordinates a q) • u q)

/-- Transfer a physical directional derivative test pairing using the proven
linear chain rule. This is the weak-jet integral required by
`app:ch_waves:eq:individual-raw-slice`. -/
theorem integral_fderiv_smul_adaptedL2Equiv
    (u : Lp F 2 (volume : Measure (ℝ × Euclidean (n - 1))))
    (φ : Euclidean n → ℂ) (v : Euclidean n) :
    ∫ x, fderiv ℝ φ x v • adaptedL2Equiv a F u x =
      ∫ q, fderiv ℝ (φ ∘ adaptedPhysicalCoordinates a) q
        ((adaptedPhysicalCoordinates a).symm v) • u q := by
  rw [integral_smul_adaptedL2Equiv]
  simp only [fderiv_adaptedPhysicalCoordinates_direction]

/-- Reverse transfer of test pairings to actual physical volume
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem integral_smul_adaptedL2Equiv_symm
    (u : Lp F 2 (volume : Measure (Euclidean n)))
    (φ : (ℝ × Euclidean (n - 1)) → ℂ) :
    ∫ q, φ q • (adaptedL2Equiv a F).symm u q =
      ∫ x, φ ((adaptedPhysicalCoordinates a).symm x) • u x := by
  calc
    _ = ∫ q, φ q • u (adaptedPhysicalCoordinates a q) := by
      apply integral_congr_ae
      filter_upwards [adaptedL2Equiv_symm_coeFn a F u] with q hq
      rw [hq]
      rfl
    _ = _ := by
      simpa only [MeasurableEquiv.symm_apply_apply] using
        integral_adaptedPhysicalCoordinates a
          (fun x ↦ φ ((adaptedPhysicalCoordinates a).symm x) • u x)

/-- Reverse transfer of directional derivative integrals. The physical
direction is the actual vector `v.1 • normal + embedding v.2`
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem integral_fderiv_smul_adaptedL2Equiv_symm
    (u : Lp F 2 (volume : Measure (Euclidean n)))
    (φ : (ℝ × Euclidean (n - 1)) → ℂ) (v : ℝ × Euclidean (n - 1)) :
    ∫ q, fderiv ℝ φ q v • (adaptedL2Equiv a F).symm u q =
      ∫ x, fderiv ℝ (φ ∘ (adaptedPhysicalCoordinates a).symm) x
        (adaptedPhysicalCoordinates a v) • u x := by
  rw [integral_smul_adaptedL2Equiv_symm]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  rw [fderiv_comp_adaptedPhysicalCoordinates_symm,
    ← adaptedPhysicalCoordinates_symm_apply, MeasurableEquiv.symm_apply_apply]

end JanetCartan.RawPrimary.SliceBounds
