module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelIdentity.Integrability

/-!
# Absolute convergence and Fubini for the frozen mixed normal

The mixed term of `paper-v2.tex`, `app:ch_background:prop:bg-frame`, leaves
the Euclidean Bessel kernel undifferentiated. Compact source derivatives and
local L¹ integrability of L² inputs supply all majorants below. These are
inputs to the identification of `B D*` and its actual adjoint `D B*`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow
open JanetCartan.ContinuumNormalReduction.ImageNormal

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

namespace KernelIdentity

/-- The source derivative used by the actual mixed entry is continuous and
compactly supported. Consumer: its Bessel integral in
`app:ch_background:prop:bg-frame`. -/
theorem mixedSource_derivative_regular (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (j k a : Fin n) :
    Continuous (fun q ↦ fderiv ℝ (fixedMixedSourceKernel hR A j k) q
      (EuclideanSpace.single a 1, 0)) ∧
    HasCompactSupport (fun q ↦ fderiv ℝ (fixedMixedSourceKernel hR A j k) q
      (EuclideanSpace.single a 1, 0)) :=
  ⟨((contDiff_fixedMixedSourceKernel hR hcell A j k).fderiv_right (m := ∞) (by simp)
    |>.clm_apply contDiff_const).continuous,
    (hasCompactSupport_fixedMixedSourceKernel hR A j k).fderiv_apply ℝ _⟩

/-- Differentiating the compact source section preserves its measurement
support. Consumer: the L² Fubini majorant for the mixed normal in
`app:ch_background:prop:bg-frame`. -/
theorem mixedSource_fderiv_eq_zero (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (j k : Fin n) (z y : E)
    (hy : y ∉ tsupport (FixedCutoffs.physical hR 1)) :
    fderiv ℝ (fixedMixedSourceKernel hR A j k) (z, y) = 0 :=
  fderiv_of_notMem_tsupport ℝ (fun h ↦
    hy ((tsupport_fixedMixedSourceKernel_subset hR A j k h).2))

/-- Absolute convergence of the defining Bessel integral in each mixed
entry (`app:ch_background:prop:bg-frame`). -/
theorem integrable_mixedSource_bessel_derivative (hR : 0 < R)
    (hcell : 4 * R < 1 / 2) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (j k a : Fin n) (p : E × E) :
    Integrable (fun t : E ↦ imageBesselKernel t *
      fderiv ℝ (fixedMixedSourceKernel hR A j k) (p.1 - t, p.2)
        (EuclideanSpace.single a 1, 0)) := by
  obtain ⟨hc, hs⟩ := mixedSource_derivative_regular hR hcell A j k a
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  exact integrable_imageBesselKernel.mul_bdd
    (hc.comp ((continuous_const.sub continuous_id).prodMk continuous_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ hC (p.1 - t, p.2))

/-- Joint continuity is obtained directly from the compact source derivative
and the integrable Bessel kernel. No regularity premise on the mixed entry is
used. Consumer: the mixed kernel action and its Hilbert adjoint in
`app:ch_background:prop:bg-frame`. -/
theorem continuous_mixedEntry (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Continuous (fixedMixedKernelEntry hR A i j) := by
  unfold fixedMixedKernelEntry
  apply ((FixedCutoffs.physical hR 1).continuous.comp continuous_fst).mul
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro k _
  apply continuous_const.mul
  obtain ⟨hc, hs⟩ := mixedSource_derivative_regular hR hcell A j k a
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  apply continuous_of_dominated (bound := fun t : E ↦ ‖imageBesselKernel t‖ * C)
  · intro p
    exact measurable_imageBesselKernel.aestronglyMeasurable.mul
      (hc.comp ((continuous_const.sub continuous_id).prodMk continuous_const)).aestronglyMeasurable
  · intro p
    exact Filter.Eventually.of_forall fun t ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC (p.1 - t, p.2)) (norm_nonneg _)
  · exact integrable_imageBesselKernel.norm.mul_const C
  · exact Filter.Eventually.of_forall fun t ↦
      continuous_const.mul (hc.comp
        ((continuous_fst.sub continuous_const).prodMk continuous_snd))

end KernelIdentity

/-- Every forward mixed scalar section is absolutely integrable on every
L² input. Consumer: combining the three actual normal terms under one
integral in `app:ch_background:prop:bg-frame`. -/
theorem integrable_fixedMixedKernelEntry_mul_coordinate (hR : 0 < R)
    (hcell : 4 * R < 1 / 2) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (u : R²) (i j : Fin n) (x : E) :
    Integrable (fun y ↦ fixedMixedKernelEntry hR A i j (x, y) * u y j) :=
  KernelIdentity.integrable_entry_mul_coordinate
    (KernelIdentity.continuous_mixedEntry hR hcell A i j)
    (KernelIdentity.hasCompactSupport_mixedEntry hR A i j) u j x

/-- Every reversed, transposed mixed scalar section is absolutely integrable
on every L² input. Consumer: the literal adjoint mixed term of the normal in
`app:ch_background:prop:bg-frame`. -/
theorem integrable_fixedMixedKernelEntry_swap_mul_coordinate (hR : 0 < R)
    (hcell : 4 * R < 1 / 2) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (u : R²) (i j : Fin n) (x : E) :
    Integrable (fun y ↦ fixedMixedKernelEntry hR A j i (y, x) * u y j) :=
  KernelIdentity.integrable_entry_mul_coordinate
    ((KernelIdentity.continuous_mixedEntry hR hcell A j i).comp continuous_swap)
    ((KernelIdentity.hasCompactSupport_mixedEntry hR A j i).comp_homeomorph
      (Homeomorph.prodComm E E)) u j x

/-- The actual mixed double integral has an integrable majorant even for
an arbitrary L² input. Only the fixed measurement support is used to
localize the datum (`app:ch_background:prop:bg-frame`). -/
theorem integrable_fixedMixedSource_bessel_weight (hR : 0 < R)
    (hcell : 4 * R < 1 / 2) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (u : R²) (j k a : Fin n) (x : E) :
    Integrable (fun p : E × E ↦ imageBesselKernel p.1 *
      fderiv ℝ (fixedMixedSourceKernel hR A j k) (x - p.1, p.2)
        (EuclideanSpace.single a 1, 0) * u p.2 j) (volume.prod volume) := by
  let S := tsupport (FixedCutoffs.physical (n := n) hR 1)
  have hS : IsCompact S := (FixedCutoffs.physical hR 1).hasCompactSupport
  have hu := (Lp.memLp u).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
  have huc : Integrable (S.indicator (fun y ↦ u y j)) :=
    (hu.locallyIntegrable (by norm_num)).integrableOn_isCompact hS
      |>.integrable_indicator hS.measurableSet
  obtain ⟨hc, hs⟩ := KernelIdentity.mixedSource_derivative_regular hR hcell A j k a
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  apply ((integrable_imageBesselKernel.norm.mul_const C).mul_prod huc.norm).mono'
  · exact (measurable_imageBesselKernel.aestronglyMeasurable.comp_fst.mul
      (hc.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)).aestronglyMeasurable).mul
      hu.aestronglyMeasurable.comp_snd
  · apply Filter.Eventually.of_forall
    rintro ⟨t, y⟩
    by_cases hy : y ∈ S
    · simp only [Set.indicator_of_mem hy, norm_mul]
      gcongr
      exact hC (x - t, y)
    · simp [KernelIdentity.mixedSource_fderiv_eq_zero hR A j k (x - t) y hy,
        Set.indicator_of_notMem hy]

/-- Fubini transfers the compact source derivative through the Bessel
integral against an arbitrary L² datum. This is the mixed-kernel contraction
needed to identify `B D*` in `app:ch_background:prop:bg-frame`. -/
theorem integral_fixedMixedSource_bessel_contraction (hR : 0 < R)
    (hcell : 4 * R < 1 / 2) (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (u : R²) (j k a : Fin n) (x : E) :
    (∫ t, imageBesselKernel t * ∫ y,
      fderiv ℝ (fixedMixedSourceKernel hR A j k) (x - t, y)
        (EuclideanSpace.single a 1, 0) * u y j) =
      ∫ y, (∫ t, imageBesselKernel t *
        fderiv ℝ (fixedMixedSourceKernel hR A j k) (x - t, y)
          (EuclideanSpace.single a 1, 0)) * u y j := by
  calc
    _ = ∫ t, ∫ y, imageBesselKernel t *
        fderiv ℝ (fixedMixedSourceKernel hR A j k) (x - t, y)
          (EuclideanSpace.single a 1, 0) * u y j := by
      simp only [integral_const_mul, mul_assoc]
    _ = ∫ y, ∫ t, imageBesselKernel t *
        fderiv ℝ (fixedMixedSourceKernel hR A j k) (x - t, y)
          (EuclideanSpace.single a 1, 0) * u y j :=
      integral_integral_swap (integrable_fixedMixedSource_bessel_weight hR hcell A u j k a x)
    _ = _ := by simp only [integral_mul_const]

end JanetCartan.ContinuumNormal.FrozenImageComparison
