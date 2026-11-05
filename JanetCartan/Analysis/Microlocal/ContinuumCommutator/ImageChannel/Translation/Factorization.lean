module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Translation.FourierFactors

/-!
# Finite factorization and exact image-channel conjugation

The source and measurement masks and every principal/connection coefficient
of `app:ch_background:defn:bg-row` are retained. These identities feed the
image-normal estimate in `app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannelTranslation

open ContinuumRow MeasureTheory

variable {n : ℕ}

private theorem conjugate_add (a : Torus n) (A B : OutputL2 n →L[ℝ] OutputL2 n) :
    conjugate a (A + B) = conjugate a A + conjugate a B := by
  simp only [conjugate, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

private theorem conjugate_sum {ι : Type*} (s : Finset ι) (a : Torus n)
    (A : ι → OutputL2 n →L[ℝ] OutputL2 n) :
    conjugate a (∑ j ∈ s, A j) = ∑ j ∈ s, conjugate a (A j) := by
  ext1 u
  simp only [conjugate, ContinuousLinearMap.comp_apply, sum_apply, map_sum]

/-- The constant matrix units commute with torus translation
(`app:ch_background:eq:bg-commutator`). -/
theorem conjugate_matrixUnit (a : Torus n) (r s : Fin n) :
    conjugate a ((reducedMatrixUnit r s).compLpL 2 volume) =
      (reducedMatrixUnit r s).compLpL 2 volume := by
  ext1 u
  apply Lp.ext
  filter_upwards [periodicL2Translation_coe a
      ((reducedMatrixUnit r s).compLpL 2 volume (periodicL2Translation (-a) u)),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae
      ((reducedMatrixUnit r s).coeFn_compLpL (periodicL2Translation (-a) u)),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae
      (periodicL2Translation_coe (-a) u),
    (reducedMatrixUnit r s).coeFn_compLpL (μ := volume) (p := 2) u]
      with x ht hm hi hr
  change periodicL2Translation a
    ((reducedMatrixUnit r s).compLpL 2 volume (periodicL2Translation (-a) u)) x = _
  rw [ht, hm, hi, hr]
  simp

/-- Conjugation translates each literal scalar matrix coefficient
(`app:ch_background:eq:bg-commutator`). -/
theorem conjugate_coefficientMultiplier (c : C(Torus n, ℝ)) (a : Torus n)
    (r s : Fin n) :
    conjugate a (reducedCoefficientMultiplier c r s) =
      reducedCoefficientMultiplier (translatedExteriorCutoff c a) r s := by
  rw [reducedCoefficientMultiplier, conjugate_comp, conjugate_matrixUnit]
  exact congrArg ((reducedMatrixUnit r s).compLpL 2 volume ∘L ·)
    (cutoffMultiplier_conjugation c a)

/-- A primitive derivative budget bounds the actual scalar matrix coefficient
commutator (`app:ch_background:eq:bg-commutator`). -/
theorem norm_conjugationDifference_coefficientMultiplier_le
    (c : C(Torus n, ℝ)) (hc : Differentiable ℝ (periodicLift c))
    (r s i : Fin n) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖fderiv ℝ (periodicLift c) x (EuclideanSpace.single i 1)‖ ≤ K)
    (h : ℝ) :
    ‖periodicConjugationDifference (reducedCoefficientMultiplier c r s) i h‖ ≤ K := by
  have hz : periodicConjugationDifference
      ((reducedMatrixUnit r s).compLpL 2 volume) i h = 0 := by
    change h⁻¹ • (conjugate _ _ - _) = 0
    rw [conjugate_matrixUnit, sub_self, smul_zero]
  have hb := norm_conjugationDifference_comp_le
    ((reducedMatrixUnit r s).compLpL 2 volume) (cutoffMultiplier c) i h
  rw [hz, norm_zero, zero_mul, zero_add] at hb
  apply hb.trans
  calc
    _ ≤ 1 * K := mul_le_mul
      ((ContinuousLinearMap.norm_compLpL_le _).trans (reducedMatrixUnit_norm_le r s))
      (norm_periodicConjugationDifference_cutoffMultiplier_le c hc i hK0 hK h)
      (norm_nonneg _) zero_le_one
    _ = K := one_mul _

/-- Finite expansion of the actual reduced/Bessel composition, including all
connection terms (`app:ch_background:defn:bg-row`). -/
theorem reduced_bessel_finite_sum
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)) :
    reducedWeakOperator c ∘L periodicBesselLift =
      (∑ j, ∑ r, ∑ s, reducedCoefficientMultiplier (c (.inl (j, r, s))) r s ∘L
        besselDerivative j) +
      ∑ r, ∑ s, reducedCoefficientMultiplier (c (.inr (r, s))) r s ∘L
        periodicBesselInverse := by
  ext1 u
  simp only [reducedWeakOperator, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    toL2_periodicBesselLift, besselDerivative]

/-- Finite bounded-factor expansion of the PUBLISHED image channel, preserving
both cutoffs (`app:ch_background:defn:bg-row`). -/
theorem imageChannel_finite_sum
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) :
    imageChannel c χmeas χsrc = cutoffMultiplier χmeas ∘L
      ((∑ j, ∑ r, ∑ s, reducedCoefficientMultiplier (c (.inl (j, r, s))) r s ∘L
        besselDerivative j) +
       ∑ r, ∑ s, reducedCoefficientMultiplier (c (.inr (r, s))) r s ∘L
        periodicBesselInverse) ∘L cutoffMultiplier χsrc := by
  rw [← reduced_bessel_finite_sum]
  simp only [imageChannel, ContinuousLinearMap.comp_assoc]

/-- Exact conjugation of the actual reduced/Bessel composition: only the
primitive coefficient array translates (`app:ch_background:eq:bg-commutator`). -/
theorem conjugate_reduced_bessel
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)) (a : Torus n) :
    conjugate a (reducedWeakOperator c ∘L periodicBesselLift) =
      reducedWeakOperator (fun j ↦ translatedExteriorCutoff (c j) a) ∘L
        periodicBesselLift := by
  simp only [reduced_bessel_finite_sum, conjugate_add, conjugate_sum,
    conjugate_comp, conjugate_coefficientMultiplier, conjugate_besselDerivative,
    conjugate_besselInverse]

/-- Exact translation conjugation of the original image channel. The source
and measurement cutoffs translate along with all first/zeroth coefficients
(`app:ch_background:eq:bg-commutator`). -/
theorem conjugate_imageChannel
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (a : Torus n) :
    conjugate a (imageChannel c χmeas χsrc) =
      imageChannel (fun j ↦ translatedExteriorCutoff (c j) a)
        (translatedExteriorCutoff χmeas a) (translatedExteriorCutoff χsrc a) := by
  have hgroup (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
      (m s : C(Torus n, ℝ)) : imageChannel c m s = cutoffMultiplier m ∘L
        (reducedWeakOperator c ∘L periodicBesselLift) ∘L cutoffMultiplier s := by
    simp only [imageChannel, ContinuousLinearMap.comp_assoc]
  simp only [hgroup, conjugate_comp, conjugate_reduced_bessel]
  change _ = _
  rw [show conjugate a (cutoffMultiplier χmeas) =
    cutoffMultiplier (translatedExteriorCutoff χmeas a) from cutoffMultiplier_conjugation _ _,
    show conjugate a (cutoffMultiplier χsrc) =
    cutoffMultiplier (translatedExteriorCutoff χsrc a) from cutoffMultiplier_conjugation _ _]

end JanetCartan.ContinuumCommutator.ImageChannelTranslation
