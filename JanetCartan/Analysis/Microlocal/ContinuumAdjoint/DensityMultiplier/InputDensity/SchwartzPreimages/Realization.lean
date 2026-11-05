module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzTests

/-!
# Literal L² realization of Schwartz partial Fourier preimages

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, a Schwartz representative of the
unit-period partial Fourier integral gives a preimage under the actual radian
partial unitary inverse. This file proves the normalization and literal L²
identification. The joint Schwartz representative of that integral is a separate
construction, still required to obtain the unconditional preimage theorem.

The exact consumer is `exists_rawSchwartz_preimage_compactSmooth`, which in turn
supplies `hpreimage` to `denseRange_rawTestSobolev_of_schwartz`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter
open scoped SchwartzMap

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

variable {n : ℕ}

/-- Transverse radian-to-unit-period coordinate rescaling for
`rawRadianRescaleSchwartz` (`app:ch_background:prop:bg-adjoint`). -/
def rawTransverseRescale (n : ℕ) : CarrierVariable n ≃L[ℝ] CarrierVariable n where
  toFun p := (p.1, (2 * Real.pi)⁻¹ • p.2)
  invFun p := (p.1, (2 * Real.pi) • p.2)
  left_inv p := by
    simp only [smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
      one_smul, Prod.mk.eta]
  right_inv p := by
    simp only [smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
      one_smul, Prod.mk.eta]
  map_add' p q := by simp [smul_add]
  map_smul' c p := by simp [smul_comm c]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Convert a unit-period Schwartz partial transform into the unitary radian
representative for `app:ch_background:prop:bg-adjoint`. The coordinate change
fixes all three carrier parameters and rescales only the `n - 1` transverse
coordinates; it also applies when that dimension is zero. -/
def rawRadianRescaleSchwartz (f : 𝓢(DensityEuclidean n, ℂ)) :
    𝓢(DensityEuclidean n, ℂ) :=
  (synthesisFactor n)⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (((densityCoordinates n).symm.trans (rawTransverseRescale n)).trans
      (densityCoordinates n)) f

/-- The exact amplitude and coordinate formula consumed by the literal L²
preimage identification (`app:ch_background:prop:bg-adjoint`). -/
theorem rawRadianRescaleSchwartz_apply (f : 𝓢(DensityEuclidean n, ℂ))
    (p : CarrierVariable n) :
    rawRadianRescaleSchwartz f (densityCoordinates n p) =
      (synthesisFactor n)⁻¹ • f (densityCoordinates n (p.1, (2 * Real.pi)⁻¹ • p.2)) := by
  simp [rawRadianRescaleSchwartz, rawTransverseRescale]

/-- The existing partial L² Fourier operator has the ordinary fiberwise
Fourier integral representative on compact physical tests. This identifies
the physical side of `exists_rawSchwartz_preimage_compactSmooth`
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem partialFourier_compactSmooth_coeFn (φ : carrierInitialTestSpace n) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun η ↦ partialFourier n (carrierInitialTestToLp φ) (z, η)) =ᵐ[volume]
        𝓕 (fun y ↦ φ.val (z, y)) := by
  filter_upwards [carrierFubiniEquiv_symm_coeFn n
      (iteratedTransverseFourier n (carrierFubiniEquiv n (carrierInitialTestToLp φ))),
    iteratedTransverseFourier_coeFn (carrierFubiniEquiv n (carrierInitialTestToLp φ)),
    carrierFubiniEquiv_toLp_coeFn (carrierInitialTest_memLp φ)] with z hz ht hφ
  have hi : Integrable (fun y ↦ φ.val (z, y)) volume := by
    apply (φ.property.1.continuous.comp
      (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact (φ.property.2.image continuous_snd)
    intro y hy
    exact ⟨(z, y), subset_tsupport φ.val hy, rfl⟩
  have hf := Localization.fourierTransform_coeFn_ae_integral_hilbert
    ((carrierFubiniEquiv n (carrierInitialTestToLp φ)) z) (hi.congr hφ.symm)
  change (fun η ↦ partialFourier n (carrierInitialTestToLp φ) (z, η)) =ᵐ[volume]
    (iteratedTransverseFourier n (carrierFubiniEquiv n (carrierInitialTestToLp φ))) z at hz
  rw [ht] at hz
  exact hz.trans (hf.trans (Filter.Eventually.of_forall fun η ↦
    Real.fourier_congr_ae hφ η))

/-- Radian rescaling followed by partial unitary synthesis has precisely the
original unit-period partial Fourier class, for every Schwartz function.
This unconditional normalization identity is used in the preimage construction
for `app:ch_background:eq:bg-density-adjoint`. -/
theorem partialFourier_partialUnitaryInverse_rawRadianRescaleSchwartz
    (f : 𝓢(DensityEuclidean n, ℂ)) :
    partialFourier n (partialUnitaryInverse n
      (rawSchwartzToL2 n (rawRadianRescaleSchwartz f))) = rawSchwartzToL2 n f := by
  apply Lp.ext
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      (Lp.stronglyMeasurable _).measurable)).mpr
  filter_upwards [partialFourier_partialUnitaryInverse_coeFn
      (rawSchwartzToL2 n (rawRadianRescaleSchwartz f)),
    Measure.ae_ae_of_ae_prod (rawSchwartzToL2_coeFn (rawRadianRescaleSchwartz f)),
    Measure.ae_ae_of_ae_prod (rawSchwartzToL2_coeFn f)] with z hz hd hf
  have hd' := (Measure.quasiMeasurePreserving_smul
    (volume : Measure (Euclidean (n - 1)))
    (by positivity : (2 * Real.pi : ℝ) ≠ 0)).ae hd
  filter_upwards [hz, hd', hf] with η hη hdη hfη
  rw [hη, hfη, hdη]
  change synthesisFactor n • rawRadianRescaleSchwartz f
    (densityCoordinates n (z, (2 * Real.pi) • η)) = f (densityCoordinates n (z, η))
  rw [rawRadianRescaleSchwartz_apply]
  simp only [smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    mul_inv_cancel₀ (ne_of_gt (synthesisFactor_pos n)), one_smul]

/-- A constructed Schwartz representative of the ordinary unit-period
partial Fourier integral yields an actual radian L² preimage. The hypothesis
`hf` must be supplied by the joint Schwartz construction before this closes
`exists_rawSchwartz_preimage_compactSmooth`; this lemma alone does not assert
that partial Fourier transformation preserves Schwartz functions
(`app:ch_background:prop:bg-adjoint`; `app:ch_background:eq:bg-density-adjoint`). -/
theorem rawSchwartz_preimage_compactSmooth_of_unitPeriod
    (φ : carrierInitialTestSpace n) (f : 𝓢(DensityEuclidean n, ℂ))
    (hf : ∀ p : CarrierVariable n,
      f (densityCoordinates n p) = 𝓕 (fun y ↦ φ.val (p.1, y)) p.2) :
    partialUnitaryInverse n (rawSchwartzToL2 n (rawRadianRescaleSchwartz f)) =
      carrierInitialTestToLp φ := by
  apply (partialFourier n).injective
  rw [partialFourier_partialUnitaryInverse_rawRadianRescaleSchwartz]
  apply Lp.ext
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      (Lp.stronglyMeasurable _).measurable)).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod (rawSchwartzToL2_coeFn f),
    partialFourier_compactSmooth_coeFn φ] with z hz hφ
  filter_upwards [hz, hφ] with η hη hφη
  exact hη.trans ((hf (z, η)).trans hφη.symm)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
