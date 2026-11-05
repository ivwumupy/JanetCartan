module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputComparison.CoordinateFourier.Weights

/-!
# Raw Sobolev bounds for compact carrier coordinate derivatives

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, the parameter Fourier multiplier
of each compact coordinate derivative passes through the checked partial
radian Fourier factorization. Its absolute value is bounded by the full
initial Bessel weight. The resulting constant-one estimate is consumed by
the reverse mixed-jet input comparison.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- Full Fourier transformation after the actual partial radian synthesis
has the coordinate monomial as multiplier. The exact transverse dilation
commutes with this parameter scalar, including transverse dimension zero.
This supplies `norm_rawTestSobolev_inputCoordinateTest_le` for
`app:ch_background:prop:bg-adjoint`. -/
theorem initialFourier_partialUnitaryInverse_inputCoordinateTest (k : ℕ)
    (f : carrierInitialTestSpace n) (a : Fin k → (Unit ⊕ Fin 2)) :
    initialFourier n (partialUnitaryInverse n
      (carrierInitialTestToLp (inputCoordinateTest k f a))) =ᵐ[carrierMeasure n]
      fun ξ => inputCoordinateSymbol a ξ.1 •
        initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ := by
  let P (g : carrierInitialTestSpace n) :=
    iteratedParameterFourier n (carrierFubiniEquiv n (carrierInitialTestToLp g))
  let D (g : carrierInitialTestSpace n) := (iteratedTransverseDilation n).symm (P g)
  have hd (g : carrierInitialTestSpace n) :
      D g =ᵐ[volume.prod volume] fun z => (transverseDilation n ℂ).symm (P g z) :=
    iteratedTransverseEquiv_symm_coeFn (transverseDilation n ℂ) (P g)
  have he : D (inputCoordinateTest k f a) =ᵐ[volume.prod volume]
      fun z => inputCoordinateSymbol a z • D f z := by
    filter_upwards [hd (inputCoordinateTest k f a), hd f,
      iteratedParameterFourier_inputCoordinateTest k f a] with z hz hf hp
    change P (inputCoordinateTest k f a) z = inputCoordinateSymbol a z • P f z at hp
    rw [hz, hf, hp, map_smul]
  simp only [initialFourier_partialUnitaryInverse]
  change (carrierFubiniEquiv n).symm (D (inputCoordinateTest k f a))
    =ᵐ[carrierMeasure n] fun ξ =>
      inputCoordinateSymbol a ξ.1 • (carrierFubiniEquiv n).symm (D f) ξ
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.stronglyMeasurable _).measurable
    (((measurable_inputCoordinateSymbol a).comp measurable_fst).smul
      (Lp.stronglyMeasurable _).measurable))).mpr
  filter_upwards [carrierFubiniEquiv_symm_coeFn n (D (inputCoordinateTest k f a)),
    carrierFubiniEquiv_symm_coeFn n (D f), he] with z hdz hfz hz
  filter_upwards [hdz, hfz, Lp.coeFn_smul (inputCoordinateSymbol a z) (D f z)]
    with η hdη hfη hsη
  change (carrierFubiniEquiv n).symm (D (inputCoordinateTest k f a)) (z, η) =
    inputCoordinateSymbol a z • (carrierFubiniEquiv n).symm (D f) (z, η)
  rw [hdη, hz]
  exact hsη.trans (congrArg (fun c : ℂ => inputCoordinateSymbol a z • c) hfη.symm)

/-- Every compact carrier coordinate jet costs exactly its order in the
existing full raw Sobolev norm, with constant one. The parent reverse input
comparison sums these bounds over the `3^k` coordinate terms for
`app:ch_background:prop:bg-adjoint` and `app:ch_background:eq:bg-density-adjoint`.
The statement retains all transverse dimensions and the literal product
Lebesgue measure. -/
theorem norm_rawTestSobolev_inputCoordinateTest_le (k t : ℕ)
    (f : carrierInitialTestSpace n) (a : Fin k → (Unit ⊕ Fin 2)) :
    ‖rawTestSobolev t (inputCoordinateTest k f a)‖ ≤ ‖rawTestSobolev (k + t) f‖ := by
  rw [norm_rawTestSobolev, norm_rawTestSobolev]
  unfold rawSobolevNorm physicalSobolevNorm
  apply ENNReal.toReal_mono (carrierInitialTest_memRawSobolev (k + t) f).eLpNorm_ne_top
  apply eLpNorm_mono_ae (aestronglyMeasurable_weightedInitialFourier t _)
  filter_upwards [initialFourier_partialUnitaryInverse_inputCoordinateTest k f a] with ξ hξ
  rw [hξ]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (initialWeight_pos _ _)]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (initialWeight_mul_norm_inputCoordinateSymbol_le t a ξ)
    (norm_nonneg _)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
