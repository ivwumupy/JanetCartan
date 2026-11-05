module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputComparison.CoordinateTests
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.HilbertPlancherel.Directional
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.HilbertPlancherel.Coordinates

/-!
# Fourier multipliers of compact carrier coordinate derivatives

The coordinate derivatives in the reverse input comparison for
`app:ch_background:prop:bg-adjoint` and `app:ch_background:eq:bg-density-adjoint`
are differentiated as actual transverse L²-valued compact smooth sections.
This supplies the parameter multiplier used by the full raw Sobolev estimate.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace ContDiff
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- The exact unit-period parameter Fourier symbol of the chosen coordinate
jet, consumed by `norm_rawTestSobolev_inputCoordinateTest_le` for
`app:ch_background:eq:bg-density-adjoint`. -/
def inputCoordinateSymbol {k : ℕ} (a : Fin k → (Unit ⊕ Fin 2))
    (z : CarrierParameter) : ℂ :=
  (-(2 * Real.pi * Complex.I)) ^ k *
    ((∏ j, -inner ℝ (WithLp.toLp 2 z) (WithLp.toLp 2 (inputCarrierBasis (a j)))) : ℝ)

/-- The scalar compact coordinate derivative represents the evaluated
Hilbert-valued section derivative. This is the differentiation input to
`app:ch_background:prop:bg-adjoint`. -/
theorem carrierTestSlice_inputCoordinateTest (k : ℕ) (f : carrierInitialTestSpace n)
    (a : Fin k → (Unit ⊕ Fin 2)) (z : CarrierParameter) :
    Fubini.slice (inputCoordinateTest k f a).val z =
      iteratedFDeriv ℝ k (Fubini.slice f.val) z (fun j => inputCarrierBasis (a j)) := by
  apply Lp.ext
  filter_upwards [Fubini.slice_coeFn
    (carrier_memLp_slice_of_continuous_hasCompactSupport
      (inputCoordinateTest k f a).property.1.continuous
      (inputCoordinateTest k f a).property.2 z),
    iteratedFDeriv_carrierTestSlice_coeFn f k z (fun j => inputCarrierBasis (a j))]
      with η hη hd
  exact hη.trans ((inputCoordinateTest_eq_carrierDerivative k f a (z, η)).trans hd.symm)

set_option maxHeartbeats 800000 in
/-- Parameter Fourier differentiation of the actual compact section retains
the exact `2π` multiplier. This identity supplies the full Fourier multiplier
in `app:ch_background:eq:bg-density-adjoint`. -/
theorem fourier_carrierTestSlice_inputCoordinateTest (k : ℕ)
    (f : carrierInitialTestSpace n) (a : Fin k → (Unit ⊕ Fin 2)) (z : CarrierParameter) :
    𝓕 (fun w : ParameterSpace => Fubini.slice (inputCoordinateTest k f a).val
      (WithLp.ofLp w)) (WithLp.toLp 2 z) =
      inputCoordinateSymbol a z •
        𝓕 (fun w : ParameterSpace => Fubini.slice f.val (WithLp.ofLp w))
          (WithLp.toLp 2 z) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean 2)
  let L := e.toContinuousLinearMap
  let φ : ParameterSpace → TransverseL2 n := fun w => Fubini.slice f.val (WithLp.ofLp w)
  let v : Fin k → ParameterSpace := fun j => WithLp.toLp 2 (inputCarrierBasis (a j))
  have hφ : ContDiff ℝ ∞ φ := (contDiff_carrierTestSlice f).comp e.contDiff
  have hc : HasCompactSupport φ :=
    (hasCompactSupport_carrierTestSlice f).comp_homeomorph e.toHomeomorph
  have hi (j : ℕ) : Integrable (iteratedFDeriv ℝ j φ) :=
    (hφ.continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport
      (hc.iteratedFDeriv j)
  have hd : (fun w : ParameterSpace => Fubini.slice (inputCoordinateTest k f a).val
      (WithLp.ofLp w)) = fun w => iteratedFDeriv ℝ k φ w v := by
    funext w
    rw [carrierTestSlice_inputCoordinateTest]
    have he := L.iteratedFDeriv_comp_right (contDiff_carrierTestSlice f) w
      (i := k) (by simp)
    exact (congrArg (fun A => A v) he).symm
  rw [hd]
  have ha : 𝓕 (iteratedFDeriv ℝ k φ) (WithLp.toLp 2 z) v =
      𝓕 (fun w => iteratedFDeriv ℝ k φ w v) (WithLp.toLp 2 z) := by
    convert! Real.fourier_continuousMultilinearMap_apply
      (m := v) (v := WithLp.toLp 2 z) (hi k) using 1
  have hf : 𝓕 (iteratedFDeriv ℝ k φ) =
      (fun w => VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 φ) w k) := by
    convert! Real.fourier_iteratedFDeriv hφ (fun j _ => hi j) (n := k) (by simp) using 1
  rw [← ha, hf]
  have hp := VectorFourier.fourierPowSMulRight_apply
    (L := -innerSL ℝ) (f := 𝓕 φ) (v := WithLp.toLp 2 z) (m := v)
  calc
    _ = (-(2 * Real.pi * Complex.I)) ^ k •
        (∏ j, -inner ℝ (WithLp.toLp 2 z) (v j)) • 𝓕 φ (WithLp.toLp 2 z) := by
      convert! hp using 1
    _ = _ := by
      simp only [inputCoordinateSymbol, v, mul_smul, Complex.coe_smul]
      rfl

set_option maxHeartbeats 800000 in
/-- The actual iterated parameter Fourier operator has the coordinate
multiplier on the literal product measure. This is consumed by the full
Fourier comparison for `app:ch_background:prop:bg-adjoint`. -/
theorem iteratedParameterFourier_inputCoordinateTest (k : ℕ)
    (f : carrierInitialTestSpace n) (a : Fin k → (Unit ⊕ Fin 2)) :
    iteratedParameterFourier n (carrierFubiniEquiv n
      (carrierInitialTestToLp (inputCoordinateTest k f a))) =ᵐ[volume.prod volume]
      fun z => inputCoordinateSymbol a z •
        iteratedParameterFourier n (carrierFubiniEquiv n (carrierInitialTestToLp f)) z := by
  have he (g : carrierInitialTestSpace n) :=
    iteratedParameterFourier_coeFn_compact (carrierFubiniEquiv n (carrierInitialTestToLp g))
      (Fubini.slice g.val) (contDiff_carrierTestSlice g).continuous
      (hasCompactSupport_carrierTestSlice g) (carrierFubiniEquiv_test_eq_slice g)
  filter_upwards [he (inputCoordinateTest k f a), he f] with z hd hf
  rw [hd, hf]
  exact fourier_carrierTestSlice_inputCoordinateTest k f a z

end JanetCartan.ContinuumAdjoint.DensityMultiplier
