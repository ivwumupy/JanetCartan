module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzTests

/-!
# Objects for the unit-period partial Schwartz transform

The construction for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint` first takes the full Fourier
transform of a compact physical test, then inverts only its three parameter
frequencies. The final consumer is `exists_unitPeriodSchwartz_compactSmooth`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap RealInnerProductSpace ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

variable {n : ℕ}

/-- A compact physical test in the shared Hilbert coordinates. Its full
Schwartz Fourier transform is the input to the parameter inversion step of
`app:ch_background:eq:bg-density-adjoint`. -/
def unitPeriodPhysicalSchwartz (φ : carrierInitialTestSpace n) :
    𝓢(InitialSpace n, ℂ) :=
  (φ.property.2.comp_homeomorph (initialCoordinatesLinear n).symm.toHomeomorph).toSchwartzMap (φ.property.1.comp (initialCoordinatesLinear n).symm.contDiff)

/-- The physical Schwartz function retains the literal compact test
(`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem unitPeriodPhysicalSchwartz_apply (φ : carrierInitialTestSpace n)
    (p : CarrierVariable n) :
    unitPeriodPhysicalSchwartz φ (initialCoordinatesLinear n p) = φ.val p := by
  exact congrArg φ.val ((initialCoordinatesLinear n).symm_apply_apply p)

/-- Restrict a Schwartz function to a parameter-frequency slice. This
supplies integrability for ordinary Fourier inversion in the three parameter
coordinates (`app:ch_background:prop:bg-adjoint`). -/
def unitPeriodParameterSlice (f : 𝓢(InitialSpace n, ℂ)) (η : Euclidean (n - 1)) :
    𝓢(ParameterSpace, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (K := 1)
    (g := fun z : ParameterSpace ↦ (z, η))
    (by
      have h := (ContinuousLinearMap.inl ℝ ParameterSpace (Euclidean (n - 1))).hasTemperateGrowth
      convert h.add (by fun_prop : Function.HasTemperateGrowth
        (fun _ : ParameterSpace ↦ ((0 : ParameterSpace), η))) using 1
      funext z
      simp only [Pi.add_apply, ContinuousLinearMap.inl_apply,
        Prod.mk_add_mk, add_zero, zero_add])
    (show Isometry (fun z : ParameterSpace ↦ (z, η)) from
      fun x y ↦ by simp [Prod.edist_eq]).antilipschitzWith
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (WithLp.prodContinuousLinearEquiv 2 ℝ ParameterSpace (Euclidean (n - 1))).symm f)

/-- The parameter slice evaluates at the actual product coordinates
(`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem unitPeriodParameterSlice_apply (f : 𝓢(InitialSpace n, ℂ))
    (η : Euclidean (n - 1)) (z : ParameterSpace) :
    unitPeriodParameterSlice f η z = f (WithLp.toLp 2 (z, η)) := rfl

/-- The literal transverse unit-period Fourier integral, before proving
joint Schwartz decay (`app:ch_background:eq:bg-density-adjoint`). -/
def unitPeriodPartialIntegral (φ : carrierInitialTestSpace n) (x : InitialSpace n) : ℂ :=
  𝓕 (fun y ↦ unitPeriodPhysicalSchwartz φ (WithLp.toLp 2 (x.fst, y))) x.snd

/-- The partial integral uses the original transverse variable and its
ordinary Lebesgue measure (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem unitPeriodPartialIntegral_apply (φ : carrierInitialTestSpace n)
    (p : CarrierVariable n) :
    unitPeriodPartialIntegral φ (initialCoordinatesLinear n p) =
      𝓕 (fun y ↦ φ.val (p.1, y)) p.2 := rfl

/-- Concrete oscillatory kernel for the compactly cut off parameter inverse.
Its Schwartz property and integration over the second factor are independent
analytic obligations in `exists_unitPeriodSchwartz_compactSmooth`
(`app:ch_background:eq:bg-density-adjoint`). -/
def unitPeriodCutoffKernel (χ : 𝓢(ParameterSpace, ℂ)) (f : 𝓢(InitialSpace n, ℂ))
    (p : InitialSpace n × ParameterSpace) : ℂ :=
  χ p.1.fst * (Real.fourierChar ⟪p.2, p.1.fst⟫ : ℂ) *
    f (WithLp.toLp 2 (p.2, p.1.snd))

/-- The kernel integral is exactly the cut off inverse parameter transform;
no Schwartz-preservation assertion is used in this identity
(`app:ch_background:prop:bg-adjoint`). -/
theorem integral_unitPeriodCutoffKernel (χ : 𝓢(ParameterSpace, ℂ))
    (f : 𝓢(InitialSpace n, ℂ)) (x : InitialSpace n) :
    (∫ z : ParameterSpace, unitPeriodCutoffKernel χ f (x, z)) =
      χ x.fst * 𝓕⁻ (unitPeriodParameterSlice f x.snd) x.fst := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [unitPeriodCutoffKernel, unitPeriodParameterSlice_apply,
    Circle.smul_def, smul_eq_mul, mul_assoc]

end JanetCartan.ContinuumAdjoint.DensityMultiplier
