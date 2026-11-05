module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Operators

/-!
# Transverse operations commute with parameter Fourier transformation

The initial norm in `app:ch_background:prop:bg-adjoint` includes all carrier
parameters. Bounded transverse operators commute with the Hilbert-valued
parameter Fourier transform. This includes bounded frequency multipliers,
and hence the truncated weights used for transverse weighted norm control.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
namespace JanetCartan.CarrierSobolev
open ContinuumRow
variable {n : ℕ}

private theorem fourier_compLp_of_integrable
    (L : TransverseL2 n →L[ℂ] TransverseL2 n)
    (f : Lp (TransverseL2 n) 2 (volume : Measure ParameterSpace))
    (hf : Integrable (f : ParameterSpace → TransverseL2 n)) :
    𝓕 (L.compLp f) = L.compLp (𝓕 f) := by
  have hL : Integrable (L.compLp f : ParameterSpace → TransverseL2 n) :=
    (L.integrable_comp hf).congr (Filter.EventuallyEq.symm (L.coeFn_compLp f))
  apply Lp.ext
  filter_upwards [Localization.fourierTransform_coeFn_ae_integral_hilbert _ hL,
    L.coeFn_compLp (𝓕 f), Localization.fourierTransform_coeFn_ae_integral_hilbert f hf]
    with ξ h₁ h₂ h₃
  rw [h₁, Real.fourier_congr_ae (L.coeFn_compLp f) ξ, h₂, h₃]
  simp only [Real.fourier_eq, Circle.smul_def, ← L.map_smul]
  exact L.integral_comp_comm ((Real.fourierIntegral_convergent_iff ξ).mpr hf)

/-- Hilbert-valued Fourier transformation in the parameter coordinates
commutes with every bounded linear operation on the transverse L² fiber.
This supplies bounded transverse multiplier compatibility for
`app:ch_background:prop:bg-adjoint`. -/
theorem parameterL2Fourier_compLp (L : TransverseL2 n →L[ℂ] TransverseL2 n)
    (f : Lp (TransverseL2 n) 2 (volume : Measure ParameterSpace)) :
    𝓕 (L.compLp f) = L.compLp (𝓕 f) := by
  apply DenseRange.induction_on
    (p := fun f : Lp (TransverseL2 n) 2 (volume : Measure ParameterSpace) =>
      𝓕 (L.compLp f) = L.compLp (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (E := ParameterSpace) (F := TransverseL2 n)
      (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      (continuous_fourier.comp (L.compLpL 2 volume).continuous)
      ((L.compLpL 2 volume).continuous.comp continuous_fourier)
  intro g
  exact fourier_compLp_of_integrable L _ (g.integrable.congr (g.coeFn_toLp 2).symm)

/-- The parameter-coordinate identification commutes with bounded transverse
operations (`app:ch_background:prop:bg-adjoint`). -/
theorem parameterL2Equiv_compLp (L : TransverseL2 n →L[ℂ] TransverseL2 n)
    (f : IteratedCarrierL2 n) :
    parameterL2Equiv n (L.compLp f) = L.compLp (parameterL2Equiv n f) := by
  have he := parameterOfLp_measurePreserving.quasiMeasurePreserving.ae
    (L.coeFn_compLp f)
  apply Lp.ext
  filter_upwards [parameterL2Equiv_coeFn (L.compLp f),
    L.coeFn_compLp (parameterL2Equiv n f), parameterL2Equiv_coeFn f, he]
    with z h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃]
  exact h₄

/-- The inverse parameter-coordinate identification also commutes with every
bounded transverse operator (`app:ch_background:prop:bg-adjoint`). -/
theorem parameterL2Equiv_symm_compLp (L : TransverseL2 n →L[ℂ] TransverseL2 n)
    (f : Lp (TransverseL2 n) 2 (volume : Measure ParameterSpace)) :
    (parameterL2Equiv n).symm (L.compLp f) = L.compLp ((parameterL2Equiv n).symm f) := by
  apply (parameterL2Equiv n).injective
  exact ((parameterL2Equiv n).apply_symm_apply (L.compLp f)).trans
    ((parameterL2Equiv_compLp L ((parameterL2Equiv n).symm f)).trans
      (congrArg L.compLp ((parameterL2Equiv n).apply_symm_apply f))).symm

/-- Parameter Fourier transformation commutes with every bounded transverse
operator on the literal iterated carrier space. The transverse multiplier
estimates in `app:ch_background:prop:bg-adjoint` consume this identity. -/
theorem iteratedParameterFourier_compLp (L : TransverseL2 n →L[ℂ] TransverseL2 n)
    (f : IteratedCarrierL2 n) :
    iteratedParameterFourier n (L.compLp f) = L.compLp (iteratedParameterFourier n f) := by
  change (parameterL2Equiv n).symm (𝓕 (parameterL2Equiv n (L.compLp f))) = _
  exact (congrArg (fun g : Lp (TransverseL2 n) 2 (volume : Measure ParameterSpace) =>
    (parameterL2Equiv n).symm (𝓕 g)) (parameterL2Equiv_compLp L f)).trans
      ((congrArg (parameterL2Equiv n).symm
        (parameterL2Fourier_compLp L (parameterL2Equiv n f))).trans
          (parameterL2Equiv_symm_compLp L (𝓕 (parameterL2Equiv n f))))

/-- Plancherel after any bounded transverse operation, in particular a
bounded frequency weight. This is the norm input for truncating unbounded
η-weights in `app:ch_background:prop:bg-adjoint`. -/
theorem iteratedParameterFourier_compLp_norm (L : TransverseL2 n →L[ℂ] TransverseL2 n)
    (f : IteratedCarrierL2 n) :
    ‖L.compLp (iteratedParameterFourier n f)‖ = ‖L.compLp f‖ := by
  rw [← iteratedParameterFourier_compLp (n := n) L f]
  exact (iteratedParameterFourier n).norm_map _

/-- The transverse and parameter Fourier factors, and likewise the
normalization dilation, commute on all iterated carrier L² data
(`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedParameterFourier_transverseEquiv
    (U : TransverseL2 n ≃ₗᵢ[ℂ] TransverseL2 n) (f : IteratedCarrierL2 n) :
    iteratedParameterFourier n (iteratedTransverseEquiv U f) =
      iteratedTransverseEquiv U (iteratedParameterFourier n f) :=
  iteratedParameterFourier_compLp U.toContinuousLinearEquiv.toContinuousLinearMap f

/-- The inverse transverse dilation commutes with parameter Fourier
transformation, allowing the exact frequency rescaling to be read after the
full Fourier factorization (`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedParameterFourier_dilation_symm (f : IteratedCarrierL2 n) :
    iteratedParameterFourier n ((iteratedTransverseDilation n).symm f) =
      (iteratedTransverseDilation n).symm (iteratedParameterFourier n f) :=
  iteratedParameterFourier_compLp
    (transverseDilation n ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap f

end JanetCartan.CarrierSobolev
