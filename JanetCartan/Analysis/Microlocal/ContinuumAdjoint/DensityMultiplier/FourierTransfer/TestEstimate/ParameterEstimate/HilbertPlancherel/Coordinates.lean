module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.WeightTransfer

/-!
# Parameter jets under the Hilbert coordinate change

For `app:ch_background:prop:bg-adjoint`, passing from the literal carrier
product to its Hilbert norm preserves measure and does not increase the
operator norm of any parameter derivative. No transverse derivative occurs.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- The parameter-coordinate pullback contracts each derivative's L² norm.
This is the coordinate comparison consumed by the parameter Plancherel
estimate for `app:ch_background:eq:bg-density-adjoint`. -/
theorem lpNorm_parameterSection_iteratedFDeriv_le
    (φ : CarrierParameter → TransverseL2 n) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (k : ℕ) :
    lpNorm (iteratedFDeriv ℝ k (fun z : ParameterSpace => φ (WithLp.ofLp z))) 2 volume ≤
      lpNorm (iteratedFDeriv ℝ k φ) 2 (volume.prod volume) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean 2)
  let L := e.toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro z
    change ‖WithLp.ofLp z‖ ≤ 1 * ‖z‖
    simpa only [Prod.norm_def, one_mul, WithLp.fst, WithLp.snd] using
      max_le (WithLp.norm_fst_le ℝ z) (WithLp.norm_snd_le ℝ z)
  have hm : MemLp (iteratedFDeriv ℝ k φ) 2 (volume.prod volume) :=
    (hφ.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
      (hc.iteratedFDeriv k)
  have hmc := hm.norm.comp_measurePreserving parameterOfLp_measurePreserving
  have hb (z : ParameterSpace) :
      ‖iteratedFDeriv ℝ k (φ ∘ L) z‖ ≤ ‖iteratedFDeriv ℝ k φ (WithLp.ofLp z)‖ := by
    rw [L.iteratedFDeriv_comp_right hφ z (by simp)]
    apply ((iteratedFDeriv ℝ k φ (L z)).norm_compContinuousLinearMap_le _).trans
    simpa [L, e] using mul_le_of_le_one_right
      (norm_nonneg (iteratedFDeriv ℝ k φ (L z)))
      (pow_le_one₀ (norm_nonneg L) hL : ‖L‖ ^ k ≤ 1)
  calc
    _ ≤ lpNorm ((fun z => ‖iteratedFDeriv ℝ k φ z‖) ∘
        (MeasurableEquiv.toLp 2 CarrierParameter).symm) 2 volume :=
      lpNorm_mono_real hmc hb
    _ = lpNorm (fun z => ‖iteratedFDeriv ℝ k φ z‖) 2 (volume.prod volume) := by
      exact congrArg ENNReal.toReal
        (eLpNorm_comp_measurePreserving hm.norm.aestronglyMeasurable
          parameterOfLp_measurePreserving)
    _ = _ := lpNorm_norm hm.aestronglyMeasurable _

/-- The compact smooth section supplies an ordinary integral representative
of the actual iterated parameter Fourier transform. This identifies the
analytic weighted estimate with the operator used in
`app:ch_background:prop:bg-adjoint`. -/
theorem iteratedParameterFourier_coeFn_compact
    (g : IteratedCarrierL2 n) (φ : CarrierParameter → TransverseL2 n)
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hg : g =ᵐ[volume.prod volume] φ) :
    iteratedParameterFourier n g =ᵐ[volume.prod volume]
      fun z => 𝓕 (fun w : ParameterSpace => φ (WithLp.ofLp w)) (WithLp.toLp 2 z) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean 2)
  let ψ : ParameterSpace → TransverseL2 n := φ ∘ e
  have hi : Integrable ψ :=
    (hφ.comp e.continuous).integrable_of_hasCompactSupport
      (hc.comp_homeomorph e.toHomeomorph)
  have he : parameterL2Equiv n g =ᵐ[volume] ψ :=
    (parameterL2Equiv_coeFn g).trans (parameterOfLp_measurePreserving.quasiMeasurePreserving.ae hg)
  have hF : (𝓕 (parameterL2Equiv n g) : Lp (TransverseL2 n) 2 volume)
      =ᵐ[volume] 𝓕 ψ :=
    (Localization.fourierTransform_coeFn_ae_integral_hilbert _
      (hi.congr he.symm)).trans (.of_forall (Real.fourier_congr_ae he))
  exact (parameterL2Equiv_symm_coeFn (𝓕 (parameterL2Equiv n g))).trans
    (parameterToLp_measurePreserving.quasiMeasurePreserving.ae hF)

/-- The literal initial weight restricted to carrier parameters is precisely
its Hilbert radial expression, including the `2π` normalization in
`app:ch_background:eq:bg-density-adjoint`. -/
theorem initialWeight_parameter_eq_sqrt (s : ℕ) (z : CarrierParameter) :
    initialWeight s (z, (0 : Euclidean (n - 1))) =
      Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2) ^ s := by
  rw [initialWeight_eq_coordinates]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rw [Real.rpow_div_two_eq_sqrt _ (by positivity), Real.rpow_natCast]
  rfl

/-- Transfer a weighted ordinary parameter Fourier integral to the actual
operator on the literal product measure, with equality of norms. The
weighted membership premise must come from the radial Hilbert Plancherel
estimate; this coordinate step alone does not prove the estimate in
`app:ch_background:eq:bg-density-adjoint`. -/
theorem parameterWeight_fourierIntegral_compact (s : ℕ)
    (g : IteratedCarrierL2 n) (φ : CarrierParameter → TransverseL2 n)
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hg : g =ᵐ[volume.prod volume] φ)
    (hm : MemLp (fun ξ : ParameterSpace =>
      Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ^ s •
        𝓕 (fun w : ParameterSpace => φ (WithLp.ofLp w)) ξ) 2 volume) :
    MemLp (fun z => initialWeight s (z, (0 : Euclidean (n - 1))) •
      iteratedParameterFourier n g z) 2 (volume.prod volume) ∧
    lpNorm (fun z => initialWeight s (z, (0 : Euclidean (n - 1))) •
      iteratedParameterFourier n g z) 2 (volume.prod volume) =
      lpNorm (fun ξ : ParameterSpace =>
        Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ^ s •
          𝓕 (fun w : ParameterSpace => φ (WithLp.ofLp w)) ξ) 2 volume := by
  let F : ParameterSpace → TransverseL2 n := fun ξ =>
    Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ^ s •
      𝓕 (fun w : ParameterSpace => φ (WithLp.ofLp w)) ξ
  have he : (fun z => initialWeight s (z, (0 : Euclidean (n - 1))) •
      iteratedParameterFourier n g z) =ᵐ[volume.prod volume]
        F ∘ (MeasurableEquiv.toLp 2 CarrierParameter) := by
    filter_upwards [iteratedParameterFourier_coeFn_compact g φ hφ hc hg] with z hz
    rw [hz, initialWeight_parameter_eq_sqrt]
    rfl
  refine ⟨(hm.comp_measurePreserving parameterToLp_measurePreserving).ae_eq he.symm, ?_⟩
  exact congrArg ENNReal.toReal ((eLpNorm_congr_ae he).trans
    (eLpNorm_comp_measurePreserving hm.aestronglyMeasurable parameterToLp_measurePreserving))

end JanetCartan.ContinuumAdjoint.DensityMultiplier
