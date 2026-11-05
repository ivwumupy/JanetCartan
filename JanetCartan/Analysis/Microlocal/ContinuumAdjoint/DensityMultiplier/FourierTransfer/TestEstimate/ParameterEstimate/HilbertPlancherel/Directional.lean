module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.WeightTransfer
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Directional parameter Plancherel

The parameter estimate for `app:ch_background:eq:bg-density-adjoint` uses
Plancherel on derivatives evaluated on fixed parameter directions. These
remain valued in the transverse Hilbert space, with no transverse derivatives.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace ContDiff
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- Ordinary Hilbert-valued parameter Fourier integrals preserve the numerical
L² norm. This is consumed by directional parameter differentiation in
`app:ch_background:prop:bg-adjoint`. -/
theorem lpNorm_parameterFourierIntegral {f : ParameterSpace → TransverseL2 n}
    (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    lpNorm (𝓕 f) 2 volume = lpNorm f 2 volume := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (Localization.fourierIntegral_memLp_two hf h₂).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      h₂.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [Localization.integral_norm_sq_fourierIntegral hf h₂]

set_option maxHeartbeats 800000 in
/-- A coordinate monomial times the parameter Fourier transform is in L²,
with its norm controlled by the full parameter derivative. The exact `2π`
factor is retained. This is the directional input for the weighted estimate
in `app:ch_background:eq:bg-density-adjoint`. -/
theorem parameterFourier_directional_power_bound
    (φ : ParameterSpace → TransverseL2 n) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (k : ℕ) (v : ParameterSpace) (hv : ‖v‖ ≤ 1) :
    MemLp (fun ξ : ParameterSpace => (2 * Real.pi * |⟪ξ, v⟫|) ^ k * ‖𝓕 φ ξ‖) 2 volume ∧
      lpNorm (fun ξ : ParameterSpace => (2 * Real.pi * |⟪ξ, v⟫|) ^ k * ‖𝓕 φ ξ‖) 2 volume ≤
        lpNorm (iteratedFDeriv ℝ k φ) 2 volume := by
  let d : ParameterSpace → TransverseL2 n :=
    fun x => iteratedFDeriv ℝ k φ x (fun _ => v)
  have hj (j : ℕ) : Continuous (iteratedFDeriv ℝ j φ) :=
    hφ.continuous_iteratedFDeriv (by simp)
  have hi (j : ℕ) : Integrable (iteratedFDeriv ℝ j φ) :=
    (hj j).integrable_of_hasCompactSupport (hc.iteratedFDeriv j)
  have hm : MemLp (iteratedFDeriv ℝ k φ) 2 volume :=
    (hj k).memLp_of_hasCompactSupport (hc.iteratedFDeriv k)
  have hd : Continuous d := by
    exact (continuous_eval_const (fun _ : Fin k => v)).comp (hj k)
  have hdc : HasCompactSupport d := (hc.iteratedFDeriv (𝕜 := ℝ) k).comp_left
    (g := fun a : ContinuousMultilinearMap ℝ (fun _ : Fin k => ParameterSpace)
      (TransverseL2 n) => a (fun _ => v)) (by simp)
  have hdi : Integrable d := hd.integrable_of_hasCompactSupport hdc
  have hdm : MemLp d 2 volume := hd.memLp_of_hasCompactSupport hdc
  have he (ξ : ParameterSpace) :
      ‖𝓕 d ξ‖ = (2 * Real.pi * |⟪ξ, v⟫|) ^ k * ‖𝓕 φ ξ‖ := by
    have ha : 𝓕 (iteratedFDeriv ℝ k φ) ξ (fun _ => v) = 𝓕 d ξ := by
      convert! Real.fourier_continuousMultilinearMap_apply
        (m := fun _ : Fin k => v) (v := ξ) (hi k) using 1
    have hf : 𝓕 (iteratedFDeriv ℝ k φ) =
        (fun w => VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 φ) w k) := by
      convert! Real.fourier_iteratedFDeriv hφ (fun j _ => hi j) (n := k) (by simp) using 1
    have hp : VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 φ) ξ k
        (fun _ => v) = (-(2 * Real.pi * Complex.I)) ^ k •
          (∏ _ : Fin k, -inner ℝ ξ v) • 𝓕 φ ξ := by
      convert! VectorFourier.fourierPowSMulRight_apply
        (L := -innerSL ℝ) (f := 𝓕 φ) (v := ξ) (m := fun _ : Fin k => v) using 1
    have hval : 𝓕 d ξ = (-(2 * Real.pi * Complex.I)) ^ k •
        (∏ _ : Fin k, -inner ℝ ξ v) • 𝓕 φ ξ := by
      apply ha.symm.trans
      have h := congrArg (fun f : ParameterSpace →
        ContinuousMultilinearMap ℝ (fun _ : Fin k => ParameterSpace) (TransverseL2 n) =>
          f ξ (fun _ => v)) hf
      convert! h.trans hp using 1
    rw [hval]
    simp only [norm_smul, norm_pow, norm_neg, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg,
      Complex.norm_I, mul_one, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_pow, mul_assoc]
  have hfm := (Localization.fourierIntegral_memLp_two hdi hdm).norm
  have hefun : (fun ξ => ‖𝓕 d ξ‖) =
      (fun ξ : ParameterSpace => (2 * Real.pi * |⟪ξ, v⟫|) ^ k * ‖𝓕 φ ξ‖) := funext he
  refine ⟨hefun ▸ hfm, ?_⟩
  rw [← hefun, lpNorm_norm
    (Localization.fourierIntegral_memLp_two hdi hdm).aestronglyMeasurable,
    lpNorm_parameterFourierIntegral hdi hdm]
  have hb (x : ParameterSpace) : ‖d x‖ ≤ ‖iteratedFDeriv ℝ k φ x‖ := by
    apply (iteratedFDeriv ℝ k φ x).unit_le_opNorm
    exact pi_norm_le_iff_of_nonneg zero_le_one |>.mpr (fun _ => hv)
  simpa only [lpNorm_norm hm.aestronglyMeasurable] using lpNorm_mono_real hm.norm hb

end JanetCartan.ContinuumAdjoint.DensityMultiplier
