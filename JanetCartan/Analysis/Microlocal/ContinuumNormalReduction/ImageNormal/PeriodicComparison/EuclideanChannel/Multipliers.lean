module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.BoundedMultiplier
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Schwartz

/-!
# Bounded differentiated image inverses

The scalar factors `∂ₐ J` used to construct the actual Euclidean channel
`μ P J χ` in `app:ch_background:prop:bg-frame`, Step 1. The physical frequency
is `2πξ`, exactly as in the shared image Bessel inverse. The consumer is
`PeriodicComparison.euclideanChannelBlock`; no realization of `P` alone is used.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped FourierTransform SchwartzMap RealInnerProductSpace
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "S" => 𝓢(E, ℂ)

/-- The actual symbol of `∂ₐ J` for the image channel in
`app:ch_background:prop:bg-frame`, Step 1. -/
def imageDerivativeBesselSymbol (a : Fin d) (ξ : E) : ℂ :=
  Complex.I * (((2 * Real.pi) • ξ) a : ℝ) * (imageBesselSymbol ξ : ℂ)

/-- The differentiated inverse is a Schwartz multiplier
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasTemperateGrowth_imageDerivativeBesselSymbol (a : Fin d) :
    (imageDerivativeBesselSymbol a).HasTemperateGrowth := by
  have hq := hasTemperateGrowth_complex_imageBesselSymbol (d := d)
  have hc : (fun ξ : E ↦ (((2 * Real.pi) • ξ) a : ℝ)).HasTemperateGrowth :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d ↦ ℝ) a).comp
      ((2 * Real.pi) • ContinuousLinearMap.id ℝ E)).hasTemperateGrowth
  unfold imageDerivativeBesselSymbol
  fun_prop

/-- The first-order factor is cancelled by the inverse weight, giving a
bounded symbol without frequency cutoffs (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_imageDerivativeBesselSymbol_le_one (a : Fin d) (ξ : E) :
    ‖imageDerivativeBesselSymbol a ξ‖ ≤ 1 := by
  let q := imageBesselSymbol ξ
  let k := (2 * Real.pi) • ξ
  have hq : 0 ≤ q := (euclideanSobolevWeight_pos (-1) k).le
  have hsq : q * q * (1 + ‖k‖ ^ 2) = 1 := by
    rw [show q * q = (1 + ‖k‖ ^ 2)⁻¹ from imageBesselSymbol_sq ξ]
    exact inv_mul_cancel₀ (by positivity)
  have hkq : ‖k‖ * q ≤ 1 := by
    nlinarith [sq_nonneg q, sq_nonneg (‖k‖ * q - 1)]
  change ‖Complex.I * (k a : ℂ) * (q : ℂ)‖ ≤ 1
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs q, abs_of_nonneg hq]
  exact (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le k a) hq).trans hkq

/-- The bounded symbol defines a genuine Lebesgue `L∞` class
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem memLp_top_imageDerivativeBesselSymbol (a : Fin d) :
    MemLp (imageDerivativeBesselSymbol a) ⊤ :=
  memLp_top_of_bound
    (hasTemperateGrowth_imageDerivativeBesselSymbol a).1.continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (norm_imageDerivativeBesselSymbol_le_one a))

/-- The bounded scalar factor `∂ₐ J` on Euclidean Lebesgue L²
(`app:ch_background:prop:bg-frame`, Step 1). -/
def imageDerivativeBesselL2Operator (a : Fin d) : L² →L[ℂ] L² :=
  fourierMultiplier ((memLp_top_imageDerivativeBesselSymbol a).toLp _)

/-- The Fourier realization extends the literal differentiated Schwartz
inverse used by `channelSchwartz` (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageDerivativeBesselL2Operator_toLp (a : Fin d) (u : S) :
    imageDerivativeBesselL2Operator a (u.toLp 2) =
      (∂_{EuclideanSpace.single a (1 : ℝ)} (imageBesselSchwartzCLM u)).toLp 2 := by
  let m := (memLp_top_imageDerivativeBesselSymbol a).toLp (imageDerivativeBesselSymbol a)
  have hm : multiplicationOperator m ((𝓕 u : S).toLp 2) =
      (SchwartzMap.smulLeftCLM ℂ (imageDerivativeBesselSymbol a) (𝓕 u)).toLp 2 := by
    apply Lp.ext
    filter_upwards [multiplicationOperator_coeFn m ((𝓕 u : S).toLp 2),
      (memLp_top_imageDerivativeBesselSymbol a).coeFn_toLp,
      (𝓕 u : S).coeFn_toLp 2,
      (SchwartzMap.smulLeftCLM ℂ (imageDerivativeBesselSymbol a) (𝓕 u)).coeFn_toLp 2]
      with ξ hξ ha hu hv
    rw [hξ, ha, hu, hv, SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_imageDerivativeBesselSymbol a), smul_eq_mul]
  have hs : SchwartzMap.smulLeftCLM ℂ (imageDerivativeBesselSymbol a) (𝓕 u) =
      𝓕 (∂_{EuclideanSpace.single a (1 : ℝ)} (imageBesselSchwartzCLM u)) := by
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    ext ξ
    have ht : (fun ξ : E ↦ inner ℝ ξ (EuclideanSpace.single a 1)).HasTemperateGrowth := by
      fun_prop
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_imageDerivativeBesselSymbol a)]
    change imageDerivativeBesselSymbol a ξ • (𝓕 u : S) ξ =
      (2 * Real.pi * Complex.I) •
        (SchwartzMap.smulLeftCLM ℂ
          (fun ξ : E ↦ inner ℝ ξ (EuclideanSpace.single a 1))
          (𝓕 (imageBesselSchwartzCLM u))) ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply ht]
    simp only [
      imageBesselSchwartzCLM_apply, fourier_imageBesselMultiplier,
      imageDerivativeBesselSymbol, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul, PiLp.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  change 𝓕⁻ (multiplicationOperator m (𝓕 (u.toLp 2))) = _
  rw [SchwartzMap.toLp_fourier_eq, hm, SchwartzMap.toLp_fourierInv_eq, hs,
    FourierTransform.fourierInv_fourier_eq]

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
