module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.ChartExtension
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.SmoothBand
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.MatrixKernel
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Coordinates

/-!
# Primitive matching of the normalized full-phase kernel

The matching hypotheses are equalities of the original phase and measured
amplitude. They retain the angular cutoff, frequency mask, half derivative,
physical measurement, square-root Jacobian and Fourier normalization. Their
actual producers are `RawPrimary.Construction.fullPrimaryWave`, `Leading`,
and `FullPhaseCharts`; the sampling parent must instantiate them for the same
objects. No forward, adjoint or normal identity is a matching hypothesis.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
open SamplingKernelBounds ContinuumRow NormalComparison Pseudodifferential

/-- The transverse Jacobian and half derivative convert the physical Fourier
factor into the full-dimensional oscillatory normalization. This is the scalar
calculation needed to supply primitive amplitude matching from the actual raw
wave (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem fullPhase_fourier_normalization {n : ℕ} (hn : 1 ≤ n) (j : ℕ)
    (θ : Euclidean (n - 1)) :
    Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) * Real.sqrt ‖(2 : ℝ) ^ j • θ‖ *
        (2 * Real.pi) ^ (-(n : ℝ) / 2) =
      normalOperatorScale n ((2 : ℝ) ^ j) * Real.sqrt ‖θ‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j),
    Real.sqrt_mul (by positivity)]
  calc
    _ = (2 * Real.pi) ^ (-(n : ℝ) / 2) *
        (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) * Real.sqrt ((2 : ℝ) ^ j)) *
          Real.sqrt ‖θ‖ := by ring
    _ = _ := by
      rw [RawInputDilation.sqrt_jacobian_mul_sqrt hn (by positivity),
        RawInputDilation.fourierScalar_mul_dilationScale (by positivity)]

variable {P : Type*} [TopologicalSpace P] {m : ℕ}
  {G : UniformNormalGeometry (m + 1) (m + 1)} {C : ℕ → ℝ}

/-- The normalized physical column is obtained from primitive phase and
amplitude matching, not from an assumed operator identity
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem normalizedFullBandColumn_coordinate_ae
    (D : BandKernelData P (m + 1)) (q : SeparatedSampling.Point → P)
    (χ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2)
    (F : UniformNormalData G C) (ε : ℝ) (u : ℝ × Euclidean m)
    (hphase : ∀ x, D.phase ((q (carrierSamplingEquiv (u.1, v)), (2 : ℝ) ^ j • u.2), x) =
      (2 : ℝ) ^ j * F.phase ε x (fullInputCoordinates m u))
    (hamplitude : ∀ x i,
      (Real.sqrt (((2 : ℝ) ^ j) ^ m) : ℂ) * (χ (carrierSamplingEquiv (u.1, v)) : ℂ) *
        (Real.sqrt ‖(2 : ℝ) ^ j • u.2‖ : ℂ) * D.mask ((2 : ℝ) ^ j • u.2) *
          D.amplitude ((q (carrierSamplingEquiv (u.1, v)), (2 : ℝ) ^ j • u.2), x) i =
      (normalOperatorScale (m + 1) ((2 : ℝ) ^ j) : ℂ) *
        F.amplitude ε x (fullInputCoordinates m u) i)
    (i : Fin (m + 1)) :
    finiteL2CoordinateIsometry volume
      (Real.sqrt (((2 : ℝ) ^ j) ^ m) •
        fullBandColumn D q χ v (u.1, (2 : ℝ) ^ j • u.2)) i =ᵐ[volume]
      fun x ↦ (normalOperatorScale (m + 1) ((2 : ℝ) ^ j) : ℂ) *
        oscillatoryFactor ((2 : ℝ) ^ j) (F.phase ε x (fullInputCoordinates m u)) *
          F.amplitude ε x (fullInputCoordinates m u) i := by
  filter_upwards [finiteL2Coordinates_apply_ae volume
    (Real.sqrt (((2 : ℝ) ^ j) ^ m) •
      fullBandColumn D q χ v (u.1, (2 : ℝ) ^ j • u.2)) i,
    Lp.coeFn_smul (Real.sqrt (((2 : ℝ) ^ j) ^ m))
      (fullBandColumn D q χ v (u.1, (2 : ℝ) ^ j • u.2)),
    fullBandColumn_coe D q χ v (u.1, (2 : ℝ) ^ j • u.2)] with x h₁ h₂ h₃
  change (finiteL2CoordinateIsometry volume _ i) x = _ at h₁
  rw [h₁, h₂]
  change (Real.sqrt (((2 : ℝ) ^ j) ^ m) •
    (fullBandColumn D q χ v (u.1, (2 : ℝ) ^ j • u.2)) x) i = _
  rw [h₃]
  simp only [BandKernelData.kernel, bandKernel, PiLp.smul_apply, Complex.real_smul,
    smul_eq_mul, hphase, oscillatoryFactor, Complex.ofReal_mul]
  rw [show (((2 : ℝ) ^ j : ℝ) : ℂ) *
      (F.phase ε x (fullInputCoordinates m u) : ℂ) * Complex.I =
      Complex.I * (((2 : ℝ) ^ j : ℝ) : ℂ) *
        (F.phase ε x (fullInputCoordinates m u) : ℂ) by ring]
  simp only [← mul_assoc]
  linear_combination
    Complex.exp (Complex.I * (((2 : ℝ) ^ j : ℝ) : ℂ) *
      (F.phase ε x (fullInputCoordinates m u) : ℂ)) * hamplitude x i

/-- Pairing the matched column with an arbitrary full physical output keeps
both complex quadratures. This is the pointwise input to the actual adjoint
identification (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem inner_eq_sum_integral_of_coordinate_kernel
    (k f : SamplingKernelBounds.Output (m + 1))
    (t : Fin (m + 1) → Euclidean (m + 1) → ℂ)
    (hk : ∀ i, finiteL2CoordinateIsometry volume k i =ᵐ[volume] t i) :
    inner ℂ k f = ∑ i, ∫ x, star (t i x) *
      (finiteL2CoordinateIsometry volume f i) x := by
  rw [← (finiteL2CoordinateIsometry volume).inner_map_map, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hk i] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

end JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
