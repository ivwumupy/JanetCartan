module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Kernel
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Oscillatory

/-!
# Literal transport normal entries

Algebra for `app:ch_background:eq:bg-full-complex-amplitude`. These are entries
of the literal regularized kernel product, before Hilbert operator identification
or change of variables. Both output positions and the square of the real input
regularization are retained. Consumers: `jc-continuum-normal-reduction` and
`jc-continuum-row`; the bounded carrier realization is supplied separately.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow.TransportKernel

variable {n N : ℕ}

/-- The real two-position density before the conic Jacobian division in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def normalDensityEntry (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (x y : Torus n) (u : CarrierVariable n) (i j : Fin n) : ℝ :=
  d.measurementCutoff x * d.measurementCutoff y *
    (m u ^ 2 * d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) ^ 2 *
      d.highCutoff ‖u.2‖ ^ 2 * ‖u.2‖ *
      ‖d.normalField (d.chartPoint x) u.1‖ ^ 2 *
      ‖d.normalField (d.chartPoint y) u.1‖ ^ 2 *
      reducedCovector d (d.chartPoint x) (d.covector (d.chartPoint x) u.1) i *
      reducedCovector d (d.chartPoint y) (d.covector (d.chartPoint y) u.1) j)

/-- Multiplication of the two half-derivative weights gives exactly `|η|`,
not `|η|²` (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem carrierAmplitude_product (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (x y : Torus n) (u : CarrierVariable n) (i j : Fin n) :
    m u ^ 2 * (carrierAmplitude d x u i * carrierAmplitude d y u j) =
      normalDensityEntry d m x y u i j := by
  simp only [carrierAmplitude, PiLp.smul_apply, smul_eq_mul, normalDensityEntry]
  have hs := Real.sq_sqrt (norm_nonneg u.2)
  ring_nf
  rw [hs]
  ring

/-- Literal entry of the regularized complex normal kernel. Its equality with
`T_R T_R*` is an additional analytic obligation, not a field of this definition
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def regularizedNormalEntry (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (x y : Torus n) (i j : Fin n) : ℂ :=
  ∫ u, ((m u : ℂ) * carrierKernel d x u i) *
    star ((m u : ℂ) * carrierKernel d y u j) ∂carrierMeasure n

/-- The exact regularized integrand, including phase subtraction and both
cutoff factors (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedKernel_product (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    {x y : Torus n} (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (u : CarrierVariable n) (i j : Fin n) :
    ((m u : ℂ) * carrierKernel d x u i) *
        star ((m u : ℂ) * carrierKernel d y u j) =
      NormalComparison.oscillatoryFactor 1 (carrierPhase d x u - carrierPhase d y u) *
        (normalDensityEntry d m x y u i j : ℂ) := by
  have hp := NormalComparison.oscillatoryFactor_mul_star 1
    (carrierPhase d x u) (carrierPhase d y u)
  simp only [NormalComparison.oscillatoryFactor, one_mul] at hp
  simp only [carrierKernel, Set.indicator_of_mem hx, Set.indicator_of_mem hy,
    PiLp.smul_apply, smul_eq_mul, euclideanComplexInclusion_apply,
    star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← carrierAmplitude_product, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_pow]
  simp only [NormalComparison.oscillatoryFactor, one_mul]
  calc
    _ = (Complex.exp (Complex.I * (carrierPhase d x u : ℂ)) *
        star (Complex.exp (Complex.I * (carrierPhase d y u : ℂ)))) *
        ((m u : ℂ) ^ 2 * ((carrierAmplitude d x u i : ℂ) *
          (carrierAmplitude d y u j : ℂ))) := by simp only [Complex.star_def]; ring
    _ = _ := by rw [hp]

/-- Integral form of the exact kernel multiplication. This algebraic equality
needs no convergence assumption; analytic uses must additionally establish the
integrability required for Fubini (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedNormalEntry_eq_phase_density (d : CarrierData n N)
    (m : CarrierVariable n → ℝ) {x y : Torus n}
    (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart) (i j : Fin n) :
    regularizedNormalEntry d m x y i j =
      ∫ u, NormalComparison.oscillatoryFactor 1
        (carrierPhase d x u - carrierPhase d y u) *
          (normalDensityEntry d m x y u i j : ℂ) ∂carrierMeasure n := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u ↦ regularizedKernel_product d m hx hy u i j

end JanetCartan.ContinuumRow.TransportKernel
