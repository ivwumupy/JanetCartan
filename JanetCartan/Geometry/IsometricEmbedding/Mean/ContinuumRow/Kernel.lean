module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# The literal transport kernel

The function data and integral in `app:ch_background:eq:bg-T`. These are stable
leaf definitions, not a postulated bounded operator. Geometric admissibility,
convergence on a dense domain, and the bounded L² extension must be supplied by
the phase-chart and oscillatory estimates. In particular a total Bochner integral
on arbitrary functions is not asserted to represent the full L² operator.

The variable `η` is a physical covector: the phase is `exp(i Y·η)` as printed in
the manuscript. Torus Fourier series continue to have physical frequency `2πk`.
The measure is exactly `dz dη`; no transported measure or Jacobian is silently
inserted into the input Hilbert norm.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow

/-- Function data for one patch in `app:ch_background:eq:bg-T`. The chart map
places the local Euclidean geometry on the auxiliary torus; the kernel is zero
outside `outputChart`. This record contains no channel bound or claimed geometric
existence theorem. The fields are to be instantiated by the actual geometric construction. -/
structure CarrierData (n N : ℕ) where
  outputChart : Set (Torus n)
  chartPoint : Torus n → Euclidean n
  transportedPosition : Euclidean n → CarrierParameter → Euclidean (n - 1)
  covector : Euclidean n → CarrierParameter → Euclidean n
  normalField : Euclidean n → CarrierParameter → Euclidean N
  stressFrame : Euclidean n → Fin n → MetricTensor n
  measurementCutoff : Torus n → ℝ
  angularCutoff : CarrierParameter → Euclidean (n - 1) → ℝ
  highCutoff : ℝ → ℝ

variable {n N : ℕ}

/-- Reduced stress contraction `q_G(x,ξ)` in `app:ch_background:defn:bg-geometry`,
using the existing Frobenius tensor pairing. -/
def reducedCovector (d : CarrierData n N) (x : Euclidean n) (ξ : Euclidean n) :
    Euclidean n :=
  WithLp.toLp 2 (fun i ↦ tensorPairing (d.stressFrame x i) (fun j k ↦ ξ j * ξ k))

/-- The transport phase `Φ = Y·η` in `app:ch_background:defn:bg-carriers`. -/
def carrierPhase (d : CarrierData n N) (x : Torus n) (u : CarrierVariable n) : ℝ :=
  inner ℝ (d.transportedPosition (d.chartPoint x) u.1) u.2

/-- The real amplitude including measurement, angular, and high-frequency cutoffs,
the half-derivative weight and the normal-field square (`app:ch_background:eq:bg-T`). -/
def carrierAmplitude (d : CarrierData n N) (x : Torus n) (u : CarrierVariable n) :
    Euclidean n :=
  (d.measurementCutoff x * d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) *
    d.highCutoff ‖u.2‖ * Real.sqrt ‖u.2‖ * ‖d.normalField (d.chartPoint x) u.1‖ ^ 2) •
      reducedCovector d (d.chartPoint x) (d.covector (d.chartPoint x) u.1)

/-- Literal vector kernel, extended by zero outside the output chart
(`app:ch_background:eq:bg-T`). -/
def carrierKernel (d : CarrierData n N) (x : Torus n) (u : CarrierVariable n) :
    EuclideanSpace ℂ (Fin n) :=
  d.outputChart.indicator (fun x ↦
    Complex.exp (Complex.I * (carrierPhase d x u : ℂ)) •
      euclideanComplexInclusion (carrierAmplitude d x u)) x

/-- Exact output support in `app:ch_background:defn:bg-row`. -/
theorem carrierKernel_eq_zero_outside (d : CarrierData n N) {x : Torus n}
    (hx : x ∉ d.outputChart) (u : CarrierVariable n) : carrierKernel d x u = 0 := by
  simp [carrierKernel, hx]

/-- The high cutoff removes the low-frequency kernel
(`app:ch_background:defn:bg-row`). -/
theorem carrierKernel_eq_zero_of_highCutoff (d : CarrierData n N)
    (x : Torus n) (u : CarrierVariable n) (h : d.highCutoff ‖u.2‖ = 0) :
    carrierKernel d x u = 0 := by
  classical
  by_cases hx : x ∈ d.outputChart <;>
    simp [carrierKernel, carrierAmplitude, hx, h]

/-- The source integral on test inputs. Its use as an operator formula requires
integrability or a proved regularization limit (`app:ch_background:eq:bg-T`). -/
def carrierTestIntegral (d : CarrierData n N) (f : CarrierVariable n → ℂ)
    (x : Torus n) : EuclideanSpace ℂ (Fin n) :=
  ∫ u, f u • carrierKernel d x u ∂carrierMeasure n

/-- Finite regularization with an explicit initial-variable mask
(`app:ch_background:eq:bg-T`). Uniform bounds and removal of this mask are separate proofs. -/
def regularizedCarrierIntegral (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (f : CarrierVariable n → ℂ) (x : Torus n) : EuclideanSpace ℂ (Fin n) :=
  carrierTestIntegral d (fun u ↦ (m u : ℂ) * f u) x

/-- Candidate literal complex adjoint integral. The order of the inner product
conjugates the kernel, as required in `app:ch_background:eq:bg-realification`.
Identifying this with a bounded Hilbert adjoint still requires the analytic proof. -/
def carrierAdjointIntegral (d : CarrierData n N)
    (w : Torus n → EuclideanSpace ℂ (Fin n)) (u : CarrierVariable n) : ℂ :=
  ∫ x, inner ℂ (carrierKernel d x u) (w x)

/-- The test integral is zero outside the output chart (`app:ch_background:defn:bg-row`). -/
theorem carrierTestIntegral_eq_zero_outside (d : CarrierData n N)
    (f : CarrierVariable n → ℂ) {x : Torus n} (hx : x ∉ d.outputChart) :
    carrierTestIntegral d f x = 0 := by
  simp [carrierTestIntegral, carrierKernel_eq_zero_outside d hx]

end JanetCartan.ContinuumRow
