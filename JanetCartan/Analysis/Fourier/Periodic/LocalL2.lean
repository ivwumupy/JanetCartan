module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.SupportedKernel
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.OutputTransfer
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization

/-!
# Physical chart L² and auxiliary torus L²

The measure-preserving chart comparison required by
`app:ch_background:defn:bg-row` and Step 1 of
`app:ch_background:prop:bg-frame`. The generic maps and kernel transport results
are in `PeriodicLocalL2`; the declarations here specialize them to the shared
real and complex output spaces of `ContinuumRow`.

The comparison is proved from Lebesgue measure and the actual quotient map.
Analytic boundedness and the Euclidean kernel realization remain explicit
inputs to the transport theorems, to be instantiated by the continuum-row and
normal-reduction constructions. Smooth periodization is reused from
`AmplitudeBound.Periodization`.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.PeriodicLocalL2
variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- Real vector output zero extension for `app:ch_background:defn:bg-row`. -/
abbrev realChartToTorus (hK : MeasurableSet K) :
    EuclideanL2 n (Euclidean n) →L[ℝ] ContinuumRow.OutputL2 n := chartToTorus hK

/-- Real vector output restriction for `app:ch_background:defn:bg-row`. -/
abbrev realChartToEuclidean (hK : MeasurableSet K) :
    ContinuumRow.OutputL2 n →L[ℝ] EuclideanL2 n (Euclidean n) := chartToEuclidean hK

/-- Complex vector output zero extension for `app:ch_background:eq:bg-T`. -/
abbrev complexChartToTorus (hK : MeasurableSet K) :
    EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] ContinuumRow.ComplexOutputL2 n :=
  chartToTorus hK

/-- Complex vector output restriction for `app:ch_background:eq:bg-T`. -/
abbrev complexChartToEuclidean (hK : MeasurableSet K) :
    ContinuumRow.ComplexOutputL2 n →L[ℂ] EuclideanL2 n (EuclideanSpace ℂ (Fin n)) :=
  chartToEuclidean hK

/-- The literal real-output adjoint identity (`app:ch_background:defn:bg-row`). -/
theorem realChartToTorus_adjoint (hK : MeasurableSet K) :
    (realChartToTorus hK).adjoint = realChartToEuclidean hK := chartToTorus_adjoint hK

/-- The literal complex-output adjoint identity (`app:ch_background:eq:bg-T`). -/
theorem complexChartToTorus_adjoint (hK : MeasurableSet K) :
    (complexChartToTorus hK).adjoint = complexChartToEuclidean hK := chartToTorus_adjoint hK

/-- The existing smooth compact amplitude periodization preserves its literal
Euclidean integral (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_amplitudePeriodization {r : ℝ} (hr : r < 1 / 2)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : AmplitudeBound.SupportedInCenteredBox r f) :
    (∫ z : Torus n, AmplitudeBound.amplitudePeriodization f z) = ∫ x, f x := by
  apply integral_representative_of_supported (K := halfOpenCell n) Set.Subset.rfl f
  intro x hx
  by_contra hfx
  apply hx
  intro i
  have hi := abs_le.mp (hf x hfx i)
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

end JanetCartan.PeriodicLocalL2
