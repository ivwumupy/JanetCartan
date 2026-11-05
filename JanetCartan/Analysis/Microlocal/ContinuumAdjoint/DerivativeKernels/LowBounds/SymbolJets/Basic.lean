module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Frequency
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Basic

/-!
# Joint charts for modified normal symbols

These are the literal definitions from `LowBounds.Kernel`, with chart data
depending on both measurement positions and the spectator. The consumer is
the modified carrier estimate in `app:ch_background:prop:bg-adjoint`.
No regularity or estimate is stored in the chart data.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow ContinuumRow.TransportKernel

/-- The two positions and physical normal frequency in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
abbrev Variables (n : ℕ) := FourierIntegral.NormalVariables n

/-- Joint chart coordinates, including the two-dimensional spectator in
`app:ch_background:eq:bg-Psi`. The third coordinate is the input slice
coordinate before substitution and the normal frequency after substitution. -/
abbrev JointVariables (n : ℕ) := Variables n × Euclidean 2

/-- Actual geometric functions for `app:ch_background:prop:bg-adjoint`.
All four conic data may depend jointly on both positions and the spectator. -/
structure Chart (n : ℕ) where
  coordinates : Euclidean n ≃ᵐ SliceVariable n
  domain : Euclidean n → Euclidean n → Euclidean 2 → Set (Euclidean n)
  forward : Euclidean n → Euclidean n → Euclidean 2 → Euclidean n → Euclidean n
  inverse : Euclidean n → Euclidean n → Euclidean 2 → Euclidean n → Euclidean n
  jacobian : Euclidean n → Euclidean n → Euclidean 2 → Euclidean n →
    Euclidean n →L[ℝ] Euclidean n

variable {n : ℕ}

/-- Original chart domain for `app:ch_background:eq:bg-Psi`. -/
def Chart.inputDomain (g : Chart n) : Set (JointVariables n) :=
  {p | p.1.2.2 ∈ g.domain p.1.1 p.1.2.1 p.2}

/-- Actual joint image domain for `app:ch_background:eq:bg-Psi`. -/
def Chart.outputDomain (g : Chart n) : Set (JointVariables n) :=
  {p | p.1.2.2 ∈ g.forward p.1.1 p.1.2.1 p.2 '' g.domain p.1.1 p.1.2.1 p.2}

/-- Joint forward map retaining both positions and the spectator
(`app:ch_background:eq:bg-Psi`). -/
def Chart.push (g : Chart n) (p : JointVariables n) : JointVariables n :=
  ((p.1.1, p.1.2.1, g.forward p.1.1 p.1.2.1 p.2 p.1.2.2), p.2)

/-- Joint inverse map for `app:ch_background:eq:bg-full-complex-amplitude`. -/
def Chart.pull (g : Chart n) (p : JointVariables n) : JointVariables n :=
  ((p.1.1, p.1.2.1, g.inverse p.1.1 p.1.2.1 p.2 p.1.2.2), p.2)

/-- Original carrier variable, before the conic inverse substitution in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def Chart.carrier (g : Chart n) (p : JointVariables n) : CarrierVariable n :=
  chartCarrierVariable g.coordinates p.2 p.1.2.2

/-- Original input density divided by the actual absolute determinant,
for `app:ch_background:prop:bg-adjoint`. This is a definition, not a jet input. -/
def inputDensity (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) (p : JointVariables n) : ℂ :=
  |(g.jacobian p.1.1 p.1.2.1 p.2 p.1.2.2).det|⁻¹ •
    modifiedNormalDensity a m p.1.1 p.1.2.1 (g.carrier p)

/-- Literal inverse density from `LowBounds.Kernel`, with fully joint geometry
(`app:ch_background:prop:bg-adjoint`). -/
def inverseDensity (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) (p : JointVariables n) : ℂ :=
  modifiedInverseDensity a m p.1.1 p.1.2.1 g.coordinates
    (g.domain p.1.1 p.1.2.1) (g.forward p.1.1 p.1.2.1)
    (g.inverse p.1.1 p.1.2.1) (g.jacobian p.1.1 p.1.2.1) p.2 p.1.2.2

/-- Literal spectator integral in physical frequency
(`app:ch_background:prop:bg-adjoint`). -/
def physicalAmplitude (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) (p : Variables n) : ℂ :=
  modifiedNormalAmplitude a m p.1 p.2.1 g.coordinates
    (g.domain p.1 p.2.1) (g.forward p.1 p.2.1)
    (g.inverse p.1 p.2.1) (g.jacobian p.1 p.2.1) p.2.2

/-- Actual normalized amplitude in the cycles-per-unit convention required
by the PDO estimate: both the factor and frequency substitution are retained
(`app:ch_background:prop:bg-adjoint`). -/
def cyclesAmplitude (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) (p : Variables n) : ℂ :=
  ((2 * Real.pi) ^ n : ℂ) *
    physicalAmplitude g a m (p.1, p.2.1, (2 * Real.pi) • p.2.2)

/-- The joint density is precisely the buffered zero extension of the input
density composed with the inverse (`app:ch_background:prop:bg-adjoint`). -/
theorem inverseDensity_eq_indicator (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) :
    inverseDensity g a m = g.outputDomain.indicator (inputDensity g a m ∘ g.pull) := by
  classical
  funext p
  by_cases hp : p ∈ g.outputDomain
  · rw [indicator_of_mem hp]
    change p.1.2.2 ∈ g.forward p.1.1 p.1.2.1 p.2 '' g.domain p.1.1 p.1.2.1 p.2 at hp
    simp only [inverseDensity, modifiedInverseDensity, indicator_of_mem hp]
    rfl
  · rw [indicator_of_notMem hp]
    change p.1.2.2 ∉ g.forward p.1.1 p.1.2.1 p.2 '' g.domain p.1.1 p.1.2.1 p.2 at hp
    simp only [inverseDensity, modifiedInverseDensity, indicator_of_notMem hp]

/-- The normalization of the actual joint normal agrees with the literal
physical kernel (`app:ch_background:prop:bg-adjoint`). -/
theorem physical_integral_eq_cycles (g : Chart n) (a : AdjointAmplitude n)
    (m : CarrierVariable n → ℝ) (x y : Euclidean n) :
    (∫ k, NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) *
      physicalAmplitude g a m (x, y, k)) =
    ∫ ξ, Complex.exp ((2 * Real.pi * inner ℝ (x - y) ξ : ℝ) * Complex.I) *
      cyclesAmplitude g a m (x, y, ξ) :=
  modifiedNormal_physical_eq_cycles (fun k ↦ physicalAmplitude g a m (x, y, k)) (x - y)

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
