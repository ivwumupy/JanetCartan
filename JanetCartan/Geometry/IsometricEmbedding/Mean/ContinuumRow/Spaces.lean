module

public import JanetCartan.Analysis.Fourier.Periodic
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Hilbert spaces of the continuum row

Shared representation for `app:ch_background:defn:bg-row`. The auxiliary torus is
unit-period with normalized Haar measure. Carrier data use Lebesgue measure in
initial variables, never the pushforward by the transport. Complex carrier data
retain both quadratures when considered as a real Hilbert space.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow

/-- The carrier parameter `z = (s,v) ∈ ℝ × ℝ²` in `app:ch_background:defn:bg-carriers`. -/
abbrev CarrierParameter := ℝ × Euclidean 2

/-- Initial Fourier variables `(z,η)` in `app:ch_background:eq:bg-T`.
Here `η` is the physical (radian) transverse covector. -/
abbrev CarrierVariable (n : ℕ) := CarrierParameter × Euclidean (n - 1)

/-- Literal initial-variable measure `dz dη` in `app:ch_background:eq:bg-T`. -/
def carrierMeasure (n : ℕ) : Measure (CarrierVariable n) :=
  (volume.prod volume).prod volume

/-- The initial-variable Lebesgue product is sigma-finite
(`app:ch_background:eq:bg-T`). -/
instance carrierMeasure_sigmaFinite (n : ℕ) : SigmaFinite (carrierMeasure n) := by
  unfold carrierMeasure
  infer_instance

/-- Full complex input of one channel in `app:ch_background:defn:bg-row`.
Its inherited real inner product is `Re ∫ conj(f) g`. -/
abbrev CarrierL2 (n : ℕ) := Lp ℂ 2 (carrierMeasure n)

/-- Real reduced-strain output on the auxiliary torus (`app:ch_background:defn:bg-row`). -/
abbrev OutputL2 (n : ℕ) := Lp (Euclidean n) 2 (volume : Measure (Torus n))

/-- Complexification of the reduced-strain output (`app:ch_background:eq:bg-T`). -/
abbrev ComplexOutputL2 (n : ℕ) :=
  Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Torus n))

/-- Finite Hilbert sum of the carrier inputs (`app:ch_background:defn:bg-row`). -/
abbrev CarrierFamilyL2 (n : ℕ) (ι : Type*) [Fintype ι] := PiLp 2 (fun _ : ι ↦ CarrierL2 n)

/-- Physical input: image data and all carrier quadratures (`app:ch_background:defn:bg-row`). -/
abbrev PhysicalInput (n : ℕ) (ι : Type*) [Fintype ι] :=
  WithLp 2 (OutputL2 n × CarrierFamilyL2 n ι)

/-- The exterior input is an auxiliary torus field, as in `app:ch_background:defn:bg-row`. -/
abbrev AugmentedInput (n : ℕ) (ι : Type*) [Fintype ι] :=
  WithLp 2 (PhysicalInput n ι × OutputL2 n)

end JanetCartan.ContinuumRow
