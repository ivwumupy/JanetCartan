module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Construction

/-!
# Literal amplitudes in the finite physical sum

These are abbreviations of the selected producer's formulas, preserving its
same root, flow, inverse chart, source mask and full zeroth-order coefficient.
They are consumed by the finite retarded sum and its upper endpoint in
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.ResidualCoordinates Characteristic.ConicAmplitude
open Characteristic.AmplitudeBounds Characteristic.RootFamily Characteristic.UniformAmplitudes
open Characteristic.EvolutionIntegral FiniteMasks FiniteMasks.ActualFamily
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)

/-- The literal three buffered local matrices, including the physical `PW₁`
entry with the full `B` coefficient (`energy-complete-residual`). -/
def selectedBufferedAmplitude (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T) (j : Fin 3) :
    T → Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  let c := f.chart p
  let e := coordinateSplit c.index
  let t := (e x).1
  let V := C.target ∩ C.symm ⁻¹' (Metric.ball t (c.maskRadius/2) ×ˢ
    (Metric.ball t (c.maskRadius/2) ×ˢ Metric.ball ((e x).2, (e p.val.val).2) (c.maskRadius/2)))
  bufferedMatrix V c.timeMask (pencilAmplitudeFamily c.index Q B
    (fieldRoot e Q c.root) Φ C c.row c.col c.sourceMask j)

/-- The SAME globally supported conic amplitudes selected for the evolution:
index zero is `W₀`, index one is `W₁`, and index two is its full physical
derivative on the output plateau (`two-term-null-identity`, `energy-complete-residual`). -/
def selectedConicAmplitude (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
    (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T) (angular : Euclidean d → ℝ)
    (j : Fin 3) : TwoTimeAmplitude d (d+1) :=
  curryCharacteristicMatrix (collared (f.chart p).radialSection
    (if j = 0 then 0 else 1) angular (selectedBufferedAmplitude f p Q B Φ C j))

end JanetCartan.RegularSector.FiniteAssembly
