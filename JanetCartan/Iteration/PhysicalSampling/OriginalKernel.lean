module

public import JanetCartan.Iteration.PhysicalSampling.CutoffRealization
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicHighPass

/-!
# The literal scalar kernel for the original selected detector

This specialization retains the exact original conic detector, norm high-pass,
radial bands, color inverse frequencies and carrier chart. Its kernel bound one
is proved from those original masks. Only the independent scalar output
coordinate and fixed physical/carrier cutoffs are new (`new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts Sampling SamplingKernelBounds
open RawPrimary.MaskProfiles ContinuumRow PhysicalMean

variable {m J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}

/-- The SAME original scalar sampling kernel with every smooth mask fixed to
its literal selected value. No mask regularity or kernel bound is an input. -/
def originalScalarKernelData
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {c C : ℝ} (hP : P.IsValid c C)
    (hcarrier : closedBall center.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {ηoriginal : Euclidean (m + 1 - 1)} {roriginal : ℝ}
    (hηoriginal : ηoriginal ≠ 0) (hroriginal : 0 < roriginal)
    (τ : (Fin 3 → Fin (p + 1)) → ℝ) (hτ₀ : ∀ color, τ color ≠ 0) :
    BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × SeparatedSampling.Point)) (m + 1) :=
  retainedScalarKernelData T Q χ center hρ hP hcarrier
    (originalConicDetector hηoriginal hroriginal)
    (fun η ↦ FixedCutoffs.highFrequency ‖η‖)
    (fun _ hη ↦ originalConicDetector_contDiffAt hηoriginal hroriginal hη)
    (contDiff_originalConicHighPass (m + 1))
    (fun _ hη ↦ FixedCutoffs.highFrequency_zero hη)
    1 zero_le_one (norm_originalConicDetectorMask_le_one hηoriginal hroriginal) τ hτ₀

end JanetCartan.PhysicalSampling
