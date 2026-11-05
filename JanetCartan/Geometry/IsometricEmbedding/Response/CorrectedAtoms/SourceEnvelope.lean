module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.RetainedFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Extension

/-!
# The same corrected atom uses the checked primary source envelope

This is the identification needed to apply
`ResponsePrimarySources.exists_retained_fullStrainEnvelope_constants` and the
fixed response-transfer estimates to `fullPrimaryResponse`. The original source
cutoff is unchanged. The already supplied envelope cutoff is one on its entire
closed support; no second source or envelope is chosen.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CorrectedAtoms
open ActualCarriers FrozenMenu CurrentFullPhase ResponseSourceExtension
open ResponsePrimarySources ResponseTransfer.SourceNegative LeadingWave.FullModulation

/-- The correction is the SAME fixed operator applied to the exact modulated
source whose complete cubic envelope is bounded by the retained source producer.
This transfers those existing input estimates without identifying independent
existential choices (`app:ch_response:eq:response-graded-source`,
`app:ch_response:cor:current-atoms`). -/
theorem fullPrimaryResponse_eq_modulatedSource
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χsrc : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    {core chart : Set (Euclidean n)} (χenv : OutputCutoff core chart)
    (hs : tsupport χsrc ⊆ core) (τ : ℝ)
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (c : Euclidean 3 × Euclidean (n - 1)) :
    fullPrimaryResponse T Q F row col Φ Y χsrc B τ r c =
      complexifyResponse B (modulatedSource χsrc (fun x ↦ phase T Q x c.2)
        (fullStrainEnvelope T Q F row col Φ Y r χenv τ c) τ⁻¹) :=
  congrArg (complexifyResponse B)
    (cutoff_fullPrimaryStrain_eq_modulatedSource T Q F row col Φ Y r χenv χsrc hs τ c)

end JanetCartan.CorrectedAtoms
