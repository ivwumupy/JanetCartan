module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Retained

/-!
# The span of the original admitted initial scalars

The consumer is `exists_finite_retained_raw_primary_family_with_source_admission`.
Its primitive scalar bounds are used only on generators. Smoothness of the SAME
transported amplitude extends to their real span by its published linear map.
The finite-family constructor remains responsible for supplying generator smoothness.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PrimarySourceAdmission
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- The original scalar class, with precisely the low order and positivity
conditions of the retained constructor (`app:ch_waves:thm:leading`). -/
def primitiveInitialScalars {n : ℕ} (z₀ : Euclidean 3) (R Mᵣ m : ℝ) :
    Set (Euclidean (n - 1) × Euclidean 3 → ℝ) :=
  {r | ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) ∧
    cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r ≤ Mᵣ ∧
    ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p}

/-- The admissible linear domain contains the original scalars and all their
finite real linear combinations (`app:ch_response:cor:current-atoms`). -/
def initialScalarSpan {n : ℕ} (z₀ : Euclidean 3) (R Mᵣ m : ℝ) :
    Submodule ℝ (Euclidean (n - 1) × Euclidean 3 → ℝ) :=
  Submodule.span ℝ (primitiveInitialScalars z₀ R Mᵣ m)

/-- Every scalar admitted by the original constructor belongs to the linear
domain, with all three original hypotheses (`app:ch_waves:eq:WKB-W`). -/
theorem mem_initialScalarSpan {n : ℕ} {z₀ : Euclidean 3} {R Mᵣ m : ℝ}
    {r : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hr : ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)))
    (hbound : cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r ≤ Mᵣ)
    (hpos : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p) :
    r ∈ initialScalarSpan z₀ R Mᵣ m :=
  Submodule.subset_span ⟨hr, hbound, hpos⟩

/-- Generator amplitude smoothness, supplied by the SAME retained raw family,
extends to its admissible span. No norm or positivity condition is imposed on
sums and differences (`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_scalarAmplitude_of_mem_initialScalarSpan
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    {z₀ : Euclidean 3} {R Mᵣ m : ℝ}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hα : ∀ r ∈ primitiveInitialScalars z₀ R Mᵣ m,
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    {r : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hr : r ∈ initialScalarSpan z₀ R Mᵣ m) :
    ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω := by
  let L := scalarAmplitudeLinearMap T Q F row col Φ Y
  change ContDiffOn ℝ ∞ (L r) Ω
  induction hr using Submodule.span_induction with
  | mem r hr => exact hα r hr
  | zero =>
    rw [map_zero]
    exact contDiffOn_const
  | add r s _ _ hr hs =>
    rw [map_add]
    exact hr.add hs
  | smul a r _ hr =>
    rw [map_smul]
    exact hr.const_smul a

end JanetCartan.PrimarySourceAdmission
