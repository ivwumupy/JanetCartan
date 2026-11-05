module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Representatives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.SmoothFamilyNorms.Measured
public import JanetCartan.Analysis.Operator.CanonicalRow
public import JanetCartan.Analysis.Iteration.MeanRecurrence

/-!
# The complete smooth residual of the fixed-row iteration

`main:lem:mean-recurrence` uses the complete output on the whole torus,
including the exterior channel. Here the smooth auxiliary output is the
literal constructed representative, and the carrier response uses the actual
component adjoints with the original weights. Telescoping proves equality
with the L² recurrence. No global physical-strain identity is used.

The raw smooth response maps and their L² identification are inputs from
the actual current-atom/canonical construction. No estimates or successful
mean solve are assumed. These inputs must still be instantiated on the same
sample and raw prefixes for the full source proposition.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

open MeasureTheory Finset
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean

open ContinuumRow AuxiliaryRawBand SmoothPeriodicFamily

variable {n : ℕ} {ι : Type*} [Fintype ι]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]

/-- The literal weighted response to the component adjoints. The raw
response is smooth because the raw band precedes physical realization;
there is no assertion that an arbitrary physical L² field is smooth
(`main:eq:canonical-identity`). -/
def smoothCanonicalResponse (μ : ι → ℝ)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (rawResponse : ∀ i, Raw i →ₗ[ℝ] SmoothResidual n)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) : OutputL2 n →ₗ[ℝ] SmoothResidual n :=
  ∑ i, μ i • (rawResponse i).comp ((A i).adjoint.toLinearMap.comp Q₀.toLinearMap)

section Complete

variable (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))

/-- Complete sampled prefix normal, with the original auxiliary cutoff
and weighted raw row (`main:eq:canonical-identity`). -/
def completeCanonicalNormal (μ : ι → ℝ)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n) {K : ℝ} (hK : 1 ≤ K) :
    OutputL2 n →L[ℝ] OutputL2 n :=
  cutAuxiliaryNormal c χmeas χsrc ψ hK +
    (CanonicalRow.weightedRow μ A).comp (CanonicalRow.weightedRow μ A).adjoint

/-- One complete smooth update with the SAME fixed `Q₀`, including its
exterior output (`main:eq:full-recursion`). -/
def completeCanonicalCorrection (μ : ι → ℝ)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (rawResponse : ∀ i, Raw i →ₗ[ℝ] SmoothResidual n)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) {K : ℝ} (hK : 1 ≤ K) :
    OutputL2 n →ₗ[ℝ] SmoothResidual n :=
  cutAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ Q₀ hK +
    smoothCanonicalResponse μ A rawResponse Q₀

/-- The complete smooth update has exactly the complete sampled normal's
L² action. This uses the proved canonical response identity, including zero
weights (`main:eq:canonical-identity`). Only the literal raw-response
identification remains with the current-atom producer. -/
theorem completeCanonicalCorrection_toL2 (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (rawResponse : ∀ i, Raw i →ₗ[ℝ] SmoothResidual n)
    (hraw : ∀ i v, smoothResidualToL2 n (rawResponse i v) = A i v)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) {K : ℝ} (hK : 1 ≤ K) (e : OutputL2 n) :
    smoothResidualToL2 n
        (completeCanonicalCorrection c hc χmeas χsrc ψ hm hs hψ μ A rawResponse Q₀ hK e) =
      completeCanonicalNormal c χmeas χsrc ψ μ A hK (Q₀ e) := by
  have haux : smoothResidualToL2 n
      (cutAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ Q₀ hK e) =
      cutAuxiliaryNormal c χmeas χsrc ψ hK (Q₀ e) :=
    cutAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ Q₀ hK e
  simp only [completeCanonicalCorrection, LinearMap.add_apply, smoothCanonicalResponse,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, map_add, map_sum, map_smul, hraw, haux]
  have hw : CanonicalRow.waveComponent (fun i ↦ ContinuousLinearMap.id ℝ (Raw i))
      (fun i ↦ ContinuousLinearMap.id ℝ (Raw i)) A = A := by
    funext i
    simp [CanonicalRow.waveComponent]
  simpa only [hw, CanonicalRow.canonicalDerivative, CanonicalRow.canonicalData,
    ContinuousLinearMap.id_apply, completeCanonicalNormal] using
    CanonicalRow.auxiliary_add_canonical_response μ hμ
      (fun i ↦ ContinuousLinearMap.id ℝ (Raw i))
      (fun i ↦ ContinuousLinearMap.id ℝ (Raw i)) A
      (cutAuxiliaryNormal c χmeas χsrc ψ hK) (Q₀ e)

variable {m : Type*} [Fintype m]

/-- The SAME complete smooth residual whose L² and high Sobolev bounds are
used in `main:lem:mean-recurrence`. It retains every complete linear output
and the actual measured Hermitian square of the accumulated derivative.
The finite run is the existing `MeanRecurrence.run`. -/
def completeResidualRepresentative (μ : ι → ℝ)
    (A : ℕ → ∀ i, Raw i →L[ℝ] OutputL2 n)
    (rawResponse : ℕ → ∀ i, Raw i →ₗ[ℝ] SmoothResidual n)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (K : ℕ → ℝ) (hK : ∀ l, 1 ≤ K l)
    (D : ℕ → OutputL2 n →ₗ[ℝ] SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (e : SmoothResidual n) (l : ℕ) : SmoothResidual n :=
  let E := fun i ↦ (completeCanonicalNormal c χmeas χsrc ψ μ (A i) (hK i)).toLinearMap
  let z := MeanRecurrence.run Q₀.toLinearMap E D
    (measuredHermitianBilinear μ C hC) (smoothResidualToL2 n e)
  e - (∑ i ∈ range l,
    completeCanonicalCorrection c hc χmeas χsrc ψ hm hs hψ μ (A i) (rawResponse i)
      Q₀ (hK i) (z i).2) - measurementFamily C hC (tensorBilinear μ (z l).1 (z l).1)

/-- Telescoping identifies the constructed smooth representative with the
L² residual of the SAME finite run. Consequently `RecurrenceTail` and
`FiniteMeanEstimates` can estimate this representative without interpreting
the exterior-augmented row as a physical strain (`main:lem:mean-recurrence`). -/
theorem completeResidualRepresentative_toL2 (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (A : ℕ → ∀ i, Raw i →L[ℝ] OutputL2 n)
    (rawResponse : ℕ → ∀ i, Raw i →ₗ[ℝ] SmoothResidual n)
    (hraw : ∀ l i v, smoothResidualToL2 n (rawResponse l i v) = A l i v)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (K : ℕ → ℝ) (hK : ∀ l, 1 ≤ K l)
    (D : ℕ → OutputL2 n →ₗ[ℝ] SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (e : SmoothResidual n) (l : ℕ) :
    smoothResidualToL2 n
      (completeResidualRepresentative c hc χmeas χsrc ψ hm hs hψ μ A rawResponse
        Q₀ K hK D C hC e l) =
      (MeanRecurrence.run Q₀.toLinearMap
        (fun i ↦ (completeCanonicalNormal c χmeas χsrc ψ μ (A i) (hK i)).toLinearMap)
        D (measuredHermitianBilinear μ C hC) (smoothResidualToL2 n e) l).2 := by
  let E := fun i ↦ (completeCanonicalNormal c χmeas χsrc ψ μ (A i) (hK i)).toLinearMap
  let B := measuredHermitianBilinear (m := m) μ C hC
  let e₀ := smoothResidualToL2 n e
  let z := MeanRecurrence.run Q₀.toLinearMap E D B e₀
  have hid := MeanRecurrence.residual_eq_source_sub_accumulated Q₀.toLinearMap E B
    (fun i ↦ (z i).2) (fun i ↦ D i (z i).2) l
    (fun i _ ↦ MeanRecurrence.run_residual_recurrence Q₀.toLinearMap E D B e₀ i)
  rw [← MeanRecurrence.run_accumulated_eq_sum] at hid
  change (z l).2 = e₀ - (∑ i ∈ range l, E i (Q₀ (z i).2)) - B (z l).1 (z l).1 at hid
  have hcorr (i : ℕ) (y : OutputL2 n) :
      smoothResidualToL2 n (completeCanonicalCorrection c hc χmeas χsrc ψ hm hs hψ
        μ (A i) (rawResponse i) Q₀ (hK i) y) = E i (Q₀ y) :=
    completeCanonicalCorrection_toL2 c hc χmeas χsrc ψ hm hs hψ μ hμ
      (A i) (rawResponse i) (hraw i) Q₀ (hK i) y
  unfold completeResidualRepresentative
  simp only [map_sub, map_sum, hcorr]
  simpa only [E, B, e₀, z, measuredHermitianBilinear, measurementL2,
    LinearMap.compr₂_apply, LinearMap.comp_apply, smoothResidualToL2] using hid.symm

end Complete
end JanetCartan.CurrentMean
