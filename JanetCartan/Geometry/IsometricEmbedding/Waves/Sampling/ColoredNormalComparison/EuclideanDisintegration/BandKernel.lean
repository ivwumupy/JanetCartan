module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.SingleBand
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.BandOperator

/-!
# Identification with the actual band-kernel construction

The slice in `samplingNormal_eq_integral_compactSlice` is the existing
`BandKernelData.operator` whenever their primitive forward kernels agree.
This closes the construction-to-construction bridge on literal Euclidean
output for `app:ch_waves:eq:sampling-prefix-normal`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
open NormalComparison SamplingKernelBounds Pseudodifferential RawInputRealization

variable {n : ℕ} {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P]

set_option maxHeartbeats 800000 in
/-- Primitive equality of the retained forward kernels identifies the
constructed compact slice with the actual `BandKernelData.operator`.
Both input restriction and physical Lebesgue measure are unchanged
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem compactSliceOperator_eq_bandKernelOperator
    (D : BandKernelData P n) (R : ℝ) (p : P)
    (b : ℝ → Fin n → Euclidean n → Euclidean (n - 1) → ℂ)
    (hb : ∀ s i, Continuous (Function.uncurry (b s i)))
    {X : Set (Euclidean n)} {U : Set (Euclidean (n - 1))}
    (hX : IsCompact X) (hU : IsCompact U)
    (hs : ∀ s i x θ, (x, θ) ∉ X ×ˢ U → b s i x θ = 0)
    (s : ℝ)
    (hkernel : ∀ θ ∈ annulus n R, ∀ i : Fin n,
      (fun x ↦ b s i x θ) =ᵐ[volume] fun x ↦ D.kernel p θ x i) :
    toSamplingOutput (compactSliceOperator (annulus n R) b hb hX hU hs s) = D.operator R p := by
  let a := compactCoordinateColumn (b s) (hb s) hX (hs s)
  have ha : MemLp a 2 (annularMeasure n R) :=
    memLp_compactCoordinateColumn (b s) (hb s) hX hU (hs s) (annulus n R)
  have hcol (θ : Euclidean (n - 1)) (hθ : θ ∈ annulus n R) :
      a θ = finiteL2CoordinateIsometry volume (D.column p θ) := by
    ext i
    have hd := (finiteL2CoordinateIsometry_ae_iff volume (D.column p θ) (D.kernel p θ)).mp
      (D.column_coe p θ) i
    filter_upwards [compactCoordinateColumn_coe (b s) (hb s) hX (hs s) θ i,
      hd, hkernel θ hθ i] with x hx hy hz
    exact hx.trans (hz.trans hy.symm)
  have hT : compactSliceOperator (annulus n R) b hb hX hU hs s = kernelSynthesis ha :=
    compactVectorKernelOperator_eq_synthesis (b s) (hb s) hX hU (hs s) (annulus n R)
  apply ContinuousLinearMap.adjoint.injective
  ext1 f
  apply Lp.ext
  rw [toSamplingOutput_adjoint, hT]
  filter_upwards [kernelSynthesis_hasAdjointKernel ha (finiteL2CoordinateIsometry volume f),
    D.operator_hasAdjointKernel R p f, ae_restrict_mem (measurableSet_annulus n R)] with θ hx hy hθ
  exact hx.trans (((congrArg (fun v ↦ inner ℂ v (finiteL2CoordinateIsometry volume f))
    (hcol θ hθ)).trans
      ((finiteL2CoordinateIsometry volume).inner_map_map (D.column p θ) f)).trans hy.symm)

end JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
