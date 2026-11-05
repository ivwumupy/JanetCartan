module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.FiniteBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.Cutoffs

/-!
# Extension using the actual full finite carrier normals

Instantiate `exists_carrierL2Extension` for the actual parameter-truncated
operators and the original radial masks of `app:ch_background:eq:bg-T`.
The only quantitative symbol input is the per-entry physical jet budget from
`PrimitiveBudget`. No normal identity, operator bound, or test-limit estimate
is assumed. `Construction` discharges that budget from primitive finite norms.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormalReduction TransportKernel
variable {n N : ℕ}

/-- The actual full finite reflected amplitudes yield the unique complex
carrier extension, including literal test membership, support and adjoint norm.
The parameter truncation is removed by angular support; the original radial
cutoffs exhaust tests. The budget `hB` is supplied from primitive norms by
`exists_fullReflectedMatrixAmplitude_regularized_bounds_of_primitiveNorms`.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_carrierL2Extension_of_fullReflectedMatrixBounds
    (hn : 0 < n) (d : CarrierData n N)
    {Z : Set CarrierParameter} (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    (κ : ℝ → ℝ) (hcκ : HasCompactSupport κ)
    (hκone : ∀ t ∈ Icc (0 : ℝ) 1, κ t = 1)
    {Rmask : ℕ → ℝ} {M Cmask : ℝ}
    (hmask : ∀ k : ℕ, CarrierRegularization.MaskHypotheses d
      (parameterTruncatedMask Z (radialCarrierMask κ (k + 1))) Z (Rmask k) M Cmask)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    (charts : ∀ (k : ℕ) x, x ∈ d.outputChart → ∀ y, y ∈ d.outputChart →
      ChartInputs d (radialCarrierMask κ (k + 1)) x y)
    (symbols : ∀ k x hx y hy, SymbolInputs (charts k x hx y hy))
    (ha : ∀ k x hx y hy, (symbols k x hx y hy).coefficients =
      TransportSymbol.regularizedCoefficients a κ (k + 1))
    (hJ : ∀ k x hx y hy, (symbols k x hx y hy).jacobian = J)
    (hu : ∀ k x hx y hy, (symbols k x hx y hy).inverse = u)
    (hΩ : ∀ k x hx y hy, (symbols k x hx y hy).domain = Ω)
    (hS : ∀ k x hx y hy, (symbols k x hx y hy).spectatorSupport = S)
    {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Cfreq * ‖(u p).2‖)
    (Rbox : ℝ) (hsupport : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ Rbox)
    (hb : ∀ k : ℕ, ContDiff ℝ ∞ (Function.uncurry
      (fullReflectedMatrixAmplitude (TransportSymbol.regularizedCoefficients a κ (k + 1)) J u Ω S)))
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hB : ∀ (k : ℕ) i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude
        (TransportSymbol.regularizedCoefficients a κ (k + 1)) J u Ω S ξ z i j)
      (2 * (n + 1)) B) :
    (∀ v : carrierInitialTestSpace n,
      MemLp (carrierTestIntegral d v.val) 2 volume ∧
      (eLpNorm (carrierTestIntegral d v.val) 2 volume).toReal ≤
        Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * B)) *
          ‖carrierInitialTestToLp v‖) ∧
    ∃ U : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      ‖U‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * B)) ∧
      ‖U.adjoint‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * B)) ∧
      (∀ v : carrierInitialTestSpace n,
        U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val) ∧
      (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ d.outputChart → U f x = 0) ∧
      ∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ v : carrierInitialTestSpace n,
          W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val) → W = U := by
  refine exists_carrierL2Extension d (fun k ↦ radialCarrierMask κ (k + 1))
    (radialCarrierMask_eventually_eq_one κ hκone)
    (fun k ↦ (hmask k).operator) ?_
    (fun k ↦ (hmask k).operator.comp (hmask k).operator.adjoint) (fun _ ↦ rfl)
    (mul_nonneg (sq_nonneg _) (mul_nonneg (fixedBoxAmplitudeConstant_nonneg n Rbox) hB₀)) ?_
  · intro k v
    rw [← regularizedCarrierIntegral_parameterTruncatedMask d hZ]
    exact (hmask k).operator_ae_of_representative (carrierInitialTestToLp v) v.val
      (carrierInitialTest_memLp v).coeFn_toLp
  · intro k
    exact (regularized_normal_norm_bounds hn hZ (hmask k) hcell hchart hpoint
      χ hχ hχsmooth hχcompact (TransportSymbol.regularizedCoefficients a κ (k + 1))
      J u Ω S hχone (charts k) (symbols k) (ha k) (hJ k) (hu k) (hΩ k) (hS k)
      (regularizedCoefficients_high_hasCompactSupport a hcκ (by positivity))
      hCfreq hcomparison Rbox (hb k) hsupport B (hB k)).1

end JanetCartan.ContinuumRow.CarrierNormalRealization
