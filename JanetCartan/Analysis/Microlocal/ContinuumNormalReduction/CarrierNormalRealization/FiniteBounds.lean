module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.FiniteIdentification
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.PrimitiveBudget

/-!
# Full finite carrier normal bounds

Identify the actual normal globally before applying the full amplitude estimate
in `app:ch_background:prop:bg-frame`, Step 1. Both real quadratures recover the
complex normal needed by `exists_carrierL2Extension`. The physical derivative
budget is supplied by `PrimitiveBudget`, independently of the kernel identity.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormalReduction TransportKernel
variable {n N : ℕ}

/-- The actual complex and real finite carrier normals satisfy the same explicit
full-space bound, with both measurement supports and no additional factor four.
The primitive budget producer supplies `hB`; this theorem assumes no normal
identity or operator bound (`app:ch_background:eq:bg-real-symbol`). -/
theorem regularized_normal_norm_bounds
    (hn : 0 < n) {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    {Z : Set CarrierParameter} {Rmask M Cmask : ℝ}
    (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    (h : CarrierRegularization.MaskHypotheses d (parameterTruncatedMask Z m) Z Rmask M Cmask)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    (charts : ∀ x ∈ d.outputChart, ∀ y ∈ d.outputChart, ChartInputs d m x y)
    (symbols : ∀ x hx y hy, SymbolInputs (charts x hx y hy))
    (ha : ∀ x hx y hy, (symbols x hx y hy).coefficients = a)
    (hJ : ∀ x hx y hy, (symbols x hx y hy).jacobian = J)
    (hu : ∀ x hx y hy, (symbols x hx y hy).inverse = u)
    (hΩ : ∀ x hx y hy, (symbols x hx y hy).domain = Ω)
    (hS : ∀ x hx y hy, (symbols x hx y hy).spectatorSupport = S)
    (hhigh : HasCompactSupport a.high) {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Cfreq * ‖(u p).2‖)
    (Rbox : ℝ)
    (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (hsupport : ∀ x, a.measurement x ≠ 0 → ∀ j, |x j| ≤ Rbox)
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) (2 * (n + 1)) B) :
    ‖h.operator.comp h.operator.adjoint‖ ≤
        (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * B) ∧
      ‖(realQuadratureChannel h.operator).comp (realQuadratureChannel h.operator).adjoint‖ ≤
        (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * B) := by
  have hid := regularized_realNormal_eq_transfer_fullReflectedMatrixOperator hn hZ h
    hcell hchart hpoint χ hχ hχsmooth hχcompact a J u Ω S hχone
    charts symbols ha hJ hu hΩ hS hhigh hCfreq hcomparison Rbox hb
    (fullReflectedMatrixAmplitude_supportedInCenteredBox a J u Ω S Rbox hsupport) B hB
  have hbnd := (fullReflectedMatrixAmplitude_operator_bounds a J u Ω S hb
    (2 * (n + 1)) B hB hn Rbox hsupport le_rfl).2.2
  rw [← hid] at hbnd
  exact ⟨(norm_carrier_normal_le_realQuadratureNormal h.operator).trans hbnd, hbnd⟩

end JanetCartan.ContinuumRow.CarrierNormalRealization
