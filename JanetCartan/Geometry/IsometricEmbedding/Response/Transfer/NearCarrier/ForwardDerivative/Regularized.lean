module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative.Transfer
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating actual regularized graph integrals

The hypotheses below concern only the integrability and local derivative
majorants of the literal kernel. They are to be discharged for each actual
compact-frequency regularization by `jc-finite-fio-calculus`. They do not contain
a derivative-transfer identity or an output Sobolev membership assertion.
Source: `app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer
open FourierIntegral
variable {n r : ℕ}

/-- Literal integrand with the frequency-source product measure in
`app:ch_response:thm:response-literal-transfer`. -/
def forwardKernelIntegrand (Φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (u : Euclidean n → Fin r → ℂ) (x : Euclidean n) (p : Euclidean n × Euclidean n) : Fin r → ℂ :=
  graphOscillation Φ x p.2 p.1 • (A x p.2 p.1).mulVec (u p.2)

/-- Primitive analytic input for an actual frequency regularization in
`app:ch_response:thm:response-literal-transfer`. Derivatives here are derivatives
of the integrand, not of the output operator. -/
structure ForwardKernelDomination (Φ : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (u : Euclidean n → Fin r → ℂ) : Prop where
  integrable : ∀ x, Integrable (forwardKernelIntegrand Φ A u x)
    (volume.prod volume)
  derivative_integrable : ∀ x, Integrable
    (fun p ↦ fderiv ℝ (fun z ↦ forwardKernelIntegrand Φ A u z p) x) (volume.prod volume)
  locally_dominated : ∀ x, ∃ s ∈ 𝓝 x, ∃ bound : Euclidean n × Euclidean n → ℝ,
    Integrable bound (volume.prod volume) ∧
    ∀ᵐ p ∂(volume.prod volume), ∀ z ∈ s,
      ‖fderiv ℝ (fun w ↦ forwardKernelIntegrand Φ A u w p) z‖ ≤ bound p

private theorem differentiableAt_forwardKernelIntegrand
    (Φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (u : Euclidean n → Fin r → ℂ) (x : Euclidean n) (p : Euclidean n × Euclidean n)
    (hΦ : DifferentiableAt ℝ (fun z ↦ Φ z p.1) x)
    (hA : DifferentiableAt ℝ (fun z ↦ A z p.2 p.1) x) :
    DifferentiableAt ℝ (fun z ↦ forwardKernelIntegrand Φ A u z p) x := by
  have he : DifferentiableAt ℝ (fun z ↦ graphOscillation Φ z p.2 p.1) x :=
    ((Complex.ofRealCLM.differentiableAt.comp x
      (hΦ.sub (differentiableAt_const (inner ℝ p.2 p.1)))).const_mul _).cexp
  apply he.smul
  apply differentiableAt_pi.mpr
  intro i
  change DifferentiableAt ℝ (fun z ↦ ∑ k, A z p.2 p.1 i k * u p.2 k) x
  exact DifferentiableAt.fun_sum (fun k _ ↦
    (differentiableAt_pi.mp (differentiableAt_pi.mp hA i) k).mul_const _)

/-- Differentiation under the actual graph integral, justified by primitive
local domination. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem hasFDerivAt_graphOperator_of_domination
    (Φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (u : Euclidean n → Fin r → ℂ)
    (hΦ : ∀ δ, Differentiable ℝ (fun z ↦ Φ z δ))
    (hA : ∀ y δ, Differentiable ℝ (fun z ↦ A z y δ))
    (hdom : ForwardKernelDomination Φ A u) (x : Euclidean n) :
    HasFDerivAt (graphOperator Φ A u)
      (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ p,
        fderiv ℝ (fun z ↦ forwardKernelIntegrand Φ A u z p) x ∂(volume.prod volume)) x := by
  obtain ⟨s, hs, bound, hb, hbound⟩ := hdom.locally_dominated x
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    (Filter.Eventually.of_forall (fun z ↦ (hdom.integrable z).aestronglyMeasurable))
    (hdom.integrable x) (hdom.derivative_integrable x).aestronglyMeasurable hbound hb
    (Filter.Eventually.of_forall (fun p z _ ↦
      (differentiableAt_forwardKernelIntegrand Φ A u z p (hΦ p.1 z) (hA p.2 p.1 z)).hasFDerivAt))
  have heq : graphOperator Φ A u = fun z ↦
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ p, forwardKernelIntegrand Φ A u z p ∂(volume.prod volume) := by
    funext z
    rw [integral_prod _ (hdom.integrable z)]
    rfl
  rw [heq]
  exact h.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)

/-- The actual output coordinate derivative is the graph with the differentiated
full amplitude. No output Sobolev domain is assumed.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem partialDeriv_graphOperator_forwardOutputAmplitude
    (Φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (u : Euclidean n → Fin r → ℂ)
    (hΦ : ∀ δ, Differentiable ℝ (fun z ↦ Φ z δ))
    (hA : ∀ y δ, Differentiable ℝ (fun z ↦ A z y δ))
    (hdom : ForwardKernelDomination Φ A u) (x : Euclidean n) (j : Fin n) :
    partialDeriv (graphOperator Φ A u) x j = graphOperator Φ (forwardOutputAmplitude Φ A j) u x := by
  unfold partialDeriv
  rw [(hasFDerivAt_graphOperator_of_domination Φ A u hΦ hA hdom x).fderiv, smul_apply,
    ContinuousLinearMap.integral_apply (hdom.derivative_integrable x)]
  have hid : Integrable (fun p ↦ graphOscillation Φ x p.2 p.1 •
      (forwardOutputAmplitude Φ A j x p.2 p.1).mulVec (u p.2)) (volume.prod volume) := by
    have h := (hdom.derivative_integrable x).apply_continuousLinearMap (EuclideanSpace.single j 1)
    change Integrable (fun p ↦ partialDeriv (fun z ↦ forwardKernelIntegrand Φ A u z p) x j)
      (volume.prod volume) at h
    simpa only [forwardKernelIntegrand,
      partialDeriv_graphOscillation_mulVec_output Φ A u x _ _ j (hΦ _ x) (hA _ _ x)] using h
  change _ • (∫ p, partialDeriv (fun z ↦ forwardKernelIntegrand Φ A u z p) x j
    ∂(volume.prod volume)) = _
  simp_rw [forwardKernelIntegrand,
    partialDeriv_graphOscillation_mulVec_output Φ A u x _ _ j (hΦ _ x) (hA _ _ x)]
  rw [integral_prod _ hid]
  rfl

end JanetCartan.ResponseTransfer
