module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Output
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Weighted
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation under the reverse graph integral

Primitive domination for compact-frequency regularizations of the reverse graph
in `app:ch_response:eq:direct-envelope-profile`. All integrals use Euclidean
Lebesgue measure and physical covectors, with the original `(2π)⁻ⁿ` normalization.
The analytic inputs must be supplied by `jc-finite-fio-calculus`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.ReverseDerivative
variable {n r : ℕ}

/-- The reverse demodulated graph of `app:ch_response:eq:direct-envelope-profile`,
with the complete two-position amplitude and physical frequency displacement. -/
def envelopeGraph (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (A : FourierIntegral.FullAmplitude n r) (f : Euclidean n → Fin r → ℂ)
    (y : Euclidean n) : Fin r → ℂ :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ δ, ∫ x,
    oscillation S ζ ρ y x δ • (A y x δ).mulVec (f x)

/-- The envelope notation is exactly the full reverse graph with phase increment
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem envelopeGraph_eq_reverseGraph
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (A : FourierIntegral.FullAmplitude n r) (f : Euclidean n → Fin r → ℂ) :
    envelopeGraph S ζ ρ A f = reverseGraph (phaseIncrement S ζ ρ) A f := by
  have he (y x δ : Euclidean n) :
      star (FourierIntegral.graphOscillation (phaseIncrement S ζ ρ) x y δ) =
        oscillation S ζ ρ y x δ := by
    simp only [FourierIntegral.graphOscillation, oscillation, Complex.star_def,
      ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  funext y
  simp only [envelopeGraph, reverseGraph, he]

/-- The literal reverse integrand on frequency × source space, as used in
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
def kernelIntegrand (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (A : FourierIntegral.FullAmplitude n r) (f : Euclidean n → Fin r → ℂ)
    (y : Euclidean n) (p : Euclidean n × Euclidean n) : Fin r → ℂ :=
  oscillation S ζ ρ y p.2 p.1 • (A y p.2 p.1).mulVec (f p.2)

/-- Primitive integrability and local domination of derivatives of the literal
integrand in `app:ch_response:eq:direct-envelope-profile`. No field asserts a
derivative of the graph integral or output Sobolev membership. -/
structure KernelDomination (S : Euclidean n → Euclidean n → ℝ)
    (ζ : Euclidean n) (ρ : ℝ) (A : FourierIntegral.FullAmplitude n r)
    (f : Euclidean n → Fin r → ℂ) : Prop where
  integrable : ∀ y, Integrable (kernelIntegrand S ζ ρ A f y) (volume.prod volume)
  derivative_integrable : ∀ y, Integrable
    (fun p ↦ fderiv ℝ (fun z ↦ kernelIntegrand S ζ ρ A f z p) y) (volume.prod volume)
  locally_dominated : ∀ y, ∃ s ∈ 𝓝 y, ∃ bound : Euclidean n × Euclidean n → ℝ,
    Integrable bound (volume.prod volume) ∧
    ∀ᵐ p ∂(volume.prod volume), ∀ z ∈ s,
      ‖fderiv ℝ (fun w ↦ kernelIntegrand S ζ ρ A f w p) z‖ ≤ bound p

private theorem differentiableAt_kernelIntegrand
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (A : FourierIntegral.FullAmplitude n r) (f : Euclidean n → Fin r → ℂ)
    (y : Euclidean n) (p : Euclidean n × Euclidean n)
    (hA : DifferentiableAt ℝ (fun z ↦ A z p.2 p.1) y) :
    DifferentiableAt ℝ (fun z ↦ kernelIntegrand S ζ ρ A f z p) y := by
  have hi : HasFDerivAt (fun z : Euclidean n ↦ inner ℝ z p.1) (innerSL ℝ p.1) y := by
    convert (innerSL ℝ p.1).hasFDerivAt (x := y) using 1
    ext z
    exact (real_inner_comm z p.1).symm
  have he : DifferentiableAt ℝ (fun z ↦ oscillation S ζ ρ z p.2 p.1) y :=
    (((Complex.ofRealCLM.hasFDerivAt.comp y
      (hi.sub_const (phaseIncrement S ζ ρ p.2 p.1))).const_mul Complex.I).cexp).differentiableAt
  exact he.smul ((matrixAction (r := r)).hasFDerivAt_of_bilinear hA.hasFDerivAt
    (hasFDerivAt_const (f p.2) y)).differentiableAt

/-- Differentiate the normalized reverse graph from primitive domination,
without assuming a graph derivative identity
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem hasFDerivAt_envelopeGraph_of_domination
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (A : FourierIntegral.FullAmplitude n r) (f : Euclidean n → Fin r → ℂ)
    (hA : ∀ x δ, Differentiable ℝ (fun z ↦ A z x δ))
    (hdom : KernelDomination S ζ ρ A f) (y : Euclidean n) :
    HasFDerivAt (envelopeGraph S ζ ρ A f)
      (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ p,
        fderiv ℝ (fun z ↦ kernelIntegrand S ζ ρ A f z p) y ∂(volume.prod volume)) y := by
  obtain ⟨s, hs, bound, hb, hbound⟩ := hdom.locally_dominated y
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    (Filter.Eventually.of_forall (fun z ↦ (hdom.integrable z).aestronglyMeasurable))
    (hdom.integrable y) (hdom.derivative_integrable y).aestronglyMeasurable hbound hb
    (Filter.Eventually.of_forall (fun p z _ ↦
      (differentiableAt_kernelIntegrand S ζ ρ A f z p (hA p.2 p.1 z)).hasFDerivAt))
  have heq : envelopeGraph S ζ ρ A f = fun z ↦
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ p, kernelIntegrand S ζ ρ A f z p ∂(volume.prod volume) := by
    funext z
    rw [integral_prod _ (hdom.integrable z)]
    rfl
  rw [heq]
  exact h.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)

/-- The coordinate derivative is the integral of the differentiated literal
kernel (`app:ch_response:eq:direct-envelope-profile`). The next source integration
by parts produces the inverse-matrix amplitudes. -/
theorem partialDeriv_envelopeGraph_of_domination
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (A : FourierIntegral.FullAmplitude n r) (f : Euclidean n → Fin r → ℂ)
    (hA : ∀ x δ, Differentiable ℝ (fun z ↦ A z x δ))
    (hdom : KernelDomination S ζ ρ A f) (y : Euclidean n) (j : Fin n) :
    partialDeriv (envelopeGraph S ζ ρ A f) y j =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ δ, ∫ x,
        partialDeriv (fun z ↦ oscillation S ζ ρ z x δ • (A z x δ).mulVec (f x)) y j := by
  unfold partialDeriv
  rw [(hasFDerivAt_envelopeGraph_of_domination S ζ ρ A f hA hdom y).fderiv,
    smul_apply, ContinuousLinearMap.integral_apply (hdom.derivative_integrable y)]
  rw [integral_prod _ ((hdom.derivative_integrable y).apply_continuousLinearMap
    (EuclideanSpace.single j 1))]
  rfl

end JanetCartan.ResponseTransfer.ReverseDerivative
